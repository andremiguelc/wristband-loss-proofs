"""
fw-eval/run.py — forward-pass evaluation of the spectral Neumann kernel.

Two questions:
  1. Discrimination  (Panel 1): does the spectral kernel detect non-Gaussianity
     as well as the pairwise wristband baseline?
  2. Throughput      (Panel 2): is it faster, and does O(N) vs O(N²) hold?

Naming:
  "wristband rep (pairwise)" — O(N²d) pairwise kernel sum (3-image Neumann).
  "spectral Neumann"         — O(NdK) spectral decomposition, l<=1, K modes.

Usage:
    cd python
    python fw-eval/run.py
    # saves fw-eval/fw_eval.png and prints a text summary.

Requires:
    torch, scipy, matplotlib
    ml-tidbits submodule at ../../ml-tidbits (for the pairwise baseline)
"""

from __future__ import annotations

import math
import os
import sys
import time

import torch
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ------------------------------------------------------------------
# Path setup
# ------------------------------------------------------------------
_REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(_REPO, "ml-tidbits", "python"))
sys.path.insert(0, os.path.join(_REPO, "python"))

from spectral.kernel import (
    build_spectral_neumann_coefficients,
    spectral_neumann_energy_l01,
    SpectralNeumannCoefficients,
)

BETA  = 8.0
ALPHA = math.sqrt(1.0 / 12.0)
DTYPE = torch.float32
SEED  = 42


# ===========================================================================
# Wristband map (shared by both kernels)
# ===========================================================================

def wristband_map(x: torch.Tensor, eps: float = 1e-12):
    s = x.square().sum(-1).clamp_min(eps)
    u = x * torch.rsqrt(s)[:, None]
    a = s.new_tensor(0.5 * x.shape[-1])
    t = torch.special.gammainc(a, 0.5 * s).clamp(eps, 1 - eps)
    return u, t


# ===========================================================================
# Energy functions
# ===========================================================================

def pairwise_energy(u, t, beta, alpha):
    """(1/N²) Σ_{i,j} K_wristband(w_i, w_j)  — O(N²d) baseline."""
    ba2 = beta * alpha ** 2
    g   = (u @ u.T).clamp(-1., 1.)
    e   = 2.0 * ba2 * (g - 1.)
    tc, tr = t[:, None], t[None, :]
    K = (torch.exp(e - beta * (tc - tr) ** 2)
       + torch.exp(e - beta * (tc + tr) ** 2)
       + torch.exp(e - beta * (tc + tr - 2) ** 2))
    return float(K.mean())


def spectral_energy(u, t, coeffs):
    """λ₀·E₀ + λ₁·E₁  — O(NdK) spectral forward pass."""
    _, _, e = spectral_neumann_energy_l01(u, t, coeffs)
    return float(e)


# ===========================================================================
# Data generators
# ===========================================================================

def make_gaussian(n, d, seed):
    g = torch.Generator().manual_seed(seed)
    return torch.randn(n, d, generator=g, dtype=DTYPE)


def make_mixture(n, d, seed, sep, n_clusters=5):
    """Gaussian mixture with cluster centres at distance *sep* from the origin."""
    g    = torch.Generator().manual_seed(seed)
    dirs = torch.randn(n_clusters, d, generator=g, dtype=DTYPE)
    dirs = dirs / dirs.norm(dim=-1, keepdim=True)
    per  = n // n_clusters
    parts = []
    for i in range(n_clusters):
        raw = torch.randn(per, d, generator=g, dtype=DTYPE)
        parts.append(raw + dirs[i] * sep)
    data = torch.cat(parts)
    perm = torch.randperm(data.size(0), generator=g)
    return data[perm]


# ===========================================================================
# Panel 1 — Discrimination
# ===========================================================================

def panel_discrimination(ax, d, n, coeffs_ref):
    """Energy ratio E(P) / E(Gaussian) vs cluster separation."""
    x_gauss   = make_gaussian(n, d, SEED)
    u_g, t_g  = wristband_map(x_gauss)
    e_pw_base = pairwise_energy(u_g, t_g, BETA, ALPHA)
    e_sp_base = spectral_energy(u_g, t_g, coeffs_ref)

    seps    = np.linspace(0.0, 4.0, 20)
    e_pw    = [1.0]
    e_sp    = [1.0]
    for sep in seps[1:]:
        x_m      = make_mixture(n, d, SEED, float(sep))
        u_m, t_m = wristband_map(x_m)
        e_pw.append(pairwise_energy(u_m, t_m, BETA, ALPHA) / e_pw_base)
        e_sp.append(spectral_energy(u_m, t_m, coeffs_ref)  / e_sp_base)

    ax.plot(seps, e_pw, "C0-o", ms=4, label="wristband rep (pairwise)")
    ax.plot(seps, e_sp, "C1-s", ms=4, label=f"spectral Neumann  ℓ≤1, K={coeffs_ref.a_k.shape[0]}")
    ax.axhline(1.0, color="gray", ls="--", lw=0.8, label="Gaussian baseline")
    ax.set_xlabel("Cluster separation (distance of centres from origin)")
    ax.set_ylabel("E(P) / E(Gaussian) — raw energy ratio")
    ax.set_title(
        f"Discrimination  (d={d}, N={n})\n"
        "Both kernels rise as data moves from Gaussian to clustered"
    )
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(bottom=0)
    return seps, e_pw, e_sp


# ===========================================================================
# Panel 2 — Throughput
# ===========================================================================

def panel_throughput(ax, d, coeffs_tp, reps=15):
    """Wall-clock time per forward pass vs batch size N."""
    n_vals = [64, 128, 256, 512, 1024, 2048, 4096]
    t_pw, t_sp = [], []

    for n in n_vals:
        x_tp     = make_gaussian(n, d, SEED)
        u_tp, t_tp = wristband_map(x_tp)

        # warm-up
        pairwise_energy(u_tp, t_tp, BETA, ALPHA)
        spectral_energy(u_tp, t_tp, coeffs_tp)

        t0 = time.perf_counter()
        for _ in range(reps):
            pairwise_energy(u_tp, t_tp, BETA, ALPHA)
        t_pw.append((time.perf_counter() - t0) / reps * 1000)

        t0 = time.perf_counter()
        for _ in range(reps):
            spectral_energy(u_tp, t_tp, coeffs_tp)
        t_sp.append((time.perf_counter() - t0) / reps * 1000)

    n_arr = np.array(n_vals, dtype=float)
    ax.loglog(n_vals, t_pw, "C0-o", ms=5, label="wristband rep  O(N²d)")
    ax.loglog(n_vals, t_sp, "C1-s", ms=5, label=f"spectral  O(NdK), K={coeffs_tp.a_k.shape[0]}")
    ax.loglog(n_arr, t_pw[0] * (n_arr / n_vals[0]) ** 2, "C0--", lw=0.8, alpha=0.5, label="N² ref")
    ax.loglog(n_arr, t_sp[0] * (n_arr / n_vals[0]),      "C1--", lw=0.8, alpha=0.5, label="N ref")
    ax.set_xlabel("Batch size N")
    ax.set_ylabel("Time per forward pass (ms)")
    ax.set_title(f"Throughput  (d={d}, CPU, K={coeffs_tp.a_k.shape[0]})")
    r_last = t_pw[-1] / t_sp[-1]
    ax.annotate(
        f"{r_last:.0f}× faster @ N={n_vals[-1]}",
        xy=(n_vals[-1], t_sp[-1]),
        xytext=(n_vals[-3], t_sp[-1] * 5),
        fontsize=9, color="C1",
        arrowprops=dict(arrowstyle="->", color="C1"),
    )
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, which="both")
    return n_vals, t_pw, t_sp


# ===========================================================================
# Main
# ===========================================================================

def main():
    torch.manual_seed(SEED)
    D, N = 8, 512
    K    = 20   # high K for discrimination panel (shows full spectral quality)
    K_TP = 6    # production K for throughput panel

    OUT = os.path.join(os.path.dirname(__file__), "fw_eval.png")

    coeffs_ref = build_spectral_neumann_coefficients(
        d=D, beta=BETA, alpha=ALPHA, k_modes=K,
        device=torch.device("cpu"), dtype=DTYPE,
    )
    coeffs_tp = build_spectral_neumann_coefficients(
        d=D, beta=BETA, alpha=ALPHA, k_modes=K_TP,
        device=torch.device("cpu"), dtype=DTYPE,
    )

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5))
    fig.suptitle(
        f"Spectral Neumann kernel — forward-pass eval  "
        f"(β={BETA}, α={ALPHA:.4f}, d={D}, N={N})",
        fontsize=12, fontweight="bold",
    )

    seps, e_pw, e_sp     = panel_discrimination(ax1, D, N, coeffs_ref)
    n_vals, t_pw, t_sp   = panel_throughput(ax2, D, coeffs_tp)

    plt.tight_layout()
    plt.savefig(OUT, dpi=150, bbox_inches="tight")
    print(f"Saved: {OUT}")

    # ------------------------------------------------------------------
    # Text summary
    # ------------------------------------------------------------------
    print("\n" + "=" * 60)
    print("DISCRIMINATION  (raw energy ratio E(P) / E(Gaussian))")
    print("=" * 60)
    print(f"  {'sep':>5}  {'pairwise':>10}  {'spectral':>10}")
    print("  " + "-" * 30)
    for sep, rp, rs in zip(seps[::3], e_pw[::3], e_sp[::3]):
        print(f"  {sep:>5.1f}  {rp:>10.4f}  {rs:>10.4f}")

    print("\n" + "=" * 60)
    print("THROUGHPUT  (ms per forward pass, CPU)")
    print("=" * 60)
    print(f"  {'N':>6}  {'pairwise ms':>12}  {'spectral ms':>12}  {'speedup':>9}")
    print("  " + "-" * 47)
    for n, tp, ts in zip(n_vals, t_pw, t_sp):
        print(f"  {n:>6}  {tp:>12.3f}  {ts:>12.3f}  {tp/ts:>8.1f}×")


if __name__ == "__main__":
    main()
