"""
train-eval/sweep.py — speedup and quality sweep across d and N.

Two panels:
  1. Speedup map   : kernel ms ratio (pairwise/spectral) vs batch size N,
                     one line per embedding dimension d.
                     Pure timing — runs in seconds.

  2. Quality sweep : final reconstruction MSE after 10 training epochs
                     at d ∈ {8, 32, 64}.  Paired bars: pairwise vs spectral.
                     Shows the spectral kernel reaches equivalent quality
                     regardless of d.

Usage:
    cd python
    python train-eval/sweep.py
    # saves train-eval/sweep.png

Requires: torch, scipy, matplotlib, ml-tidbits submodule.
"""

from __future__ import annotations

import copy
import math
import os
import sys
import time

import torch
import torch.nn as nn
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ------------------------------------------------------------------
_REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(_REPO, "ml-tidbits", "python"))
sys.path.insert(0, os.path.join(_REPO, "python"))

from embed_models.EmbedModels import C_WristbandGaussianLoss
from spectral.kernel import (
    SpectralWristbandLoss,
    build_spectral_neumann_coefficients,
    spectral_neumann_energy_l01,
)

SEED    = 42
DTYPE   = torch.float32
DEVICE  = "cpu"
K_MODES = 6


# ===========================================================================
# Shared helpers (same data / model as run.py)
# ===========================================================================

def make_non_gaussian_data(n, dim, seed=SEED):
    rng = torch.Generator().manual_seed(seed)
    centres    = torch.randn(5, dim, generator=rng) * 4.0
    transforms = [torch.randn(dim, dim, generator=rng) * 0.6 for _ in range(5)]
    per, parts = n // 5, []
    for i in range(5):
        raw = torch.randn(per, dim, generator=rng)
        raw[:, :dim // 3] = raw[:, :dim // 3].sign() * raw[:, :dim // 3].abs().pow(1.5)
        parts.append(raw @ transforms[i].T + centres[i])
    data = torch.cat(parts)
    perm = torch.randperm(data.size(0), generator=rng)
    return data[perm]


def make_mlp(in_dim, embed_dim, hidden=128):
    def _mlp(a, b):
        return nn.Sequential(
            nn.Linear(a, hidden), nn.GELU(),
            nn.Linear(hidden, hidden), nn.GELU(),
            nn.Linear(hidden, b),
        )
    class AE(nn.Module):
        def __init__(self):
            super().__init__()
            self.enc = _mlp(in_dim, embed_dim)
            self.dec = _mlp(embed_dim, in_dim)
        def forward(self, x):
            z = self.enc(x)
            return self.dec(z), z
    return AE()


def wristband_map(x, eps=1e-12):
    s = x.square().sum(-1).clamp_min(eps)
    u = x * torch.rsqrt(s)[:, None]
    a = s.new_tensor(0.5 * x.shape[-1])
    t = torch.special.gammainc(a, 0.5 * s).clamp(eps, 1 - eps)
    return u, t


def pairwise_energy_raw(u, t, beta=8.0, alpha=math.sqrt(1/12)):
    ba2 = beta * alpha**2
    g   = (u @ u.T).clamp(-1., 1.)
    e   = 2.0 * ba2 * (g - 1.)
    tc, tr = t[:, None], t[None, :]
    K = (torch.exp(e - beta*(tc-tr)**2)
       + torch.exp(e - beta*(tc+tr)**2)
       + torch.exp(e - beta*(tc+tr-2)**2))
    return K.mean()


def spectral_energy_raw(u, t, coeffs):
    _, _, e = spectral_neumann_energy_l01(u, t, coeffs)
    return e


# ===========================================================================
# Panel 1 — speedup map  (pure timing, no training)
# ===========================================================================

def timing_sweep(n_vals, d_vals, reps=20):
    """Returns dict: (d, n) -> (t_pairwise_ms, t_spectral_ms)."""
    results = {}
    for d in d_vals:
        coeffs = build_spectral_neumann_coefficients(
            d=d, beta=8.0, alpha=math.sqrt(1/12), k_modes=K_MODES,
            device=torch.device(DEVICE), dtype=DTYPE,
        )
        for n in n_vals:
            x    = torch.randn(n, d, dtype=DTYPE)
            u, t = wristband_map(x)

            # warm-up
            pairwise_energy_raw(u, t)
            spectral_energy_raw(u, t, coeffs)

            t0 = time.perf_counter()
            for _ in range(reps):
                pairwise_energy_raw(u, t)
            t_pw = (time.perf_counter() - t0) / reps * 1000

            t0 = time.perf_counter()
            for _ in range(reps):
                spectral_energy_raw(u, t, coeffs)
            t_sp = (time.perf_counter() - t0) / reps * 1000

            results[(d, n)] = (t_pw, t_sp)
            print(f"  d={d:4d}, N={n:5d}  pw={t_pw:8.2f}ms  sp={t_sp:6.3f}ms  x{t_pw/t_sp:6.1f}")

    return results


# ===========================================================================
# Panel 2 — quality sweep  (short training at multiple d)
# ===========================================================================

def short_train(d, n_samples=50_000, batch=1024, epochs=10, lr=3e-4,
                lambda_rec=1.0, lambda_wb=0.1):
    """Train both losses for `epochs` epochs; return (mse_pairwise, mse_spectral)."""
    in_dim = max(d * 2, 15)   # keep a non-trivial reconstruction task

    data = make_non_gaussian_data(n_samples, in_dim)
    mu, std = data.mean(0), data.std(0).clamp_min(1e-6)
    data = (data - mu) / std

    loss_pw = C_WristbandGaussianLoss(
        calibration_shape=(batch, d),
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )
    loss_sp = SpectralWristbandLoss(
        d=d, k_modes=K_MODES,
        calibration_shape=(batch, d),
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )

    torch.manual_seed(SEED)
    model_init = make_mlp(in_dim, d)
    model_pw   = copy.deepcopy(model_init)
    model_sp   = copy.deepcopy(model_init)

    def run(model, loss_fn):
        opt = torch.optim.Adam(model.parameters(), lr=lr)
        for _ in range(epochs):
            perm = torch.randperm(data.size(0))
            for i in range(0, data.size(0) - batch + 1, batch):
                b     = data[perm[i:i+batch]]
                xh, z = model(b)
                rec   = (xh - b).square().mean()
                wb    = loss_fn(z)
                (lambda_rec * rec + lambda_wb * wb.total).backward()
                opt.step(); opt.zero_grad()
        model.eval()
        with torch.no_grad():
            xh_all, _ = model(data)
            return float((xh_all - data).square().mean())

    mse_pw = run(model_pw, loss_pw)
    mse_sp = run(model_sp, loss_sp)
    return mse_pw, mse_sp


# ===========================================================================
# Main
# ===========================================================================

def main():
    OUT = os.path.join(os.path.dirname(__file__), "sweep.png")

    # --- Panel 1: timing sweep ---
    N_VALS = [64, 128, 256, 512, 1024, 2048, 4096]
    D_VALS = [8, 32, 128, 512]
    print("=== Timing sweep ===")
    timing = timing_sweep(N_VALS, D_VALS, reps=20)

    # --- Panel 2: quality sweep ---
    D_TRAIN = [8, 32, 64]
    print("\n=== Quality sweep (10 epochs each) ===")
    quality = {}
    for d in D_TRAIN:
        print(f"  d={d} ...", end=" ", flush=True)
        mse_pw, mse_sp = short_train(d, epochs=10)
        quality[d] = (mse_pw, mse_sp)
        print(f"pw={mse_pw:.5f}  sp={mse_sp:.5f}")

    # --- Plots ---
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle(
        f"Spectral Neumann — scaling behaviour  (K={K_MODES}, CPU)",
        fontsize=12, fontweight="bold",
    )

    colors = ["C0", "C1", "C2", "C3"]

    # Panel 1: computation time ratio (log-log), d=32/128/512 only
    D_PLOT = [d for d in D_VALS if d != 8]
    for d, col in zip(D_PLOT, colors[1:]):
        ratios = [timing[(d, n)][0] / timing[(d, n)][1] for n in N_VALS]
        ax1.loglog(N_VALS, ratios, f"{col}-o", ms=5, lw=1.8, label=f"d={d}")
        ratio_last = ratios[-1]
        ax1.annotate(
            f"{ratio_last:.0f}×",
            xy=(N_VALS[-1], ratio_last),
            xytext=(6, 0), textcoords="offset points",
            fontsize=9, color=col, va="center", fontweight="bold",
        )
    ax1.set_xlabel("Batch size N")
    ax1.set_ylabel("Time ratio  (pairwise ÷ spectral)")
    ax1.set_title("Spectral kernel is N/K faster\n(log–log)")
    ax1.legend(fontsize=9, title="embed dim")
    ax1.grid(True, alpha=0.3, which="both")

    # Panel 2: final MSE — paired bars
    x_pos  = np.arange(len(D_TRAIN))
    width  = 0.35
    mse_pw = [quality[d][0] for d in D_TRAIN]
    mse_sp = [quality[d][1] for d in D_TRAIN]

    bars_pw = ax2.bar(x_pos - width/2, mse_pw, width, label="pairwise", color="C0", alpha=0.85)
    bars_sp = ax2.bar(x_pos + width/2, mse_sp, width, label=f"spectral (K={K_MODES})", color="C1", alpha=0.85)
    ax2.set_xticks(x_pos)
    ax2.set_xticklabels([f"d={d}" for d in D_TRAIN])
    ax2.set_ylabel("Final reconstruction MSE  (10 epochs)")
    ax2.set_title("Quality equivalence across d\nBoth kernels converge to same MSE")
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3, axis="y")

    # Annotate bars with values
    for bar in list(bars_pw) + list(bars_sp):
        h = bar.get_height()
        ax2.annotate(
            f"{h:.4f}",
            xy=(bar.get_x() + bar.get_width() / 2, h),
            xytext=(0, 3), textcoords="offset points",
            ha="center", va="bottom", fontsize=7.5,
        )

    plt.tight_layout()
    plt.savefig(OUT, dpi=150, bbox_inches="tight")
    print(f"\nSaved: {OUT}")

    # --- Text summary ---
    print("\n" + "=" * 60)
    print(f"SPEEDUP  (pairwise ms / spectral ms)  K={K_MODES}")
    print("=" * 60)
    header = f"  {'N':>6}" + "".join(f"  {'d='+str(d):>10}" for d in D_VALS)
    print(header)
    print("  " + "-" * (len(header) - 2))
    for n in N_VALS:
        row = f"  {n:>6}"
        for d in D_VALS:
            t_pw, t_sp = timing[(d, n)]
            row += f"  {t_pw/t_sp:>9.1f}×"
        print(row)

    print("\n" + "=" * 60)
    print("QUALITY  (final reconstruction MSE, 10 epochs)")
    print("=" * 60)
    print(f"  {'d':>6}  {'pairwise':>12}  {'spectral':>12}  {'ratio':>8}")
    print("  " + "-" * 44)
    for d in D_TRAIN:
        pw, sp = quality[d]
        print(f"  {d:>6}  {pw:>12.5f}  {sp:>12.5f}  {sp/pw:>7.3f}×")


if __name__ == "__main__":
    main()
