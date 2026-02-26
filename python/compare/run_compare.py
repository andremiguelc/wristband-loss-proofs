"""
run_compare.py — side-by-side comparison of the 3-image and spectral Neumann kernels.

Usage:
    cd python
    python compare/run_compare.py

Requires:
    - pytorch, scipy
    - ml-tidbits submodule at ../../ml-tidbits  (gitignored, must be present on disk)

What it tests:
    On Gaussian data (the null):  both `rep` losses should be near their calibrated
    zero means — confirming the spectral identity E_spectral ≈ E_3image.

    On non-Gaussian data:  both losses should be clearly positive (= "not Gaussian"),
    but they may differ in magnitude since they measure different facets of the
    same kernel decomposition.

    The kernel identity in the Lean proof says spectralEnergy = kernelEnergy
    holds for every measure; this script probes that numerically.
"""

from __future__ import annotations

import os
import sys
import math

import torch

# ------------------------------------------------------------------
# Path setup: make ml-tidbits importable without modifying it.
# The submodule lives at ../../ml-tidbits relative to this file.
# ------------------------------------------------------------------
_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
_ML_TIDBITS_PY = os.path.join(_REPO_ROOT, "ml-tidbits", "python")
if _ML_TIDBITS_PY not in sys.path:
    sys.path.insert(0, _ML_TIDBITS_PY)

_THIS_PY = os.path.join(_REPO_ROOT, "python")
if _THIS_PY not in sys.path:
    sys.path.insert(0, _THIS_PY)

from embed_models.EmbedModels import C_WristbandGaussianLoss   # ml-tidbits (read-only)
from spectral.wristband import SpectralWristbandLoss            # our spectral kernel


# ------------------------------------------------------------------
# Shared hyperparameters
# ------------------------------------------------------------------

N        = 512    # batch size
D        = 8      # embedding dimension (must be >= 3 for spectral)
BETA     = 8.0
ALPHA    = math.sqrt(1.0 / 12.0)   # chordal heuristic (same as ml-tidbits default)
K_MODES  = 12     # Neumann radial modes for spectral

CAL_REPS = 256    # fewer reps for speed; 1024 for production

DEVICE   = "cpu"
DTYPE    = torch.float32
SEED     = 42


# ------------------------------------------------------------------
# Data generators
# ------------------------------------------------------------------

def make_gaussian(n: int, d: int, seed: int) -> torch.Tensor:
    """True N(0, I) samples — null distribution."""
    g = torch.Generator().manual_seed(seed)
    return torch.randn(n, d, generator=g)


def make_non_gaussian(n: int, d: int, seed: int, n_clusters: int = 4) -> torch.Tensor:
    """Mixture-of-Gaussians with shifted centres and correlated clusters."""
    g = torch.Generator().manual_seed(seed)
    centres = torch.randn(n_clusters, d, generator=g) * 3.5
    per = n // n_clusters
    parts = []
    for i in range(n_clusters):
        A = torch.randn(d, d, generator=g) * 0.5
        raw = torch.randn(per, d, generator=g)
        raw[:, :d // 2] = raw[:, :d // 2].sign() * raw[:, :d // 2].abs().pow(1.5)
        parts.append(raw @ A.T + centres[i])
    data = torch.cat(parts)
    perm = torch.randperm(data.size(0), generator=g)
    return data[perm]


# ------------------------------------------------------------------
# Build loss objects
# ------------------------------------------------------------------

def build_losses():
    print(f"Building C_WristbandGaussianLoss  (N={N}, d={D}, cal_reps={CAL_REPS}) ...", end=" ", flush=True)
    wb_3image = C_WristbandGaussianLoss(
        beta=BETA,
        alpha=ALPHA,
        angular="chordal",
        reduction="per_point",
        lambda_rad=0.1,
        lambda_ang=0.0,
        moment="w2",
        lambda_mom=1.0,
        calibration_shape=(N, D),
        calibration_reps=CAL_REPS,
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )
    print("done.")

    print(f"Building SpectralWristbandLoss     (N={N}, d={D}, K={K_MODES}, cal_reps={CAL_REPS}) ...", end=" ", flush=True)
    wb_spectral = SpectralWristbandLoss(
        d=D,
        beta=BETA,
        alpha=ALPHA,
        k_modes=K_MODES,
        lambda_rad=0.1,
        moment="w2",
        lambda_mom=1.0,
        calibration_shape=(N, D),
        calibration_reps=CAL_REPS,
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )
    print("done.\n")

    return wb_3image, wb_spectral


# ------------------------------------------------------------------
# Comparison
# ------------------------------------------------------------------

def compare(wb_3image, wb_spectral, x: torch.Tensor, label: str):
    with torch.no_grad():
        lc3  = wb_3image(x)
        lcs  = wb_spectral(x)

    print(f"=== {label} ===")
    print(f"{'':15s}  {'3-image':>10s}  {'spectral':>10s}  {'diff':>10s}")
    print("-" * 52)
    for name in ("rep", "rad", "ang", "mom", "total"):
        v3 = float(getattr(lc3, name))
        vs = float(getattr(lcs, name))
        print(f"  {name:<13s}  {v3:>10.4f}  {vs:>10.4f}  {vs - v3:>+10.4f}")
    print()


def compare_raw_energy(wb_spectral: SpectralWristbandLoss, x: torch.Tensor, label: str):
    """Print uncalibrated spectral energies E_0, E_1 for extra insight."""
    from spectral.neumann import spectral_neumann_energy_l01, SpectralNeumannCoefficients

    wdtype = torch.float32 if x.dtype in (torch.float16, torch.bfloat16) else x.dtype
    xw = x.to(wdtype)
    u, t = wb_spectral._wristband_map(xw)

    coeffs = SpectralNeumannCoefficients(
        lam_0=wb_spectral.coeffs.lam_0,
        lam_1=wb_spectral.coeffs.lam_1,
        a_k=wb_spectral.coeffs.a_k.to(device=xw.device, dtype=wdtype),
    )
    e_0, e_1, e_total = spectral_neumann_energy_l01(u, t, coeffs)
    print(f"  [{label}] raw spectral:  "
          f"E_0={float(e_0):.6g}  E_1={float(e_1):.6g}  E_total={float(e_total):.6g}")


# ------------------------------------------------------------------
# Main
# ------------------------------------------------------------------

def main():
    torch.manual_seed(SEED)

    wb_3image, wb_spectral = build_losses()

    print(f"Hyperparameters: beta={BETA}, alpha={ALPHA:.4f}, K={K_MODES}, N={N}, d={D}\n")

    # --- Null: Gaussian samples ---
    x_gauss = make_gaussian(N, D, seed=SEED).to(DTYPE)
    compare(wb_3image, wb_spectral, x_gauss, label="Gaussian N(0,I) — both losses should be near 0")
    compare_raw_energy(wb_spectral, x_gauss, "Gaussian")

    print()

    # --- Alternative: non-Gaussian ---
    x_nong = make_non_gaussian(N, D, seed=SEED).to(DTYPE)
    compare(wb_3image, wb_spectral, x_nong, label="Non-Gaussian (mixture) — both losses should be clearly positive")
    compare_raw_energy(wb_spectral, x_nong, "Non-Gaussian")

    print()

    # --- Sweep: multiple Gaussian batches, track rep correlation ---
    print("=== rep-loss correlation over 20 Gaussian batches ===")
    print(f"  {'batch':>5s}  {'3img_rep':>10s}  {'spec_rep':>10s}")
    print("  " + "-" * 30)
    vals_3 = []
    vals_s = []
    with torch.no_grad():
        for i in range(20):
            xi = make_gaussian(N, D, seed=SEED + i * 7).to(DTYPE)
            lc3 = wb_3image(xi)
            lcs = wb_spectral(xi)
            v3, vs = float(lc3.rep), float(lcs.rep)
            vals_3.append(v3)
            vals_s.append(vs)
            print(f"  {i+1:>5d}  {v3:>10.4f}  {vs:>10.4f}")

    # Pearson r
    import statistics
    if len(vals_3) > 1:
        m3 = statistics.mean(vals_3)
        ms = statistics.mean(vals_s)
        cov = sum((a - m3) * (b - ms) for a, b in zip(vals_3, vals_s)) / (len(vals_3) - 1)
        s3 = statistics.stdev(vals_3)
        ss = statistics.stdev(vals_s)
        r = cov / (s3 * ss + 1e-12)
        print(f"\n  Pearson r(3-image rep, spectral rep) = {r:.4f}")
        print("  (r near 1 supports the spectral identity)")


if __name__ == "__main__":
    main()
