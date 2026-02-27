"""
train-eval/run.py — training comparison: pairwise wristband vs spectral Neumann.

Comparable in scope to Mikhail's DeterministicGAE.py (ml-tidbits/python/tests/):
  - same synthetic non-Gaussian data (15-D, 5-cluster mixture)
  - same latent dimension (d=8), batch size (1024), 40 epochs
  - same loss weights (lambda_rec=1.0, lambda_wb=0.1)
  - simple MLP encoder/decoder (instead of the attention module, to keep
    this eval self-contained and focused on the loss, not the architecture)

Two runs with identical architecture/seed, one per loss:
  A. C_WristbandGaussianLoss  — pairwise, O(N²d)
  B. SpectralWristbandLoss    — spectral Neumann, O(NdK)

Metrics reported:
  - Per-epoch: total loss, reconstruction MSE, wristband total, time
  - Final: reconstruction MSE, latent mean/std per dim, W2 to N(0,I)
  - Timing: kernel ms/batch vs total ms/batch

Usage:
    cd python
    python train-eval/run.py
    # saves train-eval/train_eval.png and prints a text summary.

Requires:
    torch, scipy, matplotlib
    ml-tidbits submodule at ../../ml-tidbits (for C_WristbandGaussianLoss)
"""

from __future__ import annotations

import math
import os
import sys
import time
import copy

import torch
import torch.nn as nn
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# ------------------------------------------------------------------
# Path setup
# ------------------------------------------------------------------
_REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(_REPO, "ml-tidbits", "python"))
sys.path.insert(0, os.path.join(_REPO, "python"))

from embed_models.EmbedModels import C_WristbandGaussianLoss
from spectral.kernel import SpectralWristbandLoss

# ------------------------------------------------------------------
# Hyperparameters  (matching DeterministicGAE.py where applicable)
# ------------------------------------------------------------------
IN_DIM      = 15
EMBED_DIM   = 8
N_SAMPLES   = 100_000
BATCH_SIZE  = 1024
N_EPOCHS    = 40
LR          = 3e-4
LAMBDA_REC  = 1.0
LAMBDA_WB   = 0.1
SEED        = 42
K_MODES     = 6      # radial modes for spectral kernel

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
DTYPE  = torch.float32


# ===========================================================================
# Data  (same generator as DeterministicGAE.py)
# ===========================================================================

def make_non_gaussian_data(n_samples: int, dim: int, n_clusters: int = 5, seed: int = 42):
    """Mixture of shifted/scaled Gaussians with heavy tails and correlations."""
    rng = torch.Generator().manual_seed(seed)
    centres    = torch.randn(n_clusters, dim, generator=rng) * 4.0
    transforms = [torch.randn(dim, dim, generator=rng) * 0.6 for _ in range(n_clusters)]
    per   = n_samples // n_clusters
    parts = []
    for i in range(n_clusters):
        raw = torch.randn(per, dim, generator=rng)
        raw[:, :dim // 3] = raw[:, :dim // 3].sign() * raw[:, :dim // 3].abs().pow(1.5)
        parts.append(raw @ transforms[i].T + centres[i])
    data = torch.cat(parts)
    perm = torch.randperm(data.size(0), generator=rng)
    return data[perm]


# ===========================================================================
# Model — simple MLP autoencoder, self-contained
# ===========================================================================

def _mlp(in_dim: int, out_dim: int, hidden: int = 128, layers: int = 3) -> nn.Sequential:
    dims = [in_dim] + [hidden] * (layers - 1) + [out_dim]
    mods = []
    for i in range(len(dims) - 1):
        mods.append(nn.Linear(dims[i], dims[i + 1]))
        if i < len(dims) - 2:
            mods.append(nn.GELU())
    return nn.Sequential(*mods)


class MLPAutoencoder(nn.Module):
    def __init__(self, in_dim: int, embed_dim: int, hidden: int = 128):
        super().__init__()
        self.encoder = _mlp(in_dim, embed_dim, hidden)
        self.decoder = _mlp(embed_dim, in_dim, hidden)

    def forward(self, x):
        z     = self.encoder(x)
        x_hat = self.decoder(z)
        return x_hat, z


# ===========================================================================
# W2² to N(0,I) — same formula as in kernel.py
# ===========================================================================

def w2_sq_to_gaussian(z: torch.Tensor) -> float:
    """Empirical W2² between batch z and N(0,I)."""
    b, d = z.shape
    mu   = z.mean(0)
    xc   = z - mu
    m    = (xc.T @ xc) / (b - 1)
    m    = 0.5 * (m + m.T)
    eig  = torch.linalg.eigvalsh(m).clamp_min(0.)
    bw2  = (torch.sqrt(eig + 1e-8) - 1.).square().sum()
    return float(mu.square().sum() + bw2)


# ===========================================================================
# Training loop — generic, works for any loss with .total attribute
# ===========================================================================

def train_one_run(
    model: nn.Module,
    data: torch.Tensor,
    loss_fn,
    label: str,
) -> dict:
    """Train for N_EPOCHS, return per-epoch logs and timing."""
    model = model.to(DEVICE)
    data  = data.to(DEVICE)
    opt   = torch.optim.Adam(model.parameters(), lr=LR)

    logs = {
        "label":      label,
        "epoch_loss": [],
        "epoch_rec":  [],
        "epoch_wb":   [],
        "epoch_time": [],   # seconds per epoch
        "kernel_ms":  [],   # kernel forward ms per batch (sampled)
    }

    n_batches = (N_SAMPLES // BATCH_SIZE)
    print(f"\n=== {label} ===")
    print(f"{'ep':>4}  {'loss':>8}  {'rec':>8}  {'wb':>8}  {'s/ep':>7}  {'ker ms':>8}")
    print("-" * 52)

    for epoch in range(1, N_EPOCHS + 1):
        model.train()
        perm       = torch.randperm(data.size(0), device=DEVICE)
        sum_loss   = sum_rec = sum_wb = 0.
        sum_ker_ms = 0.
        t_epoch    = time.perf_counter()

        for i in range(0, data.size(0) - BATCH_SIZE + 1, BATCH_SIZE):
            batch = data[perm[i : i + BATCH_SIZE]]

            x_hat, z = model(batch)
            rec_loss = (x_hat - batch).square().mean()

            # Time the kernel call only
            t_ker = time.perf_counter()
            wb    = loss_fn(z)
            sum_ker_ms += (time.perf_counter() - t_ker) * 1000

            loss = LAMBDA_REC * rec_loss + LAMBDA_WB * wb.total
            opt.zero_grad()
            loss.backward()
            opt.step()

            sum_loss += loss.item()
            sum_rec  += rec_loss.item()
            sum_wb   += wb.total.item()

        ep_time = time.perf_counter() - t_epoch
        n       = n_batches

        logs["epoch_loss"].append(sum_loss / n)
        logs["epoch_rec"].append(sum_rec / n)
        logs["epoch_wb"].append(sum_wb / n)
        logs["epoch_time"].append(ep_time)
        logs["kernel_ms"].append(sum_ker_ms / n)

        print(f"{epoch:4d}  {sum_loss/n:8.4f}  {sum_rec/n:8.4f}  "
              f"{sum_wb/n:8.4f}  {ep_time:7.1f}s  {sum_ker_ms/n:8.3f}ms")

    # Final diagnostics
    model.eval()
    with torch.no_grad():
        x_hat_all, z_all = model(data)
        mse   = float((x_hat_all - data).square().mean())
        w2    = w2_sq_to_gaussian(z_all)
        zmean = z_all.mean(0).cpu().tolist()
        zstd  = z_all.std(0).cpu().tolist()

    logs["final_mse"]  = mse
    logs["final_w2"]   = w2
    logs["final_zmean"] = zmean
    logs["final_zstd"]  = zstd
    logs["total_time"]  = sum(logs["epoch_time"])

    return logs


# ===========================================================================
# Plots
# ===========================================================================

def make_plots(logs_a: dict, logs_b: dict, out_path: str):
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))
    fig.suptitle(
        f"Training eval — pairwise vs spectral Neumann  "
        f"(d={EMBED_DIM}, N={BATCH_SIZE}, {N_EPOCHS} epochs)",
        fontsize=12, fontweight="bold",
    )

    epochs = list(range(1, N_EPOCHS + 1))
    ca, cb = "C0", "C1"

    # Panel 1: Total training loss
    ax = axes[0]
    ax.plot(epochs, logs_a["epoch_loss"], f"{ca}-", lw=1.5, label=logs_a["label"])
    ax.plot(epochs, logs_b["epoch_loss"], f"{cb}-", lw=1.5, label=logs_b["label"])
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Total loss (rec + λ·wb)")
    ax.set_title("Training loss")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Panel 2: Reconstruction MSE
    ax = axes[1]
    ax.plot(epochs, logs_a["epoch_rec"], f"{ca}-", lw=1.5, label=logs_a["label"])
    ax.plot(epochs, logs_b["epoch_rec"], f"{cb}-", lw=1.5, label=logs_b["label"])
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Reconstruction MSE")
    ax.set_title("Reconstruction quality")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Panel 3: Kernel time per batch (ms)
    ax = axes[2]
    ax.plot(epochs, logs_a["kernel_ms"], f"{ca}-", lw=1.5, label=logs_a["label"])
    ax.plot(epochs, logs_b["kernel_ms"], f"{cb}-", lw=1.5, label=logs_b["label"])
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Kernel forward (ms/batch)")
    ax.set_title(f"Kernel time per batch  (N={BATCH_SIZE})")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(out_path, dpi=150, bbox_inches="tight")
    print(f"Saved: {out_path}")


# ===========================================================================
# Main
# ===========================================================================

def main():
    torch.manual_seed(SEED)
    OUT = os.path.join(os.path.dirname(__file__), "train_eval.png")

    # Data
    print(f"Generating data  ({N_SAMPLES} samples, {IN_DIM}-D) ...", end=" ", flush=True)
    data = make_non_gaussian_data(N_SAMPLES, IN_DIM, seed=SEED).to(DTYPE)
    mu   = data.mean(0)
    std  = data.std(0).clamp_min(1e-6)
    data = (data - mu) / std
    print("done.")

    # Build both losses (calibrated once, reused every epoch)
    print(f"\nCalibrating pairwise loss  (batch={BATCH_SIZE}, d={EMBED_DIM}) ...", end=" ", flush=True)
    loss_pairwise = C_WristbandGaussianLoss(
        calibration_shape=(BATCH_SIZE, EMBED_DIM),
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )
    print("done.")

    print(f"Calibrating spectral loss  (batch={BATCH_SIZE}, d={EMBED_DIM}, K={K_MODES}) ...", end=" ", flush=True)
    loss_spectral = SpectralWristbandLoss(
        d=EMBED_DIM,
        k_modes=K_MODES,
        calibration_shape=(BATCH_SIZE, EMBED_DIM),
        calibration_device=DEVICE,
        calibration_dtype=DTYPE,
    )
    print("done.")

    # Identical initial weights for both runs
    torch.manual_seed(SEED)
    model_init = MLPAutoencoder(IN_DIM, EMBED_DIM).to(DEVICE)
    model_a    = copy.deepcopy(model_init)
    model_b    = copy.deepcopy(model_init)

    # Run A: pairwise
    logs_a = train_one_run(model_a, data, loss_pairwise, label="pairwise (C_WristbandGaussianLoss)")
    # Run B: spectral
    logs_b = train_one_run(model_b, data, loss_spectral, label=f"spectral (SpectralWristbandLoss, K={K_MODES})")

    # ------------------------------------------------------------------
    # Text summary
    # ------------------------------------------------------------------
    print("\n" + "=" * 65)
    print("FINAL METRICS")
    print("=" * 65)
    print(f"  {'':30s}  {'pairwise':>12}  {'spectral':>12}")
    print(f"  {'-'*57}")
    print(f"  {'Final reconstruction MSE':30s}  {logs_a['final_mse']:>12.6f}  {logs_b['final_mse']:>12.6f}")
    print(f"  {'W2² to N(0,I)':30s}  {logs_a['final_w2']:>12.4f}  {logs_b['final_w2']:>12.4f}")
    print(f"  {'Total training time (s)':30s}  {logs_a['total_time']:>12.1f}  {logs_b['total_time']:>12.1f}")
    avg_ker_a = sum(logs_a['kernel_ms']) / len(logs_a['kernel_ms'])
    avg_ker_b = sum(logs_b['kernel_ms']) / len(logs_b['kernel_ms'])
    print(f"  {'Mean kernel ms/batch':30s}  {avg_ker_a:>12.3f}  {avg_ker_b:>12.3f}")
    print(f"  {'Kernel speedup':30s}  {'':>12s}  {avg_ker_a/avg_ker_b:>11.1f}×")

    print("\n  Latent per-dim mean (pairwise):", [f"{v:.3f}" for v in logs_a['final_zmean']])
    print("  Latent per-dim mean (spectral): ", [f"{v:.3f}" for v in logs_b['final_zmean']])
    print("  Latent per-dim std  (pairwise):", [f"{v:.3f}" for v in logs_a['final_zstd']])
    print("  Latent per-dim std  (spectral): ", [f"{v:.3f}" for v in logs_b['final_zstd']])

    make_plots(logs_a, logs_b, OUT)


if __name__ == "__main__":
    main()
