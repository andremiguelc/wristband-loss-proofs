"""Custom Pythae model subclasses for the spectral wristband benchmark.

Each model subclasses pythae's AE and overrides forward() to add its
regularization penalty. All models share the same encoder/decoder — only
the latent penalty differs.

Models:
  SpectralWristbandAE  — O(NdK) spectral decomposition (our method)
  PairwiseWristbandAE  — O(N^2d) pairwise kernel (ablation baseline)
  SWAE                 — Sliced Wasserstein AE
  RFF_MMD_AE           — Random Fourier Features MMD
"""

from __future__ import annotations

import math
from typing import Optional

import torch
import torch.nn.functional as F
from pydantic.dataclasses import dataclass

from pythae.models.ae import AE, AEConfig
from pythae.models.base.base_utils import ModelOutput
from pythae.models.nn import BaseDecoder, BaseEncoder

# ---------------------------------------------------------------------------
# Configs
# ---------------------------------------------------------------------------

@dataclass
class SpectralWristbandConfig(AEConfig):
    """Config for spectral wristband AE."""
    reg_weight: float = 1.0
    beta: float = 8.0
    alpha: float = 0.28867513459481287  # 1/sqrt(12)
    k_modes: int = 6
    lambda_rad: float = 0.1
    lambda_mom: float = 1.0
    calibration_reps: int = 512


@dataclass
class PairwiseWristbandConfig(AEConfig):
    """Config for pairwise wristband AE (O(N^2) ablation)."""
    reg_weight: float = 1.0
    beta: float = 8.0
    alpha: float = 0.28867513459481287
    lambda_rad: float = 0.1
    lambda_mom: float = 1.0
    calibration_reps: int = 512


@dataclass
class SWAEConfig(AEConfig):
    """Config for sliced Wasserstein AE."""
    reg_weight: float = 10.0
    num_projections: int = 50


@dataclass
class RFF_MMD_Config(AEConfig):
    """Config for random Fourier features MMD AE."""
    reg_weight: float = 3e-2
    rff_dim: int = 500
    kernel_bandwidth: float = 1.0


# ---------------------------------------------------------------------------
# Spectral Wristband AE (our method)
# ---------------------------------------------------------------------------

class SpectralWristbandAE(AE):
    """Wristband AE with O(NdK) spectral repulsion loss."""

    def __init__(
        self,
        model_config: SpectralWristbandConfig,
        encoder: Optional[BaseEncoder] = None,
        decoder: Optional[BaseDecoder] = None,
    ):
        AE.__init__(self, model_config=model_config, encoder=encoder, decoder=decoder)
        self.model_name = "SpectralWristbandAE"

        # Try direct import first (works when python/ is on sys.path).
        # Fall back to relative path for local use.
        try:
            from spectral.kernel import SpectralWristbandLoss
        except ImportError:
            import sys, os
            sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
            from spectral.kernel import SpectralWristbandLoss

        d = model_config.latent_dim
        cal_shape = (256, d) if model_config.calibration_reps > 0 else None
        self.wb_loss = SpectralWristbandLoss(
            d=d,
            beta=model_config.beta,
            alpha=model_config.alpha,
            k_modes=model_config.k_modes,
            lambda_rad=model_config.lambda_rad,
            lambda_mom=model_config.lambda_mom,
            calibration_shape=cal_shape,
            calibration_reps=model_config.calibration_reps,
        )

    def forward(self, inputs, **kwargs) -> ModelOutput:
        x = inputs["data"]
        z = self.encoder(x).embedding
        recon_x = self.decoder(z)["reconstruction"]

        recon_loss = F.mse_loss(
            recon_x.reshape(x.shape[0], -1),
            x.reshape(x.shape[0], -1),
            reduction="none",
        ).sum(dim=-1).mean()

        wb = self.wb_loss(z)
        loss = recon_loss + self.model_config.reg_weight * wb.total

        return ModelOutput(
            loss=loss, recon_loss=recon_loss,
            reg_loss=wb.total, recon_x=recon_x, z=z,
        )


# ---------------------------------------------------------------------------
# Pairwise Wristband AE (O(N^2) ablation)
# ---------------------------------------------------------------------------

class PairwiseWristbandAE(AE):
    """Wristband AE with O(N^2) pairwise kernel (ablation baseline)."""

    def __init__(
        self,
        model_config: PairwiseWristbandConfig,
        encoder: Optional[BaseEncoder] = None,
        decoder: Optional[BaseDecoder] = None,
    ):
        AE.__init__(self, model_config=model_config, encoder=encoder, decoder=decoder)
        self.model_name = "PairwiseWristbandAE"

        # Try direct import first (works when ml-tidbits/python is on sys.path,
        # e.g. from the notebook setup cell). Fall back to relative path for local use.
        try:
            from embed_models.EmbedModels import C_WristbandGaussianLoss
        except ImportError:
            import sys, os
            tidbits_path = os.path.abspath(os.path.join(
                os.path.dirname(__file__), "..", "..", "ml-tidbits", "python"
            ))
            if tidbits_path not in sys.path:
                sys.path.insert(0, tidbits_path)
            from embed_models.EmbedModels import C_WristbandGaussianLoss

        d = model_config.latent_dim
        cal_shape = (256, d) if model_config.calibration_reps > 0 else None
        self.wb_loss = C_WristbandGaussianLoss(
            beta=model_config.beta,
            alpha=model_config.alpha,
            lambda_rad=model_config.lambda_rad,
            lambda_mom=model_config.lambda_mom,
            calibration_shape=cal_shape,
            calibration_reps=model_config.calibration_reps,
        )

    def forward(self, inputs, **kwargs) -> ModelOutput:
        x = inputs["data"]
        z = self.encoder(x).embedding
        recon_x = self.decoder(z)["reconstruction"]

        recon_loss = F.mse_loss(
            recon_x.reshape(x.shape[0], -1),
            x.reshape(x.shape[0], -1),
            reduction="none",
        ).sum(dim=-1).mean()

        wb = self.wb_loss(z)
        loss = recon_loss + self.model_config.reg_weight * wb.total

        return ModelOutput(
            loss=loss, recon_loss=recon_loss,
            reg_loss=wb.total, recon_x=recon_x, z=z,
        )


# ---------------------------------------------------------------------------
# SWAE — Sliced Wasserstein Autoencoder
# ---------------------------------------------------------------------------

def _sliced_wasserstein_distance(z: torch.Tensor, z_prior: torch.Tensor, num_proj: int) -> torch.Tensor:
    """Sliced Wasserstein distance between z and z_prior."""
    d = z.shape[1]
    # random projections on unit sphere
    projections = torch.randn(num_proj, d, device=z.device, dtype=z.dtype)
    projections = projections / projections.norm(dim=1, keepdim=True)

    # project and sort
    z_proj = z @ projections.T          # (N, num_proj)
    zp_proj = z_prior @ projections.T   # (N, num_proj)

    z_sorted, _ = z_proj.sort(dim=0)
    zp_sorted, _ = zp_proj.sort(dim=0)

    return (z_sorted - zp_sorted).square().mean()


class SWAE(AE):
    """Sliced Wasserstein Autoencoder."""

    def __init__(
        self,
        model_config: SWAEConfig,
        encoder: Optional[BaseEncoder] = None,
        decoder: Optional[BaseDecoder] = None,
    ):
        AE.__init__(self, model_config=model_config, encoder=encoder, decoder=decoder)
        self.model_name = "SWAE"

    def forward(self, inputs, **kwargs) -> ModelOutput:
        x = inputs["data"]
        z = self.encoder(x).embedding
        recon_x = self.decoder(z)["reconstruction"]

        recon_loss = F.mse_loss(
            recon_x.reshape(x.shape[0], -1),
            x.reshape(x.shape[0], -1),
            reduction="none",
        ).sum(dim=-1).mean()

        z_prior = torch.randn_like(z)
        swd = _sliced_wasserstein_distance(z, z_prior, self.model_config.num_projections)
        loss = recon_loss + self.model_config.reg_weight * swd

        return ModelOutput(
            loss=loss, recon_loss=recon_loss,
            reg_loss=swd, recon_x=recon_x, z=z,
        )


# ---------------------------------------------------------------------------
# RFF-MMD AE — Random Fourier Features MMD
# ---------------------------------------------------------------------------

def _rff_mmd(z: torch.Tensor, z_prior: torch.Tensor, rff_dim: int, bandwidth: float) -> torch.Tensor:
    """MMD^2 via random Fourier features (Rahimi & Recht 2007)."""
    d = z.shape[1]
    sigma = math.sqrt(d * bandwidth ** 2)

    # sample random frequencies and bias
    W = torch.randn(d, rff_dim, device=z.device, dtype=z.dtype) / sigma
    b = torch.rand(rff_dim, device=z.device, dtype=z.dtype) * (2.0 * math.pi)

    # feature maps: sqrt(2/D) * cos(zW + b)
    scale = math.sqrt(2.0 / rff_dim)
    phi_z = scale * torch.cos(z @ W + b)        # (N, rff_dim)
    phi_zp = scale * torch.cos(z_prior @ W + b)  # (N, rff_dim)

    # MMD^2 = || mean(phi_z) - mean(phi_zp) ||^2
    diff = phi_z.mean(dim=0) - phi_zp.mean(dim=0)
    return diff.dot(diff)


class RFF_MMD_AE(AE):
    """AE with Random Fourier Features MMD regularization."""

    def __init__(
        self,
        model_config: RFF_MMD_Config,
        encoder: Optional[BaseEncoder] = None,
        decoder: Optional[BaseDecoder] = None,
    ):
        AE.__init__(self, model_config=model_config, encoder=encoder, decoder=decoder)
        self.model_name = "RFF_MMD_AE"

    def forward(self, inputs, **kwargs) -> ModelOutput:
        x = inputs["data"]
        z = self.encoder(x).embedding
        recon_x = self.decoder(z)["reconstruction"]

        recon_loss = F.mse_loss(
            recon_x.reshape(x.shape[0], -1),
            x.reshape(x.shape[0], -1),
            reduction="none",
        ).sum(dim=-1).mean()

        z_prior = torch.randn_like(z)
        mmd = _rff_mmd(z, z_prior, self.model_config.rff_dim, self.model_config.kernel_bandwidth)
        loss = recon_loss + self.model_config.reg_weight * mmd

        return ModelOutput(
            loss=loss, recon_loss=recon_loss,
            reg_loss=mmd, recon_x=recon_x, z=z,
        )
