"""
Spectral Neumann kernel for the Wristband Gaussian Loss.

Implements the l <= 1, k < K spectral decomposition of the Neumann
radial kernel, matching the Lean proof in SpectralFoundations.lean.

Notes:
- Requires d >= 3 (d=2 rejected by design, matches Lean assumption).
- Angular eigenvalues are computed for l=0 (constant mode) and l=1
  (linear/directional mode) only. Higher l vanish faster under the
  radial Neumann weights for practical k_modes.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Optional

import torch
from scipy.special import gammaln, ive, iv


@dataclass(frozen=True)
class SpectralNeumannCoefficients:
    """Precomputed spectral coefficients for the Neumann target path.

    Attributes
    ----------
    lam_0 : float
        Angular eigenvalue for l=0 (constant spherical harmonic).
    lam_1 : float
        Angular eigenvalue for l=1 (linear spherical harmonics).
    a_k : Tensor of shape (K,)
        Radial Neumann coefficients for k=0..K-1.
    """
    lam_0: float
    lam_1: float
    a_k: torch.Tensor


def legacy_3image_denominator(n: int) -> float:
    """Denominator used in the ml-tidbits 3-image path (per_point reduction)."""
    return float(3 * n * n - n)


def _safe_log_ive(order: float, c: float) -> float:
    """Stable log(ive(order, c)) with iv fallback."""
    ive_val = float(ive(order, c))
    if ive_val > 0.0 and math.isfinite(ive_val):
        return math.log(ive_val)
    iv_val = float(iv(order, c))
    if iv_val > 0.0 and math.isfinite(iv_val):
        return math.log(iv_val) - c
    raise FloatingPointError(
        f"Cannot evaluate Bessel term for order={order}, c={c}."
    )


def _angular_eigenvalue_l(d: int, beta: float, alpha: float, ell: int) -> float:
    """Angular eigenvalue for spherical harmonic degree ell.

    lambda_ell = Gamma(nu+1) * (2/c)^nu * ive(ell+nu, c)

    where nu = (d-2)/2 and c = 2*beta*alpha^2.
    """
    if d < 3:
        raise ValueError("Spectral Neumann path requires d >= 3.")
    if beta <= 0.0:
        raise ValueError("beta must be > 0.")
    if alpha <= 0.0:
        raise ValueError("alpha must be > 0.")
    if ell < 0:
        raise ValueError("ell must be >= 0.")

    nu = 0.5 * (d - 2)
    c = 2.0 * beta * (alpha ** 2)
    if c <= 0.0:
        raise ValueError("c = 2*beta*alpha^2 must be > 0.")

    log_prefactor = float(gammaln(nu + 1.0) + nu * (math.log(2.0) - math.log(c)))
    log_ive = _safe_log_ive(nu + ell, c)
    log_lambda = log_prefactor + log_ive

    max_log = math.log(float(torch.finfo(torch.float64).max))
    min_log = math.log(float(torch.finfo(torch.float64).tiny))
    if log_lambda > max_log:
        raise FloatingPointError(
            f"Angular eigenvalue overflow for ell={ell}, d={d}, beta={beta}, alpha={alpha}."
        )
    if log_lambda < min_log:
        return 0.0

    lam = math.exp(log_lambda)
    if not math.isfinite(lam) or lam < 0.0:
        raise FloatingPointError(f"Invalid angular eigenvalue: {lam}.")
    return lam


def build_spectral_neumann_coefficients(
    d: int,
    beta: float,
    alpha: float,
    k_modes: int,
    *,
    device: torch.device,
    dtype: torch.dtype,
) -> SpectralNeumannCoefficients:
    """Precompute l=0/l=1 angular eigenvalues and radial Neumann coefficients.

    Typically called once at loss construction time.

    Parameters
    ----------
    d : int
        Embedding dimension (must be >= 3).
    beta : float
        Radial bandwidth.
    alpha : float
        Angular-radial coupling scale.
    k_modes : int
        Number of Neumann radial modes K (k=0..K-1).
    device, dtype :
        Target device/dtype for the a_k tensor.
    """
    if k_modes < 1:
        raise ValueError("k_modes must be >= 1.")

    lam_0 = _angular_eigenvalue_l(d, beta, alpha, ell=0)
    lam_1 = _angular_eigenvalue_l(d, beta, alpha, ell=1)

    beta_t = torch.as_tensor(beta, device=device, dtype=dtype)
    k_range = torch.arange(k_modes, device=device, dtype=dtype)
    radial_pref = torch.sqrt(torch.pi / beta_t)
    a_k = radial_pref * torch.where(
        k_range == 0,
        torch.ones_like(k_range),
        2.0 * torch.exp(-(torch.pi ** 2) * k_range.square() / (4.0 * beta_t)),
    )

    return SpectralNeumannCoefficients(lam_0=lam_0, lam_1=lam_1, a_k=a_k)


def spectral_neumann_energy_l01(
    u: torch.Tensor,
    t: torch.Tensor,
    coeffs: SpectralNeumannCoefficients,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Compute spectral energies E_0, E_1, E_total for l <= 1.

    Parameters
    ----------
    u : Tensor of shape (N, d)
        Unit-normalized embeddings.
    t : Tensor of shape (N,)
        Radial CDF values in [0, 1].
    coeffs : SpectralNeumannCoefficients

    Returns
    -------
    (e_0, e_1, e_total) : each a scalar Tensor.
    """
    if u.ndim != 2:
        raise ValueError(f"Expected u shape (N, d), got {tuple(u.shape)}.")
    if t.ndim != 1:
        raise ValueError(f"Expected t shape (N,), got {tuple(t.shape)}.")
    if u.shape[0] != t.shape[0]:
        raise ValueError("u and t must share batch dimension N.")
    n, d = u.shape
    if d < 3:
        raise ValueError("Spectral Neumann path requires d >= 3.")

    a_k = coeffs.a_k.to(device=t.device, dtype=t.dtype)
    k_modes = int(a_k.shape[0])

    k_range = torch.arange(k_modes, device=t.device, dtype=t.dtype)
    cos_mat = torch.cos(torch.pi * k_range[None, :] * t[:, None])  # (N, K)

    c_0k = cos_mat.mean(dim=0)                                          # (K,)
    c_1k = (math.sqrt(float(d)) / float(n)) * (u.T @ cos_mat)          # (d, K)

    lam_0_t = torch.as_tensor(coeffs.lam_0, device=t.device, dtype=t.dtype)
    lam_1_t = torch.as_tensor(coeffs.lam_1, device=t.device, dtype=t.dtype)

    e_0 = lam_0_t * (a_k * c_0k.square()).sum()
    e_1 = lam_1_t * (a_k[None, :] * c_1k.square()).sum()
    e_total = e_0 + e_1
    return e_0, e_1, e_total


def spectral_neumann_rep_loss(
    u: torch.Tensor,
    t: torch.Tensor,
    *,
    beta: float,
    alpha: float,
    k_modes: int = 6,
    coeffs: Optional[SpectralNeumannCoefficients] = None,
    normalization_constant: float = 1.0,
    eps: float = 1e-12,
) -> tuple[torch.Tensor, dict[str, torch.Tensor]]:
    """Compute the Neumann-spectral repulsion loss.

    Returns
    -------
    (rep_loss, info) where info contains e_0, e_1, e_total, lam_0, lam_1.
    """
    if normalization_constant <= 0.0:
        raise ValueError("normalization_constant must be > 0.")
    if eps <= 0.0:
        raise ValueError("eps must be > 0.")

    if coeffs is None:
        coeffs = build_spectral_neumann_coefficients(
            d=int(u.shape[1]),
            beta=float(beta),
            alpha=float(alpha),
            k_modes=k_modes,
            device=u.device,
            dtype=u.dtype,
        )

    e_0, e_1, e_total = spectral_neumann_energy_l01(u, t, coeffs)
    scaled_energy = e_total / float(normalization_constant)

    beta_t = torch.as_tensor(beta, device=u.device, dtype=u.dtype)
    rep_loss = torch.log(torch.clamp_min(scaled_energy, eps)) / beta_t

    info = {
        "e_0": e_0,
        "e_1": e_1,
        "e_total": e_total,
        "scaled_energy": scaled_energy,
        "lam_0": torch.as_tensor(coeffs.lam_0, device=u.device, dtype=u.dtype),
        "lam_1": torch.as_tensor(coeffs.lam_1, device=u.device, dtype=u.dtype),
    }
    return rep_loss, info
