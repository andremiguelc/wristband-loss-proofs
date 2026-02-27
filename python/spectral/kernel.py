"""
Spectral Neumann kernel for the Wristband Gaussian Loss.

All kernel math in one place:
  - SpectralNeumannCoefficients  : precomputed λ₀, λ₁, a_k
  - build_spectral_neumann_coefficients : one-time coefficient setup
  - spectral_neumann_energy_l01  : O(NdK) forward pass (the core computation)
  - spectral_neumann_rep_loss    : log-energy repulsion loss
  - SpectralWristbandLoss        : drop-in for C_WristbandGaussianLoss

Mathematical correspondence to Lean (WristbandLossProofs/Spectral/):
  l=0, l=1 mode projections  ↔  SpectralPrimitives.lean `modeProj`
  a_k radial coefficients     ↔  SpectralPrimitives.lean `radialFeature`, `radialCoeff`
  spectral_neumann_energy_l01 ↔  SpectralPrimitives.lean `spectralEnergy`

Notes:
  - Requires d >= 3 (matches Lean assumption).
  - Angular eigenvalues for l=0 and l=1 only; l=2 contributes <0.05% at d>=128.
  - Eigenvalues computed in log-domain to avoid Bessel underflow at large d.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import NamedTuple, Optional

import torch
import torch.linalg
from scipy.special import gammaln, ive, iv


# ===========================================================================
# Spectral coefficients
# ===========================================================================

@dataclass(frozen=True)
class SpectralNeumannCoefficients:
    """Precomputed spectral coefficients for the Neumann target.

    lam_0 : angular eigenvalue for l=0 (constant spherical harmonic).
    lam_1 : angular eigenvalue for l=1 (linear spherical harmonics).
    a_k   : radial Neumann coefficients, shape (K,).
    """
    lam_0: float
    lam_1: float
    a_k: torch.Tensor


def _safe_log_ive(order: float, c: float) -> float:
    """log(ive(order, c)) with fallback for underflow."""
    v = float(ive(order, c))
    if v > 0.0 and math.isfinite(v):
        return math.log(v)
    # ive underflowed: use iv (unscaled) and subtract c
    v = float(iv(order, c))
    if v > 0.0 and math.isfinite(v):
        return math.log(v) - c
    raise FloatingPointError(
        f"Cannot evaluate Bessel term for order={order}, c={c}."
    )


def _angular_eigenvalue_l(d: int, beta: float, alpha: float, ell: int) -> float:
    """λ_ell = Γ(ν+1) · (2/c)^ν · ive(ell+ν, c),  ν=(d-2)/2,  c=2βα²."""
    if d < 3:
        raise ValueError("Spectral Neumann path requires d >= 3.")
    nu = 0.5 * (d - 2)
    c  = 2.0 * beta * (alpha ** 2)
    log_prefactor = float(gammaln(nu + 1.0) + nu * (math.log(2.0) - math.log(c)))
    log_ive       = _safe_log_ive(nu + ell, c)
    log_lambda    = log_prefactor + log_ive
    if log_lambda < math.log(float(torch.finfo(torch.float64).tiny)):
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
    """Precompute λ₀, λ₁ and radial Neumann coefficients a_k.

    Call once at construction time; pass the result to spectral_neumann_energy_l01.

    Parameters
    ----------
    d       : embedding dimension (>= 3)
    beta    : radial bandwidth
    alpha   : angular–radial coupling scale
    k_modes : number of radial modes K (k=0..K-1)
    device, dtype : target for the a_k tensor
    """
    if k_modes < 1:
        raise ValueError("k_modes must be >= 1.")
    lam_0 = _angular_eigenvalue_l(d, beta, alpha, ell=0)
    lam_1 = _angular_eigenvalue_l(d, beta, alpha, ell=1)
    beta_t  = torch.as_tensor(beta, device=device, dtype=dtype)
    k_range = torch.arange(k_modes, device=device, dtype=dtype)
    pref    = torch.sqrt(torch.pi / beta_t)
    a_k = pref * torch.where(
        k_range == 0,
        torch.ones_like(k_range),
        2.0 * torch.exp(-(torch.pi ** 2) * k_range.square() / (4.0 * beta_t)),
    )
    return SpectralNeumannCoefficients(lam_0=lam_0, lam_1=lam_1, a_k=a_k)


# ===========================================================================
# Forward pass — O(NdK)
# ===========================================================================

def spectral_neumann_energy_l01(
    u: torch.Tensor,
    t: torch.Tensor,
    coeffs: SpectralNeumannCoefficients,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Spectral energies (E_0, E_1, E_total) for l ≤ 1.

    This is the core O(NdK) computation, corresponding to `spectralEnergy`
    in SpectralPrimitives.lean.

    Parameters
    ----------
    u      : (N, d) unit-normalised embeddings (wristband angular component)
    t      : (N,)  radial CDF values in [0, 1]  (wristband radial component)
    coeffs : precomputed SpectralNeumannCoefficients

    Returns
    -------
    (e_0, e_1, e_total) — scalar Tensors.
      e_0     = λ₀ · Σ_k a_k · c_0k²    (l=0 constant mode)
      e_1     = λ₁ · Σ_{j,k} a_k · c_1jk²  (l=1 directional modes)
      e_total = e_0 + e_1
    """
    if u.ndim != 2 or t.ndim != 1 or u.shape[0] != t.shape[0]:
        raise ValueError(
            f"Expected u (N,d) and t (N,); got {tuple(u.shape)}, {tuple(t.shape)}."
        )
    n, d = u.shape
    if d < 3:
        raise ValueError("Spectral Neumann path requires d >= 3.")

    a_k     = coeffs.a_k.to(device=t.device, dtype=t.dtype)
    k_range = torch.arange(int(a_k.shape[0]), device=t.device, dtype=t.dtype)
    cos_mat = torch.cos(torch.pi * k_range[None, :] * t[:, None])  # (N, K)

    c_0k = cos_mat.mean(dim=0)                                      # (K,)
    c_1k = (math.sqrt(float(d)) / float(n)) * (u.T @ cos_mat)      # (d, K)

    lam_0_t = torch.as_tensor(coeffs.lam_0, device=t.device, dtype=t.dtype)
    lam_1_t = torch.as_tensor(coeffs.lam_1, device=t.device, dtype=t.dtype)

    e_0 = lam_0_t * (a_k * c_0k.square()).sum()
    e_1 = lam_1_t * (a_k[None, :] * c_1k.square()).sum()
    return e_0, e_1, e_0 + e_1


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
) -> tuple[torch.Tensor, dict]:
    """Neumann-spectral repulsion loss: log(E_total / norm) / β.

    Parameters
    ----------
    u, t   : wristband coordinates (see spectral_neumann_energy_l01)
    beta   : bandwidth (same as C_WristbandGaussianLoss)
    alpha  : angular–radial coupling scale
    k_modes: number of radial modes (ignored if coeffs is provided)
    coeffs : precomputed coefficients (built from beta/alpha/d if None)

    Returns
    -------
    (rep_loss, info)  where info = {"e_0", "e_1", "e_total"}
    """
    if coeffs is None:
        coeffs = build_spectral_neumann_coefficients(
            d=int(u.shape[1]), beta=beta, alpha=alpha, k_modes=k_modes,
            device=u.device, dtype=u.dtype,
        )
    e_0, e_1, e_total = spectral_neumann_energy_l01(u, t, coeffs)
    scaled = e_total / float(normalization_constant)
    beta_t = torch.as_tensor(beta, device=u.device, dtype=u.dtype)
    rep_loss = torch.log(torch.clamp_min(scaled, eps)) / beta_t
    return rep_loss, {"e_0": e_0, "e_1": e_1, "e_total": e_total}


# ===========================================================================
# SpectralWristbandLoss — drop-in for C_WristbandGaussianLoss
# ===========================================================================

class S_LossComponents(NamedTuple):
    """Named loss components (mirrors ml-tidbits S_LossComponents)."""
    total: torch.Tensor
    rep:   torch.Tensor
    rad:   torch.Tensor
    ang:   torch.Tensor
    mom:   torch.Tensor


def _eps_for_dtype(dtype: torch.dtype, large: bool = False) -> float:
    eps = torch.finfo(dtype).eps
    return math.sqrt(eps) if large else eps


def _w2_to_standard_normal_sq(x: torch.Tensor) -> torch.Tensor:
    """Squared 2-Wasserstein distance between empirical Gaussian fit and N(0,I)."""
    b, d = x.shape[-2], x.shape[-1]
    wdtype = torch.float32 if x.dtype in (torch.float16, torch.bfloat16) else x.dtype
    xw  = x.to(wdtype)
    mu  = xw.mean(dim=-2, keepdim=True)
    xc  = xw - mu
    mu2 = mu.squeeze(-2).square().sum(dim=-1)
    denom = float(b - 1)
    if d <= b:
        m, m_dim = (xc.transpose(-1, -2) @ xc) / denom, d
    else:
        m, m_dim = (xc @ xc.transpose(-1, -2)) / denom, b
    m    = 0.5 * (m + m.transpose(-1, -2))
    eig  = torch.linalg.eigvalsh(m).clamp_min(0.)
    sqrt = torch.sqrt(eig + _eps_for_dtype(eig.dtype))
    bw2  = (sqrt - 1.).square().sum(dim=-1)
    if d > m_dim:
        bw2 = bw2 + (d - m_dim)
    return mu2 + bw2


class SpectralWristbandLoss:
    r"""Wristband repulsion loss with spectral Neumann rep term.

    Drop-in for C_WristbandGaussianLoss (same __call__ interface returning
    S_LossComponents).  The `rep` component uses the l≤1 spectral energy
    E = λ₀·E₀ + λ₁·E₁  at O(NdK) instead of the pairwise O(N²d) kernel sum.

    Parameters
    ----------
    d          : embedding dimension (>= 3)
    beta       : bandwidth
    alpha      : angular–radial coupling; None → √(1/12) (chordal heuristic)
    k_modes    : radial Neumann modes K (default 6)
    lambda_rad : weight for 1D radial W2² penalty
    moment     : "w2" | "kl_diag" | "mu_only"
    lambda_mom : weight for moment penalty
    calibration_shape, calibration_reps, calibration_device, calibration_dtype :
        Monte-Carlo null calibration.  Pass calibration_shape=None to skip.
    """

    def __init__(self, *,
        d: int,
        beta: float = 8.,
        alpha: float | None = None,
        k_modes: int = 6,
        lambda_rad: float = 0.1,
        moment: str = "w2",
        lambda_mom: float = 1.,
        calibration_shape: tuple[int, int] | None = None,
        calibration_reps: int = 1024,
        calibration_device: str | torch.device = "cpu",
        calibration_dtype: torch.dtype = torch.float32,
        normalization_constant: float = 1.0,
    ):
        if d < 3:   raise ValueError("SpectralWristbandLoss requires d >= 3.")
        if beta <= 0: raise ValueError("beta must be > 0.")
        if moment not in ("w2", "kl_diag", "mu_only"):
            raise ValueError("moment must be 'w2', 'kl_diag', or 'mu_only'.")

        self.d = int(d);  self.beta = float(beta);  self.k_modes = int(k_modes)
        self.lambda_rad = float(lambda_rad);  self.moment = moment
        self.lambda_mom = float(lambda_mom)
        self.normalization_constant = float(normalization_constant)
        self.eps = 1e-12

        if alpha is None:
            alpha = math.sqrt(1. / 12.)
        self.alpha = float(alpha)

        dev = torch.device(calibration_device) if isinstance(calibration_device, str) else calibration_device
        self.coeffs = build_spectral_neumann_coefficients(
            d=self.d, beta=self.beta, alpha=self.alpha, k_modes=self.k_modes,
            device=dev, dtype=calibration_dtype,
        )

        self.mean_rep = self.mean_rad = self.mean_mom = 0.
        self.std_rep  = self.std_rad  = self.std_mom  = 1.
        self.std_total = 1.

        if calibration_shape is not None:
            self._calibrate(calibration_shape, calibration_reps, calibration_device, calibration_dtype)

    def _wristband_map(self, xw):
        eps = self.eps
        s = xw.square().sum(dim=-1).clamp_min(eps)
        u = xw * torch.rsqrt(s)[..., :, None]
        a = s.new_tensor(0.5 * float(xw.shape[-1]))
        t = torch.special.gammainc(a, 0.5 * s).clamp(eps, 1. - eps)
        return u, t

    def _moment_penalty(self, xw):
        if self.moment == "w2":
            return _w2_to_standard_normal_sq(xw) / float(xw.shape[-1])
        elif self.moment == "kl_diag":
            n_f = float(xw.shape[-2])
            mu  = xw.mean(dim=-2)
            xc  = xw - mu[..., None, :]
            var = xc.square().sum(dim=-2) / (n_f - 1.)
            return 0.5 * (var + mu.square() - 1. - torch.log(var + self.eps)).mean(dim=-1)
        else:
            return xw.mean(dim=-2).square().mean(dim=-1)

    def _compute(self, x):
        if x.ndim < 2:
            raise ValueError(f"Expected x.ndim>=2, got {tuple(x.shape)}.")
        n, d = int(x.shape[-2]), int(x.shape[-1])
        if d != self.d:
            raise ValueError(f"Expected d={self.d}, got {d}.")
        batch_shape = x.shape[:-2]
        if n < 2:
            z = x.sum(dim=(-2, -1)) * 0.
            return S_LossComponents(z, z, z, z, z)

        wdtype = torch.float32 if x.dtype in (torch.float16, torch.bfloat16) else x.dtype
        xw = x.to(wdtype)
        u, t = self._wristband_map(xw)

        mom_pen = xw.new_zeros(batch_shape)
        if self.lambda_mom != 0.:
            mom_pen = self._moment_penalty(xw)

        rad_loss = xw.new_zeros(batch_shape)
        if self.lambda_rad != 0.:
            t_sorted, _ = torch.sort(t, dim=-1)
            q = (torch.arange(n, device=xw.device, dtype=wdtype) + 0.5) / float(n)
            rad_loss = 12. * (t_sorted - q).square().mean(dim=-1)

        coeffs_dev = SpectralNeumannCoefficients(
            lam_0=self.coeffs.lam_0, lam_1=self.coeffs.lam_1,
            a_k=self.coeffs.a_k.to(device=xw.device, dtype=wdtype),
        )
        if x.ndim == 2:
            rep_loss, _ = spectral_neumann_rep_loss(
                u, t, beta=self.beta, alpha=self.alpha, k_modes=self.k_modes,
                coeffs=coeffs_dev, normalization_constant=self.normalization_constant,
                eps=self.eps,
            )
        else:
            flat_u, flat_t = u.reshape(-1, n, d), t.reshape(-1, n)
            results = [
                spectral_neumann_rep_loss(
                    flat_u[i], flat_t[i], beta=self.beta, alpha=self.alpha,
                    k_modes=self.k_modes, coeffs=coeffs_dev,
                    normalization_constant=self.normalization_constant, eps=self.eps,
                )[0]
                for i in range(flat_u.shape[0])
            ]
            rep_loss = torch.stack(results).reshape(batch_shape)

        ang_loss = xw.new_zeros(batch_shape)
        return S_LossComponents(rep_loss, rep_loss, rad_loss, ang_loss, mom_pen)

    def _calibrate(self, shape, reps, device, dtype):
        n, d = shape
        if n < 2 or d != self.d or reps < 2:
            return
        all_rep, all_rad, all_mom = [], [], []
        with torch.no_grad():
            for _ in range(int(reps)):
                comp = self._compute(torch.randn(n, d, device=device, dtype=dtype))
                all_rep.append(float(comp.rep))
                all_rad.append(float(comp.rad))
                all_mom.append(float(comp.mom))
        rf  = float(reps)
        bsl = rf / (rf - 1.)

        def _stats(vals):
            m = sum(vals) / rf
            v = (sum(x * x for x in vals) / rf - m * m) * bsl
            return m, v

        self.mean_rep, var_rep = _stats(all_rep)
        self.mean_rad, var_rad = _stats(all_rad)
        self.mean_mom, var_mom = _stats(all_mom)
        eps_c = _eps_for_dtype(dtype, True)
        self.std_rep   = math.sqrt(max(var_rep,  eps_c))
        self.std_rad   = math.sqrt(max(var_rad,  eps_c))
        self.std_mom   = math.sqrt(max(var_mom,  eps_c))

        sum_t = sum2_t = 0.
        for rep, rad, mom in zip(all_rep, all_rad, all_mom):
            tot = ((rep - self.mean_rep) / self.std_rep
                   + self.lambda_rad * (rad - self.mean_rad) / self.std_rad
                   + self.lambda_mom * (mom - self.mean_mom) / self.std_mom)
            sum_t += tot;  sum2_t += tot * tot
        m_t = sum_t / rf
        self.std_total = math.sqrt(max((sum2_t / rf - m_t * m_t) * bsl, eps_c))

    def __call__(self, x: torch.Tensor) -> S_LossComponents:
        """Compute calibrated spectral wristband loss.  x : (..., N, d)."""
        comp = self._compute(x)
        nr   = (comp.rep - self.mean_rep) / self.std_rep
        nrad = (comp.rad - self.mean_rad) / self.std_rad
        nmom = (comp.mom - self.mean_mom) / self.std_mom
        total = (nr + self.lambda_rad * nrad + self.lambda_mom * nmom) / self.std_total
        m = lambda t: t.mean() if t.ndim > 0 else t
        return S_LossComponents(m(total), m(nr), m(nrad), comp.ang, m(nmom))
