"""
SpectralWristbandLoss — same external interface as C_WristbandGaussianLoss,
but the repulsion term is replaced by the Neumann-spectral energy E_0 + E_1.

All other components (radial W2, moment penalty, calibration) are identical
to the ml-tidbits reference implementation so comparisons are apples-to-apples.
"""

from __future__ import annotations

import math
from typing import NamedTuple

import torch
import torch.linalg

from .neumann import (
    SpectralNeumannCoefficients,
    build_spectral_neumann_coefficients,
    spectral_neumann_energy_l01,
    spectral_neumann_rep_loss,
)


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
    """Squared 2-Wasserstein distance between Gaussian fit of x and N(0,I), shape (...)."""
    b = x.shape[-2]
    d = x.shape[-1]
    wdtype = torch.float32 if x.dtype in (torch.float16, torch.bfloat16) else x.dtype
    xw = x.to(wdtype)
    mu = xw.mean(dim=-2, keepdim=True)
    xc = xw - mu
    mu2 = mu.squeeze(-2).square().sum(dim=-1)
    denom = float(b - 1)
    if d <= b:
        m = (xc.transpose(-1, -2) @ xc) / denom
        m_dim = d
    else:
        m = (xc @ xc.transpose(-1, -2)) / denom
        m_dim = b
    m = 0.5 * (m + m.transpose(-1, -2))
    eig = torch.linalg.eigvalsh(m).clamp_min(0.)
    sqrt_eig = torch.sqrt(eig + _eps_for_dtype(eig.dtype))
    bw2 = (sqrt_eig - 1.).square().sum(dim=-1)
    if d > m_dim:
        bw2 = bw2 + (d - m_dim)
    return mu2 + bw2


class SpectralWristbandLoss:
    r"""Wristband repulsion loss with spectral Neumann repulsion term.

    Drops-in for ``C_WristbandGaussianLoss`` (same ``__call__`` interface).
    The ``rep`` component is replaced by the l<=1 spectral energy:

        E_spectral = lam_0 * E_0 + lam_1 * E_1

    where E_0, E_1 are the projections of the empirical (u,t) measure onto
    the l=0 and l=1 Neumann–cosine modes respectively.

    Parameters
    ----------
    d : int
        Embedding dimension.  Required for spectral coefficient precomputation.
    beta : float
        Bandwidth parameter (same as C_WristbandGaussianLoss).
    alpha : float | None
        Angular–radial coupling scale.  None picks the same chordal heuristic.
    k_modes : int
        Number of Neumann radial modes to keep (K).
    lambda_rad, lambda_mom : float
        Weights for radial-uniformity and moment penalty components.
    moment : str
        One of ``"w2"``, ``"kl_diag"``, ``"mu_only"``.
    calibration_shape : tuple[int, int] | None
        ``(N, D)`` for Monte-Carlo null calibration.
    calibration_reps : int
        Number of MC repetitions.
    calibration_device, calibration_dtype :
        Device/dtype for calibration samples.
    normalization_constant : float
        Divides the spectral energy before taking log.  Set to 1 by default;
        the calibration absorbs the remaining scale.
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
        if d < 3:
            raise ValueError("SpectralWristbandLoss requires d >= 3.")
        if beta <= 0:
            raise ValueError("beta must be > 0.")
        if moment not in ("w2", "kl_diag", "mu_only"):
            raise ValueError("moment must be one of 'w2', 'kl_diag', 'mu_only'.")
        if normalization_constant <= 0.:
            raise ValueError("normalization_constant must be > 0.")

        self.d = int(d)
        self.beta = float(beta)
        self.k_modes = int(k_modes)
        self.lambda_rad = float(lambda_rad)
        self.moment = moment
        self.lambda_mom = float(lambda_mom)
        self.normalization_constant = float(normalization_constant)
        self.eps = 1e-12

        if alpha is None:
            alpha = math.sqrt(1. / 12.)  # same chordal heuristic as ml-tidbits
        self.alpha = float(alpha)

        # Precompute spectral coefficients (d, beta, alpha fixed at init).
        dev = torch.device(calibration_device) if isinstance(calibration_device, str) else calibration_device
        self.coeffs: SpectralNeumannCoefficients = build_spectral_neumann_coefficients(
            d=self.d,
            beta=self.beta,
            alpha=self.alpha,
            k_modes=self.k_modes,
            device=dev,
            dtype=calibration_dtype,
        )

        # Calibration statistics (identity transform when not calibrated).
        self.mean_rep = self.mean_rad = self.mean_mom = 0.
        self.std_rep = self.std_rad = self.std_mom = 1.
        self.std_total = 1.

        if calibration_shape is not None:
            self._calibrate(calibration_shape, calibration_reps, calibration_device, calibration_dtype)

    # ------------------------------------------------------------------
    # Wristband map (identical to ml-tidbits)
    # ------------------------------------------------------------------

    def _wristband_map(self, xw: torch.Tensor):
        """Return (u, t) from batch xw of shape (..., N, d)."""
        eps = self.eps
        s = xw.square().sum(dim=-1).clamp_min(eps)       # (..., N)
        u = xw * torch.rsqrt(s)[..., :, None]             # (..., N, d)
        a_df = s.new_tensor(0.5 * float(xw.shape[-1]))
        t = torch.special.gammainc(a_df, 0.5 * s).clamp(eps, 1. - eps)  # (..., N)
        return u, t

    # ------------------------------------------------------------------
    # Moment penalty (subset of ml-tidbits options)
    # ------------------------------------------------------------------

    def _moment_penalty(self, xw: torch.Tensor) -> torch.Tensor:
        batch_shape = xw.shape[:-2]
        d_f = float(xw.shape[-1])
        eps = self.eps

        if self.moment == "w2":
            return _w2_to_standard_normal_sq(xw) / d_f
        elif self.moment == "kl_diag":
            n_f = float(xw.shape[-2])
            mu = xw.mean(dim=-2)
            xc = xw - mu[..., None, :]
            var = xc.square().sum(dim=-2) / (n_f - 1.)
            return 0.5 * (var + mu.square() - 1. - torch.log(var + eps)).mean(dim=-1)
        else:  # mu_only
            mu = xw.mean(dim=-2)
            return mu.square().mean(dim=-1)

    # ------------------------------------------------------------------
    # Core computation
    # ------------------------------------------------------------------

    def _compute(self, x: torch.Tensor) -> S_LossComponents:
        if x.ndim < 2:
            raise ValueError(f"Expected x.ndim>=2 (N, d), got {tuple(x.shape)}.")

        n = int(x.shape[-2])
        d = int(x.shape[-1])
        if d != self.d:
            raise ValueError(f"Expected d={self.d}, got {d}.")
        batch_shape = x.shape[:-2]

        if n < 2 or d < 1:
            z = x.sum(dim=(-2, -1)) * 0.
            return S_LossComponents(z, z, z, z, z)

        wdtype = torch.float32 if x.dtype in (torch.float16, torch.bfloat16) else x.dtype
        xw = x.to(wdtype)
        n_f = float(n)

        # Moment penalty
        mom_pen = xw.new_zeros(batch_shape)
        if self.lambda_mom != 0.:
            mom_pen = self._moment_penalty(xw)

        # Wristband map
        u, t = self._wristband_map(xw)

        # Radial 1D W2^2 on t vs Unif(0,1) — same as ml-tidbits
        rad_loss = xw.new_zeros(batch_shape)
        if self.lambda_rad != 0.:
            t_sorted, _ = torch.sort(t, dim=-1)
            q = (torch.arange(n, device=xw.device, dtype=wdtype) + 0.5) / n_f
            rad_loss = 12. * (t_sorted - q).square().mean(dim=-1)

        # Spectral repulsion (replaces the 3-image kernel)
        # Move coeffs to the right device/dtype.
        coeffs_device = SpectralNeumannCoefficients(
            lam_0=self.coeffs.lam_0,
            lam_1=self.coeffs.lam_1,
            a_k=self.coeffs.a_k.to(device=xw.device, dtype=wdtype),
        )

        if x.ndim == 2:
            # Simple (N, d) case — call directly.
            rep_loss, _info = spectral_neumann_rep_loss(
                u, t,
                beta=self.beta,
                alpha=self.alpha,
                k_modes=self.k_modes,
                coeffs=coeffs_device,
                normalization_constant=self.normalization_constant,
                eps=self.eps,
            )
        else:
            # Batched case: iterate over leading dims.
            flat_u = u.reshape(-1, n, d)
            flat_t = t.reshape(-1, n)
            results = []
            for i in range(flat_u.shape[0]):
                rl, _ = spectral_neumann_rep_loss(
                    flat_u[i], flat_t[i],
                    beta=self.beta,
                    alpha=self.alpha,
                    k_modes=self.k_modes,
                    coeffs=coeffs_device,
                    normalization_constant=self.normalization_constant,
                    eps=self.eps,
                )
                results.append(rl)
            rep_loss = torch.stack(results).reshape(batch_shape)

        ang_loss = xw.new_zeros(batch_shape)  # spectral has no separate ang term

        return S_LossComponents(rep_loss, rep_loss, rad_loss, ang_loss, mom_pen)

    # ------------------------------------------------------------------
    # Calibration
    # ------------------------------------------------------------------

    def _calibrate(self, shape: tuple[int, int], reps: int, device, dtype):
        n, d = shape
        if n < 2 or d < 1 or reps < 2 or d != self.d:
            return

        all_rep, all_rad, all_mom = [], [], []

        with torch.no_grad():
            for _ in range(int(reps)):
                x_gauss = torch.randn(int(n), int(d), device=device, dtype=dtype)
                comp = self._compute(x_gauss)
                all_rep.append(float(comp.rep))
                all_rad.append(float(comp.rad))
                all_mom.append(float(comp.mom))

        reps_f = float(reps)
        bessel = reps_f / (reps_f - 1.)

        def _stats(vals):
            m = sum(vals) / reps_f
            v = (sum(x * x for x in vals) / reps_f - m * m) * bessel
            return m, v

        self.mean_rep, var_rep = _stats(all_rep)
        self.mean_rad, var_rad = _stats(all_rad)
        self.mean_mom, var_mom = _stats(all_mom)

        eps_cal = _eps_for_dtype(dtype, True)
        self.std_rep = math.sqrt(max(var_rep, eps_cal))
        self.std_rad = math.sqrt(max(var_rad, eps_cal))
        self.std_mom = math.sqrt(max(var_mom, eps_cal))

        sum_total, sum2_total = 0., 0.
        for rep, rad, mom in zip(all_rep, all_rad, all_mom):
            t_rep = (rep - self.mean_rep) / self.std_rep
            t_rad = self.lambda_rad * (rad - self.mean_rad) / self.std_rad
            t_mom = self.lambda_mom * (mom - self.mean_mom) / self.std_mom
            total = t_rep + t_rad + t_mom
            sum_total += total
            sum2_total += total * total

        mean_total = sum_total / reps_f
        var_total = (sum2_total / reps_f - mean_total * mean_total) * bessel
        self.std_total = math.sqrt(max(var_total, eps_cal))

    # ------------------------------------------------------------------
    # Public interface
    # ------------------------------------------------------------------

    def __call__(self, x: torch.Tensor) -> S_LossComponents:
        """Compute calibrated spectral wristband loss.

        Parameters
        ----------
        x : Tensor ``(..., N, d)``

        Returns
        -------
        S_LossComponents — (total, rep, rad, ang, mom)
        """
        comp = self._compute(x)

        norm_rep = (comp.rep - self.mean_rep) / self.std_rep
        norm_rad = (comp.rad - self.mean_rad) / self.std_rad
        norm_mom = (comp.mom - self.mean_mom) / self.std_mom
        norm_ang = comp.ang  # always 0

        total = (norm_rep + self.lambda_rad * norm_rad + self.lambda_mom * norm_mom) / self.std_total

        def _mean(t):
            return t.mean() if t.ndim > 0 else t

        return S_LossComponents(
            _mean(total), _mean(norm_rep), _mean(norm_rad), _mean(norm_ang), _mean(norm_mom)
        )
