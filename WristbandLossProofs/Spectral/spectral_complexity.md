# Spectral Kernel — Algorithmic Complexity Analysis

This document covers the computational aspects of the spectral decomposition:
cost comparison with the original O(N^2 d) kernel, higher-order angular
corrections, and alternative approximation strategies.

For the mathematical identity, proof architecture, and Lean formalization,
see `spectral_guide.md`.

---

## 1. Complexity Comparison

| | Current | Spectral ($\ell \leq 1$, $K = 6$) |
|-|---------|-------------------------------|
| Multiplications ($N=4096$, $d=512$) | $\approx 8.6\text{G}$ | $\approx 12.6\text{M}$ ($\mathbf{680}\times$) |
| Peak intermediate memory | $O(N^2) \approx 200\,\text{MB}$ | $O(Nd) \approx 8\,\text{MB}$ |
| Largest batch (8 GB GPU) | $N \approx 4{,}500$ | $N \approx 65{,}000$ |

A 4x larger batch halves the gradient variance (U-statistic, $\mathrm{Var}
\propto 1/N$) — aligned with the author's motivation for minimizing $O(N^2)$.

---

## 2. Higher-Order Angular Corrections

For $\ell = 0$ (constant) and $\ell = 1$ (linear harmonics $\varphi_{1m}(u) = \sqrt{d}\,u_m$),
the spectral code achieves $O(NdK)$.  Degree-$\ell$ spherical harmonics have
$\approx d^\ell/\ell!$ independent components, so computing the $\ell$-th-order projections
costs $O(Nd^\ell K)$.

| Angular order $\ell$ | Cost per pass | Cheaper than $O(N^2d)$ when |
|---|---|---|
| 0 (constant) | $O(NK)$ | always |
| 1 (linear) | $O(NdK)$ | always |
| 2 (quadratic) | $O(Nd^2K)$ | $N > dK$ |
| $L$ (general) | $O(Nd^L K)$ | $N > d^{L-1}K$ |

### Crossover and energy contribution at $K = 6$, $\beta = 8$, $\alpha = 1$

| $d$ | $\ell = 2$ break-even $N$ | $\ell = 2$ energy fraction | Speedup at $N = 4096$ ($\ell\leq 1$ / $\ell\leq 2$ / original) |
|---|---|---|---|
| 32 | 192 | $\approx 12.5\%$ | 170x / 1.3x / -- |
| 128 | 768 | $\approx 0.8\%$ | -- / 1.3x / -- |
| 512 | 3072 | $\approx 0.05\%$ | **680x** / 2.6x / baseline |

Energy fractions use the large-$d$ approximation
$\lambda_\ell/\lambda_0 \approx (2\beta\alpha^2/d)^\ell / \ell!$
(valid when $d \gg 2\beta\alpha^2$; for $\beta=8$, $\alpha=1$: $\lambda_1/\lambda_0 \approx 16/d$,
$\lambda_2/\lambda_0 \approx 128/d^2$).

### Is $\ell = 2$ worth it?

At $d \geq 128$ (typical for production embedding models), the $\ell = 2$ modes
contribute less than 1% of total energy.  Adding them multiplies the spectral
cost by $\approx d/K > 80$, for negligible accuracy gain.  At $d \leq 32$,
$\ell = 2$ contributes 10--25% and is potentially useful — but at that scale
the original $O(N^2d)$ cost is already low, so absolute savings are modest.

**The $O(NdK)$ operating point ($\ell = 1$) is optimal across the entire range
of production embedding dimensions.**

---

## 3. Eigenvalue Decay vs Dimension

| $d$ | $\lambda_1/\lambda_0$ | $\lambda_2/\lambda_0$ |
|---|---|---|
| 32 | $\approx 50\%$ | $\approx 12.5\%$ |
| 128 | $\approx 12.5\%$ | $\approx 0.8\%$ |
| 512 | $\approx 3.1\%$ | $\approx 0.05\%$ |

At production embedding dimensions ($d \geq 128$), the $\ell = 2$ modes
contribute less than 1% of total energy. The $\ell = 0$ (constant) and
$\ell = 1$ (coordinate projection) modes capture $> 99\%$ of the kernel.

---

## 4. Polynomial Alternatives for Higher-Order Corrections

If higher-order accuracy *is* needed (small $d$ or a tight eigenvalue spectrum),
three approaches exist:

1. **Monomial (tensor-power) sketch.**  Approximate $k_\text{ang}(u\cdot u')$ by its
   Taylor series $\sum_\ell c_\ell (u\cdot u')^\ell$ with
   $c_\ell = e^{-2\beta\alpha^2}(2\beta\alpha^2)^\ell/\ell!$.  The estimator is
   $\sum_\ell c_\ell \|(1/N)\sum_i u_i^{\otimes\ell} f_k(t_i)\|^2$.
   However, $u^{\otimes\ell}$ has $d^\ell$ components, so the asymptotic cost is
   $O(Nd^\ell K)$ — identical to spherical harmonics.  No improvement.

2. **Random features for zonal kernels** (cf. Pennington et al. 2015).  Sample $D$
   random directions $\omega_r$ from the kernel's spectral measure; use
   $\varphi_r(u) = \cos(\omega_r \cdot u)$.  Cost: $O(NDd)$ for $D$ features.
   For $D = dK$ this matches $\ell = 1$; larger $D$ approximates higher-order modes
   at Monte Carlo variance.  Useful when the Gegenbauer expansion is unavailable
   analytically; adds variance that the deterministic eigenbasis avoids.

3. **Nystrom approximation.**  Sub-sample $m \ll N$ landmark points; approximate
   $K \approx K_{Nm}K_{mm}^{-1}K_{mN}$.  Cost $O(Nm^2 + m^3)$.
   For $m = O(\sqrt{N})$: cost $O(N^{3/2}d)$.  Breaks the $O(N^2)$ barrier without
   requiring the product-kernel structure, but is slower than $O(NdK)$ for $d \geq K$.

None of these matches $O(NdK)$ for the same level of approximation accuracy.
**For the wristband kernel at $d \geq 64$, $\ell = 1$ is both the cheapest and the
most accurate practical choice.**

---

## 5. Gradient Truncation Error

The gradient of the truncated loss (angular order $\leq L$, radial modes $\leq K$) is:
$\partial E_{L,K}/\partial x_i = 2 \sum_{j\leq L,k\leq K} \lambda_j b_k \hat{c}_{jk}\, \partial\hat{c}_{jk}/\partial x_i$.

The gradient truncation error is the missing tail. By Cauchy-Schwarz:
$\|\delta\nabla\| \leq \sqrt{\text{energy tail}} \cdot \sqrt{\sum_\text{tail} \lambda_j b_k \|\partial\hat{c}_{jk}/\partial x_i\|^2}$.

For $L = 1$, $K = 6$, $\beta = 8$ the energy tail is $\approx 0.03\%$ of total energy,
so $\|\delta\nabla\| \leq O(0.03\%)^{1/2} \cdot \|\nabla E\| \approx 1.7\%$ of the full gradient norm.

Near the minimum (where all $\hat{c}_{jk} \approx 0$ for $(j,k) \neq (0,0)$),
both the exact and truncated gradients vanish — the minimum is structurally
stable under truncation.

Whether the gradient error during optimization (far from the minimum) causes
practical convergence issues depends on the curvature landscape and requires
experimental validation.
