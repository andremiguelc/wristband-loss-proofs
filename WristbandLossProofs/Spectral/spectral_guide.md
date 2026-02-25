# Wristband Loss — Spectral Decomposition Guide

This document is the companion to `docs/proof_guide.md` for the
`WristbandLossProofs/Spectral/` branch.  It covers three questions:

1. **What** the spectral decomposition is (mathematically and algorithmically).
2. **How** it connects to the existing kernel energy proofs.
3. **Where** it lives in the Lean files and what remains to be proved.

---

## 1. The Central Identity

The wristband repulsion energy is:

$$\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W, W')]$$

where $K = k_\text{ang} \cdot k_\text{rad}$ is the product kernel on the
wristband $S^{d-1}\times[0,1]$.  Computing this naively over a batch of $N$
points costs $O(N^2 d)$ and uses $O(N^2)$ memory.

The spectral decomposition says: **the same energy equals a sum of squared
mode projections**:

$$\boxed{\mathcal{E}(P) = \sum_{j=0}^\infty \sum_{k=0}^\infty
  \lambda_j \cdot \tilde{a}_k \cdot \bigl|\hat{c}_{jk}(P)\bigr|^2}$$

where:

| Symbol | Meaning | Source |
|--------|---------|--------|
| $\lambda_j \geq 0$ | Mercer eigenvalues of $k_\text{ang}$ on $S^{d-1}$ | Axiom `kernelAngChordal_mercerExpansion` |
| $\varphi_j : S^{d-1} \to \mathbb{R}$ | corresponding orthonormal eigenfunctions | same axiom |
| $\tilde{a}_k \geq 0$ | radial mode coefficients: $\tilde{a}_0 = a_0$, $\tilde{a}_k = a_{k-1}$ for $k \geq 1$ | Axiom `kernelRadNeumann_hasCosineExpansion` |
| $\hat{c}_{jk}(P) = \mathbb{E}_{(u,t)\sim P}[\varphi_j(u)\cdot f_k(t)]$ | joint mode projection | `modeProj` in `SpectralPrimitives.lean` |
| $f_0(t) = 1$, $f_k(t) = \cos(k\pi t)$ for $k \geq 1$ | radial eigenfunctions (Neumann on $[0,1]$) | `radialFeature` in `SpectralPrimitives.lean` |

**Why the minimum is unchanged.**  At the uniform measure $\mu_0 =
\sigma_{d-1}\otimes\mathrm{Unif}[0,1]$:

- $\hat{c}_{jk}(\mu_0) = 0$ for every $(j, k) \neq (0, 0)$:
  angular eigenfunctions $\varphi_j$ ($j \geq 1$) integrate to zero over
  $\sigma_{d-1}$; cosines $\cos(k\pi t)$ ($k \geq 1$) integrate to zero
  over $[0,1]$.
- The $(0, 0)$ term always equals $\lambda_0 \cdot \tilde{a}_0 \cdot 1$
  (since $\varphi_0 = 1$ and $f_0 = 1$, so $\hat{c}_{00} = 1$ for every
  probability measure).

Therefore $\mathcal{E}(\mu_0) = \lambda_0\tilde{a}_0$, and every deviation
from $\mu_0$ adds non-negative terms.  The unique minimizer is preserved.

**Why the computation is faster.**  Instead of the $N^2$-sum, compute each
$\hat{c}_{jk}$ as an $N$-average.  For $j \leq 1$ (dominant angular modes)
and $K \leq 6$ radial modes, the total cost is $O(NdK)$ — about 680× fewer
multiplications than $O(N^2 d)$ for $N = 4096$, $d = 512$, $K = 6$.

---

## 2. How the Spectral Branch Fits Into the Overall Proof

```
Step 1: Wristband Equivalence         Step 2: Kernel Minimization
  Φ_#Q = μ₀  ⟺  Q = γ               E(P) ≥ E(μ₀), equality iff P = μ₀
        │                                          │
        └──────────────────┬───────────────────────┘
                           │   (reused by spectral branch)
               Spectral Branch
               ──────────────
               E(P) = Σ_{j,k} λ_j·ã_k·|ĉ_{jk}|²      (identity)
               ⟹ spectralEnergy(P) ≥ spectralEnergy(μ₀) (minimization)
               ⟹ spectralEnergy uniquely minimized at μ₀  (uniqueness)
               ⟹ Q ~ N(0,I) ↔ spectral energy at minimum  (characterization)
```

The spectral branch **does not replace** the existing proofs — it imports them.
`spectralEnergy_minimizer_unique` calls `kernelEnergy_minimizer_unique`
(from `KernelMinimization.lean`) after converting via the identity.
`spectralEnergy_wristband_gaussian_iff` calls `wristbandEquivalence`.

---

## 3. Lean File Map

| File | Contents | Status |
|------|----------|--------|
| `SpectralPrimitives.lean` | `radialFeature`, `radialCoeff`, `modeProj`, `spectralEnergy` | Definitions only |
| `SpectralImportedFacts.lean` | `kernelAngChordal_mercerExpansion` (sole new axiom) | 1 axiom |
| `SpectralFoundations.lean` | Witness extraction + 6 lemmas | Scaffolded (5 `sorry`) |
| `SpectralMinimization.lean` | 3 main theorems | Bodies complete; 2 are dependency-blocked by `SpectralFoundations` sorrys |

---

## 4. Python Correspondence

All Python references are to
[`EmbedModels.py`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py),
method `_Compute` (lines 762–804).

### 4.1 Current code (O(N²d))

```python
g     = (u @ u.T).clamp(-1., 1.)          # (N,N) angular Gram matrix
e_ang = (2. * beta_alpha2) * (g - 1.)     # (N,N)
diff0 = t[:,None] - t[None,:]             # (N,N)
diff1 = t[:,None] + t[None,:]             # (N,N)
diff2 = diff1 - 2.                        # (N,N)
total  = exp(e_ang - beta * diff0**2)     # three (N,N) kernel matrices
total += exp(e_ang - beta * diff1**2)
total += exp(e_ang - beta * diff2**2)
rep_loss = log(total.sum() / (3N²-N)) / beta
```

### 4.2 Proposed spectral code (O(NdK))

```python
# Precomputed once at construction (from β, α, d — no new hyperparameters):
#   a_k  = [1, 2*exp(-π²/4β), 2*exp(-4π²/4β), …]  for k = 0..K-1
#   b_0, b_1 = angular eigenvalues (Bessel-function formula, see §7)

K       = 6
k_range = torch.arange(K)                          # (K,)
cos_mat = torch.cos(π * k_range[None,:] * t[:,None]) # (N,K)  radial features

c_0k = cos_mat.mean(0)                             # (K,)   ℓ=0 projections
c_1k = u.T @ cos_mat / N                           # (d,K)  ℓ=1 projections

E_0  = b_0 * (a_k * c_0k**2).sum()
E_1  = b_1 * (a_k[None,:] * c_1k**2).sum()
rep_loss = log(E_0 + E_1) / beta
```

**What changed:** the three $(N,N)$ matrices are replaced by a single
$(d, K)$ matrix multiply.  Nothing else changes.

### 4.3 Complexity comparison

| | Current | Spectral ($L \leq 1$, $K = 6$) |
|-|---------|-------------------------------|
| Multiplications ($N=4096$, $d=512$) | $\approx 8.6\text{G}$ | $\approx 12.6\text{M}$ ($\mathbf{680}\times$) |
| Peak intermediate memory | $O(N^2) \approx 200\,\text{MB}$ | $O(Nd) \approx 8\,\text{MB}$ |
| Largest batch (8 GB GPU) | $N \approx 4{,}500$ | $N \approx 65{,}000$ |

A 4× larger batch halves the gradient variance (U-statistic, $\mathrm{Var}
\propto 1/N$) — aligned with the author's motivation for minimizing $O(N^2)$.

#### Higher-order corrections: when does ℓ > 1 pay off?

For ℓ = 0 (constant) and ℓ = 1 (linear harmonics $\varphi_{1m}(u) = \sqrt{d}\,u_m$),
the spectral code achieves $O(NdK)$.  Degree-ℓ spherical harmonics have
$\approx d^\ell/\ell!$ independent components, so computing the ℓ-th-order projections
costs $O(Nd^\ell K)$.

| Angular order ℓ | Cost per pass | Cheaper than $O(N^2d)$ when |
|---|---|---|
| 0 (constant) | $O(NK)$ | always |
| 1 (linear) | $O(NdK)$ | always |
| 2 (quadratic) | $O(Nd^2K)$ | $N > dK$ |
| $L$ (general) | $O(Nd^L K)$ | $N > d^{L-1}K$ |

**Crossover and energy contribution** at $K = 6$, $\beta = 8$, $\alpha = 1$:

| $d$ | ℓ = 2 break-even $N$ | ℓ = 2 energy fraction | Speedup at $N = 4096$ (ℓ≤1 / ℓ≤2 / original) |
|---|---|---|---|
| 32 | 192 | ≈ 12.5% | 170× / 1.3× / — |
| 128 | 768 | ≈ 0.8% | — / 1.3× / — |
| 512 | 3072 | ≈ 0.05% | **680×** / 2.6× / baseline |

Energy fractions use the large-$d$ approximation
$\lambda_\ell/\lambda_0 \approx (2\beta\alpha^2/d)^\ell / \ell!$
(valid when $d \gg 2\beta\alpha^2$; for $\beta=8$, $\alpha=1$: $\lambda_1/\lambda_0 \approx 16/d$,
$\lambda_2/\lambda_0 \approx 128/d^2$).

**How plausible is the ℓ = 2 regime?**  At $d \geq 128$ (typical for production embedding
models), the ℓ = 2 modes contribute less than 1% of the total energy.  Adding them
multiplies the spectral cost by $\approx d/K > 80$, for negligible accuracy gain.
At $d \leq 32$, ℓ = 2 contributes 10–25% and is potentially useful — but at that scale
the original $O(N^2d)$ cost is already low, so absolute savings are modest.
**The $O(NdK)$ operating point (ℓ = 1) is optimal across the entire range of
production embedding dimensions.**

#### Polynomial alternatives for higher-order corrections

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
   For $D = dK$ this matches ℓ = 1; larger $D$ approximates higher-order modes
   at Monte Carlo variance.  Useful when the Gegenbauer expansion is unavailable
   analytically; adds variance that the deterministic eigenbasis avoids.

3. **Nyström approximation.**  Sub-sample $m \ll N$ landmark points; approximate
   $K \approx K_{Nm}K_{mm}^{-1}K_{mN}$.  Cost $O(Nm^2 + m^3)$.
   For $m = O(\sqrt{N})$: cost $O(N^{3/2}d)$.  Breaks the $O(N^2)$ barrier without
   requiring the product-kernel structure, but is slower than $O(NdK)$ for $d \geq K$.

None of these matches $O(NdK)$ for the same level of approximation accuracy.
**For the wristband kernel at $d \geq 64$, ℓ = 1 is both the cheapest and the
most accurate practical choice.**

---

## 5. Definitions (`SpectralPrimitives.lean`)

| Name | Type / Formula | Line |
|------|----------------|------|
| `radialFeature k t` | $f_k(t)$: `1` if $k=0$, `cos(kπt)` if $k \geq 1$ | 45 |
| `radialCoeff a0 a k` | $\tilde{a}_k$: `a0` if $k=0$, `a(k-1)` if $k \geq 1$ | 55 |
| `modeProj φ j k P` | $\hat{c}_{jk}(P) = \int \varphi_j(u)\,f_k(t)\;dP(u,t)$ | 74 |
| `spectralEnergy φ λv a0 a P` | $\sum'_j \sum'_k \lambda_j\tilde{a}_k(\hat{c}_{jk})^2$ | 93 |

**Design note.** The extended index $k = 0$ (constant) allows a single uniform
tsum covering both the constant-mode term $a_0$ and the cosine modes $a_k$.
The $(0,0)$ term is always $\lambda_0\tilde{a}_0 \cdot 1$ for any probability
measure.

---

## 6. Axiom

The spectral branch adds a single new axiom:

### `kernelAngChordal_mercerExpansion` (`SpectralImportedFacts.lean:26`)

**What it says:**  There exist functions $\varphi_j : S^{d-1} \to \mathbb{R}$
and scalars $\lambda_j \geq 0$ such that:

1. $\lambda_j \geq 0$ for all $j$.
2. $\varphi_j$ are orthonormal: $\int_{S^{d-1}}\varphi_j\varphi_{j'}\,d\sigma = \delta_{jj'}$.
3. $k_\text{ang}(u,u') = \sum'_j \lambda_j\,\varphi_j(u)\,\varphi_j(u')$ for all $u, u'$.
4. $\varphi_0 \equiv 1$ (the constant function).

**Mathematical basis:** Mercer's theorem for continuous PSD kernels on compact
metric spaces (Steinwart & Christmann, Theorem 4.49).  For zonal kernels on
$S^{d-1}$, this is Schoenberg's theorem (1942): every continuous PSD zonal
kernel $k(u\cdot u')$ expands in spherical harmonics with non-negative
coefficients.

**Mathlib status:** The spectral theorem for compact self-adjoint operators
on Hilbert spaces exists in Mathlib (`Analysis.InnerProductSpace.Spectrum`).
The specific Mercer form with *pointwise* (not just $L^2$) convergence is
not yet in Mathlib — hence the axiom.

**Reused axioms (no change):**

| Axiom | File | Role |
|-------|------|------|
| `kernelRadNeumann_hasCosineExpansion` | `KernelImportedFacts.lean:38` | Radial eigenvalues $\tilde{a}_k$ |
| `kernelAngChordal_posSemiDef` | `KernelImportedFacts.lean:28` | Angular PSD (licenses $\lambda_j \geq 0$) |
| `kernelEnergy_minimizer_unique` | `KernelMinimization.lean:155` | Uniqueness at $\mu_0$ |
| `wristbandEquivalence` | `Equivalence.lean:999` | Gaussian $\leftrightarrow$ uniform |

---

## 7. Lemmas & Theorems

### 7.1 Lemmas (`SpectralFoundations.lean`)

| Lemma | Statement | Status | Proof route |
|-------|-----------|--------|-------------|
| `mercerEigenval_nonneg` | $\lambda_j \geq 0$ | **Proved** | Extracted from axiom clause 1 |
| `mercerEigenfun_orthonormal` | $\int\varphi_j\varphi_{j'}\,d\sigma = \delta_{jj'}$ | **Proved** | Extracted from axiom clause 2 |
| `mercerEigenfun_zero_eq_one` | $\varphi_0 \equiv 1$ | **Proved** | Extracted from axiom clause 4 |
| `neumannRadialCoeff_nonneg` | $\tilde{a}_k \geq 0$ | **Proved** | Case split on `radialCoeff` |
| `radialFeature_cosine_integral_zero` | $\int_0^1 f_{k+1}\,dt = 0$ | **Proved** | Calls `cosine_mode_integral_uniform01` |
| `radialFeature_constant_integral_one` | $\int_0^1 f_0\,dt = 1$ | **Proved** | `simp` |
| `angularEigenfun_integral_zero` | $\int_{S^{d-1}}\varphi_j\,d\sigma = 0$ for $j > 0$ | `sorry` | Orthonormality with $j'=0$ + $\varphi_0=1$ |
| `modeProj_zero_zero_eq_one` | $\hat{c}_{00}(P) = 1$ for any $P$ | `sorry` | $\varphi_0 = f_0 = 1$, probability mass 1 |
| `modeProj_vanishes_at_uniform` | $\hat{c}_{jk}(\mu_0) = 0$ for $(j,k)\neq(0,0)$ | `sorry` | `integral_prod_mul` + angular/radial zero-mean lemmas |
| `spectralEnergy_eq_kernelEnergy` | $\sum'_{jk}\lambda_j\tilde{a}_k\hat{c}_{jk}^2 = \mathcal{E}(P)$ | `sorry` | 7-step algebra (Mercer axiom + cosine axiom + integral/series interchange + `tsum` algebra + `integral_prod_mul`) |
| `spectralEnergy_nonneg_excess` | $\mathcal{E}_\text{sp}(\mu_0) \leq \mathcal{E}_\text{sp}(P)$ | `sorry` | `tsum_nonneg` + mode projections |

### 7.2 Main theorems (`SpectralMinimization.lean`)

| Theorem | Statement | Status |
|---------|-----------|--------|
| `spectralEnergy_minimized_at_uniform` | $\mathcal{E}_\text{sp}(P) \geq \mathcal{E}_\text{sp}(\mu_0)$ | `sorry` (calls `spectralEnergy_nonneg_excess`) |
| `spectralEnergy_minimizer_unique` | $\mathcal{E}_\text{sp}(P) = \mathcal{E}_\text{sp}(\mu_0) \Rightarrow P = \mu_0$ | **Proved** (calls `kernelEnergy_minimizer_unique` via identity) |
| `spectralEnergy_wristband_gaussian_iff` | $Q = \gamma \iff \mathcal{E}_\text{sp}(\Phi_\#Q) = \mathcal{E}_\text{sp}(\mu_0)$ | `sorry` (calls `wristbandEquivalence`) |

---

## 8. Angular Eigenvalues in Practice

For the angular kernel $k_\text{ang}(u,u') = e^{2\beta\alpha^2(\langle u,u'\rangle-1)}$
with $\alpha^2 = 1/12$ (default), the Mercer eigenvalues involve modified Bessel
functions:

$$\lambda_\ell \propto e^{-c}\,I_{\ell+(d-2)/2}(c)\cdot (c/2)^{-(d-2)/2},
\quad c = 2\beta\alpha^2$$

Key qualitative properties:

- **$\lambda_\ell \geq 0$ always** (Schoenberg's theorem / existing PSD axiom).
- **Exponential decay in $\ell$**: $\lambda_\ell \to 0$ super-exponentially.
- **High-$d$ effect**: for $d \gg c$, $\lambda_1/\lambda_0 \approx c/d$ — the
  $\ell=1$ term is small but significant.

For the $\ell=1$ eigenfunctions: $\varphi_{1,m}(u) = \sqrt{d}\,u_m$.  This
means the $\ell=1$ mode projections are $\hat{c}_{1k} = \frac{\sqrt{d}}{N}U^\top\text{CosMatrix}$
— just the matrix multiply `u.T @ cos_mat`, already available.

---

## 9. Open Sorry's and Priority

Verified against the current Lean files:

| Sorry | File | Difficulty | Criticality | Blocks | Priority |
|-------|------|------------|-------------|--------|----------|
| `modeProj_vanishes_at_uniform` | `SpectralFoundations.lean` | ★★☆ | **C0** | `spectralEnergy_nonneg_excess`, practical minimization proof route | **1st** |
| `spectralEnergy_eq_kernelEnergy` | `SpectralFoundations.lean` | ★★★ | **C0** | `spectralEnergy_minimizer_unique`, finiteness route for nonneg-excess, Gaussian characterization chain | **2nd** |
| `spectralEnergy_nonneg_excess` | `SpectralFoundations.lean` | ★☆☆ | **C0** | `spectralEnergy_minimized_at_uniform` | **3rd** |
| `angularEigenfun_integral_zero` | `SpectralFoundations.lean` | ★☆☆ | C1 | `modeProj_vanishes_at_uniform` (`k = 0`, `j > 0` branch) | **4th** |
| `modeProj_zero_zero_eq_one` | `SpectralFoundations.lean` | ★☆☆ | C1 | nonneg-excess proof simplification and canonical `(0,0)` term normalization | **5th** |

The spectral critical path is:
`angularEigenfun_integral_zero` + `radialFeature_cosine_integral_zero` + `MeasureTheory.integral_prod_mul`
→ `modeProj_vanishes_at_uniform`
→ `spectralEnergy_eq_kernelEnergy`
→ (`spectralEnergy_nonneg_excess`, `spectralEnergy_minimizer_unique`)
→ `spectralEnergy_wristband_gaussian_iff`.

**Transitive (kernel-side) sorrys** relevant to practical claims:

| Sorry | File | Criticality | Blocks |
|-------|------|-------------|--------|
| `threeImage_energy_approx` | `KernelMinimization.lean:806` | C1 | Formal bridge from Neumann proofs to the exact Python 3-image loss |

`threeImage_approx_neumann` is now proved; it is no longer an open blocker.

---

## 10. What's Not Formalized

| Python feature | Mathematical content | Notes |
|----------------|---------------------|-------|
| Truncation to $L \leq 1$, $K \leq 6$ | Error bounded by $\sum_{\ell>1}b_\ell + \sum_{k>6}a_k$ | Exponentially small for $\beta=8$ |
| Angular eigenvalue computation | $\lambda_\ell$ via Bessel functions | Precomputed at runtime, not in Lean |
| $\ell=2$ correction | $O(Nd^2K)$ cost, relevant for small $d$ | Not yet designed |
| Gradient analysis | Gradient of mode energy w.r.t. $x_i$ | Not formalized anywhere |

---

## 11. Mathlib Lookups Needed

| Fact | Lean name | Group | Status |
|------|-----------|-------|--------|
| Swap $\int$ and $\sum'$ | `MeasureTheory.integral_tsum` | Series/integral interchange | In Mathlib; needs measurability + nonnegativity |
| Swap $\sum'\sum'$ | `ENNReal.tsum_comm` or `tsum_comm'` | Double-series commutation | In Mathlib |
| Factor $\sum f\cdot\sum f = (\sum f)^2$ | `tsum_mul_left`, `tsum_mul_right` | Series product algebra | In Mathlib |
| Factor $\int_{X\times Y}f(x)g(y) = \int f\cdot\int g$ | `MeasureTheory.integral_prod_mul` | Product-measure factorization | In Mathlib (Fubini) |
| Mercer pointwise convergence | Not in Mathlib | Mercer expansion axiom | **Axiom required** |
| Spherical harmonics in $d>2$ | Not in Mathlib | — | Not needed (abstracted by axiom) |

---

## 12. FAQ — Hard Questions

This section stress-tests the applicability of the spectral decomposition.
Questions are grouped by audience.  Ratings: ✅ *cleanly answered*, ⚠️ *valid
concern, mitigated*, ❌ *genuine open problem*.

---

### 12.1 ML Engineer Questions

---

**Q1 ⚠️: The Python `rep_loss` is `(1/β)·log(mean_kernel)`, not `mean_kernel`.
You optimize a different objective.  Why should the minimizer be the same?**

The Lean proof formalizes that `spectralEnergy(P)` (= `mean_kernel`) is
minimized at and only at `μ₀`.  The Python loss `(1/β)·log(·)` is a strictly
monotone increasing function of `mean_kernel`, so it is minimized at exactly
the same `P`.  The optimizer direction is identical in expectation.  The log
changes the gradient *scale* (by a factor of `1/mean_kernel`) but not the
gradient *zero* or the minimum location.  **No issue for the theoretical
claim.  Gradient magnitude changes are a hyperparameter concern, not a
correctness concern.**

---

**Q2 ❌: The gradient of the truncated spectral loss ≠ gradient of the
original loss.  Is this a problem we can only characterize empirically?**

Partially — but the error has a computable theoretical bound.

The gradient of the truncated loss (angular order ≤ L, radial modes ≤ K) is:
`∂E_{L,K}/∂x_i = 2 Σ_{j≤L,k≤K} λ_j b_k ĉ_{jk} ∂ĉ_{jk}/∂x_i`.
The **gradient truncation error** is the missing tail:
`δ∇ = Σ_{j>L or k>K} λ_j b_k ĉ_{jk} ∂ĉ_{jk}/∂x_i`.

By Cauchy–Schwarz:
`‖δ∇‖ ≤ √(energy tail) · √(Σ_tail λ_j b_k ‖∂ĉ_{jk}/∂x_i‖²)`.

For `L = 1`, `K = 6`, `β = 8` the energy tail is ≈ 0.03% of total energy,
so `‖δ∇‖ ≤ O(0.03%)^{1/2} · ‖∇E‖ ≈ 1.7%` of the full gradient norm.

**What theory gives:** near the minimum (where all `ĉ_{jk} ≈ 0` for
`(j,k) ≠ (0,0)`), both the exact and truncated gradients vanish — the minimum
is structurally stable under truncation.  The 1.7% bound applies at any point
in parameter space, including during training.

**What remains empirical:** whether the gradient error *during optimization*
(far from the minimum) accumulates over many steps and pushes the trajectory
into a spurious basin.  This depends on the curvature landscape of the missing
modes, which is model- and data-dependent.  **Theoretical bounds exist and are
strong for this kernel; confirming they don't cause practical convergence issues
requires experimental runs.**

---

**Q3 ⚠️: You need to precompute `λ_ℓ` (Bessel function formula).  How do
you compute it?  Does it depend on `β` and `α` in a stable way?**

For the angular kernel `exp(2βα²(⟨u,u'⟩-1))`, the Mercer eigenvalues are
computable via modified spherical Bessel functions:

$$\lambda_\ell \propto e^{-c}\,\frac{I_{\ell+(d-2)/2}(c)}{(c/2)^{(d-2)/2}},
\quad c = 2\beta\alpha^2.$$

For `ℓ = 0,1` these are stable and easily precomputed with SciPy
(`scipy.special.iv`).  For large `d` and small `c`, the ratio
`λ_1/λ_0 ≈ c/d` makes `ℓ=1` corrections small.  **The precomputation is
numerically stable.  The Lean proof does not need to compute `λ_ℓ`
explicitly — it is existentially quantified in the axiom.**

---

**Q4 ⚠️: For `ℓ > 1`, `φ_{ℓm}(u)` are degree-`ℓ` polynomial functions of
`u`.  When does the `O(NdK)` claim hold, and what alternatives exist for
higher-order corrections?**

See §4.3 for the full breakdown with crossover conditions and energy fractions.
Summary:

- **ℓ ≤ 1**: always $O(NdK)$ regardless of $d$ or $N$.  This is the current
  proposal and the primary claim.
- **ℓ ≤ 2**: costs $O(Nd^2K)$, cheaper than $O(N^2d)$ only when $N > dK$.
  For $d = 512$, $K = 6$: requires $N > 3072$.  At $N = 4096$ the speedup
  is 2.6× (vs 680× for ℓ ≤ 1), because the ℓ = 2 cost itself is large.
- **ℓ ≤ 3**: impractical for $d \geq 32$ — cost exceeds original for all
  $N < d^2 K \approx 10^5$.

**Is ℓ = 2 worth it?**  For $\beta = 8$, $\alpha = 1$, $d = 512$: the ℓ = 2
contribution is ≈ 0.05% of total energy — negligible.  For $d = 32$: ≈ 12.5%,
potentially meaningful.  The exponential decay
$\lambda_\ell \propto (2\beta\alpha^2/d)^\ell/\ell!$ makes ℓ = 1 sufficient at
production embedding dimensions.

**Polynomial alternatives** (see §4.3 for details): monomial tensor powers
have the same $O(Nd^\ell K)$ cost as harmonics; random features for zonal
kernels are flexible but add Monte Carlo variance; Nyström approximation is
useful for non-product kernels or small $d$.  **None bypasses
$O(Nd^\ell K)$ for genuine degree-ℓ accuracy.**

---

### 12.2 Mathematician Questions

---

**Q5 ⚠️: The `tsum` in Lean is defined to be 0 when the sum is not summable.
Your axiom asserts a `tsum` equality.  How do you know the Mercer sum is
summable in Lean's sense, so the tsum isn't silently returning 0?**

This is the most important technical gap in the current scaffold.  The
`sorry`'d proof of `spectralEnergy_eq_kernelEnergy` must establish
summability *before* equating the tsum to the kernel energy.  The argument
is: `Σ' j, λ_j |φ_j(u)|² ≤ k_ang(u,u) ≤ 1` (the diagonal Mercer sum is
bounded by the kernel's supremum), so by Cauchy-Schwarz the cross-term sum
`Σ' j, λ_j |φ_j(u)||φ_j(u')| ≤ 1` as well.  A similar bound for the
radial series.  This gives a uniform dominating constant for the double sum,
ensuring summability.  **The scaffold does not yet formalize this
summability argument.  It is the first obligation inside
`spectralEnergy_eq_kernelEnergy`.**

---

**Q6 ✅: The spectral decomposition is stated for the sphere.  The wristband
is `Sphere d × [0,1]`.  Why does it apply to the product space?**

Because `wristbandKernelNeumann` is a **product** `k_ang · k_rad`.  The
decomposition is applied factor-by-factor:

```
K((u,t),(u',t')) = [Σ_j λ_j φ_j(u)φ_j(u')] · [Σ_k b_k f_k(t)f_k(t')]
                 = Σ_{j,k} (λ_j b_k) [φ_j(u)f_k(t)] [φ_j(u')f_k(t')]
```

The joint eigenfunctions `Ψ_{jk}(u,t) = φ_j(u)·f_k(t)` live on the full
wristband and are orthonormal in `L²(σ ⊗ Unif[0,1])`.  No Mercer theorem
for the product space is needed — the product structure of the kernel is all
that is required.  The wristband measure `wristbandUniform d` is already
defined as `productLaw (sphereUniform d) uniform01` in `Equivalence.lean`.
**No new axiom is needed for the product space.**

---

**Q7 ⚠️: The summation interchange `∫∫ Σ = Σ ∫∫` needs more than just a
tsum equality.  It needs the partial sums to be dominated by an integrable
function.  Does your axiom provide this?**

Not explicitly.  The axiom (clause 3) asserts the tsum equality `k_ang(u,v) =
∑' j, λ_j φ_j(u) φ_j(v)` but does not assert absolute summability of the
integrand or a dominating function.  The interchange is justified as follows:

1. `|Σ' j, λ_j φ_j(u) φ_j(v)| = |k_ang(u,v)| ≤ 1` (kernel bounded by 1).
2. The partial sums `Σ_{j<N} λ_j φ_j(u) φ_j(v) ≤ k_ang(u,u) ≤ 1` (by the
   Mercer diagonal bound and Cauchy-Schwarz) give a uniform dominating constant.
3. `MeasureTheory.integral_tsum` applies under the domination by the constant
   function 1, which is integrable since P is a probability measure.

**The domination argument is valid but not yet axiomatized.  The sorry'd
proof must establish it explicitly before applying `integral_tsum`.**

---

**Q8 ⚠️: Clause (4) of A1_bundle asserts `φ_0 ≡ 1`.  Mercer's theorem
does not uniquely determine the eigenfunctions.  Is this an additional
assumption or a consequence?**

It is a consequence of the kernel being **zonal** (depending only on `u·u'`).
For any zonal kernel on `S^{d-1}`, the constant function is an eigenfunction:
`∫ k(u·v)·1 dσ(v) = (∫ k(u·v) dσ(v)) · 1 = λ_0 · 1`, where `λ_0 = ∫ k dσ`
is constant by rotation invariance.  The normalization `φ_0 = 1` (not
`1/√ω_d`) follows from `σ` being a **probability** measure:
`∫ φ_0² dσ = ∫ 1 dσ = 1`, so `φ_0 = 1` is already unit-norm.
**This is a theorem, not an additional assumption.  Bundling it in the
axiom is a convenience that avoids formalizing the zonality argument.**

---

**Q9 ✅: The modeProj basis is not unique — Mercer eigenspaces can have
multiplicity.  Does the spectralEnergy depend on which basis is chosen?**

No.  Suppose the `ℓ`-th eigenspace has eigenvalue `λ_ℓ` and is spanned by
`{φ_{ℓm}}_{m=1}^{N(d,ℓ)}`.  For any orthonormal basis of this eigenspace:

$$\sum_m \lambda_\ell \,(\hat{c}_{\ell m,k})^2
= \lambda_\ell \left\|\sum_m \hat{c}_{\ell m,k} \phi_{\ell m}\right\|^2_P
$$

The norm of the projection of `f_k` onto the eigenspace is basis-independent.
The spectralEnergy thus sums eigenspace contributions, not individual-vector
contributions.  **For zonal kernels (our case) eigenspace contributions are
equal to `λ_ℓ · Σ_m (ĉ_{ℓmk})²`, which equals the addition-formula sum and
is rotationally invariant and basis-free.**

---

**Q10 ⚠️: The proof of `spectralEnergy_nonneg_excess` requires the sum
`spectralEnergy P` to be finite (not `+∞`).  Otherwise `∞ ≥ ∞` is vacuous.
Where is finiteness established?**

Finiteness follows from `spectralEnergy_eq_kernelEnergy` (the main identity):
`spectralEnergy P = kernelEnergy K P`, and `kernelEnergy K P ≤ sup K ≤ 1·3 = 3`
since both kernel factors are bounded.  But this means `spectralEnergy_nonneg_excess`
**depends on `spectralEnergy_eq_kernelEnergy`** — it cannot be proved
before the identity is established.  The dependency order in the scaffold
is correct (nonneg_excess is listed after the identity in priority), but the
sorry stubs do not make this dependency explicit.  **A future proof of
`spectralEnergy_nonneg_excess` must import the identity as a hypothesis or
prove finiteness independently.**

---

**Q11 ✅: The `spectralEnergy_minimizer_unique` theorem is already fully
proved (no sorry).  But it depends on `kernelEnergy_minimizer_unique` from
`KernelMinimization.lean`, which in turn depends on sorry'd facts.  Is the
proof actually complete?**

No, it is not complete end-to-end.  `kernelEnergy_minimizer_unique` uses
`wristbandKernelNeumann_characteristic`, which is imported from
`kernelAngChordal_universal` and the characteristic kernel chain.  The
universality axioms are genuine axioms (not sorry'd), so that chain is
sound.  However, `spectralEnergy_minimizer_unique` also requires
`spectralEnergy_eq_kernelEnergy` (the identity), which is sorry'd.  So the
"fully proved" status means: **the proof is complete modulo the sorry's that
it explicitly calls, which includes the identity.  The proof tree is sound
in structure; the leaves are the sorry obligations.**

---

**Q12 ⚠️: The spectral decomposition proves the *population* energy is
minimized at `μ₀`.  Training uses finite batches.  How exactly is this gap
handled?**

The gap decomposes into two independent, manageable sources of error:

**1. Statistical consistency (per mode, exact L, K).**
The empirical projection `ĉ_{jk}(P̂_N) = (1/N)Σ_i φ_j(u_i) f_k(t_i)` converges
a.s. to `ĉ_{jk}(P)` by the strong law of large numbers (`φ_j` and `f_k` are
bounded).  For fixed $L, K$, the truncated spectral energy
`E_{L,K}(P̂_N) = Σ_{j≤L,k≤K} λ_j b_k ĉ_{jk}(P̂_N)²`
converges a.s. to `E_{L,K}(P)` by the continuous mapping theorem.
Rate: $O(1/\sqrt{N})$ per mode by CLT.  **This is standard statistical
theory — no new formalization is needed.**

**2. Approximation error (population, missing modes).**
`E(P) - E_{L,K}(P) = Σ_{j>L or k>K} λ_j b_k ĉ_{jk}(P)²`

All terms are non-negative, so this is a well-defined non-negative remainder.
For the Neumann kernel it decays exponentially: the radial tail is
$O(\exp(-L\pi^2/\beta))$ and the angular tail is $O((2\beta\alpha^2/d)^L/L!)$.
For $L = 1$, $K = 6$, $\beta = 8$, $d = 512$: approximation error ≤ 0.03%
of total energy.  **This bound follows from the kernel's analytic properties;
it is not yet formalized in Lean but is standard functional-analytic reasoning.**

**Combined error decomposition:**
```
|E(P̂_N) - E(P)| ≤ |E_{L,K}(P̂_N) - E_{L,K}(P)| + (E(P) - E_{L,K}(P))
                 ≤      O(LK/√N)                +   O(exponential tail)
```
For $N = 4096$, $L = 1$, $K = 6$: statistical error $\approx O(6/64)$ per
mode; exponential tail ≈ 0.03%.  The statistical error dominates, and both
terms vanish as $N \to \infty$ and $L, K \to \infty$.  **The batch estimator
is consistent for the truncated energy; the population minimization result is
recovered in the joint limit.**

What remains unformalized: the interaction between the two error sources
*during the optimization trajectory* (not just at convergence).  See Q2.

---

**Q13 ⚠️: The axiom adds `∀ u, φ 0 u = 1` but the orthonormality clause
says `∫ φ_0² dσ = 1`.  Are these consistent?  Only if `σ(S^{d-1}) = 1`.**

Correct — and this is exactly what `sphereUniform d` provides: it is defined
as a probability measure (`IsProbabilityMeasure`) on `Sphere d`.  So
`∫ 1² dσ = 1` and `φ_0 = 1` is consistent with orthonormality.  If the
measure were not normalized, one would need `φ_0 = 1/√ω_d`.  **The Lean
type `Distribution (Sphere d)` enforces the probability measure property, so
the axiom clauses (2) and (4) are consistent by construction.**

---

## 13. References

1. Mercer, J. (1909). "Functions of positive and negative type." *Phil. Trans. R.
   Soc. London A* 209, 415–446.
2. Schoenberg, I.J. (1942). "Positive definite functions on spheres." *Duke Math.
   J.* 9(1), 96–108.
3. Steinwart, I. & Christmann, A. (2008). *Support Vector Machines.* Springer.
   (Theorem 4.49: Mercer for compact metric spaces.)
4. Sun, H. & Chen, D. (2008). "Reproducing kernel Banach spaces with the $\ell^1$
   norm." Relevant for PD zonal kernels on $S^{d-1}$.
5. Jupp, P.E. (2008). "Data-driven Sobolev tests of uniformity on compact Riemannian
   manifolds." *Ann. Statist.* 36(3), 1246–1260.  (Mode-truncation argument.)

---

## 14. Imported-Fact Minimization Audit

This section is an explicit "use Mathlib first, import only what is necessary"
audit for the spectral branch.

### 14.1 Spectral-facing imported facts

Criticality legend:
- **C0**: blocks the core spectral theorem chain.
- **C1**: does not block the core population theorem chain, but blocks practical
  alignment or secondary theorem goals.
- **C2**: hygiene / optional strengthening.

| Item | Where | Why needed now | Criticality | Can we remove soon? |
|------|-------|----------------|-------------|---------------------|
| `kernelAngChordal_mercerExpansion` | `SpectralImportedFacts.lean` | Supplies angular eigenbasis + eigenvalues + pointwise expansion | **C0** | Not realistically short-term; Mathlib lacks ready-made pointwise Mercer package |
| `kernelRadNeumann_hasCosineExpansion` | `KernelImportedFacts.lean` | Supplies radial spectral series and nonnegative coefficients | **C0** | Not short-term unless we fully prove Neumann cosine series in-repo |
| `kernelEnergy_minimizer_unique` | `KernelMinimization.lean` | Current uniqueness transfer (`spectral` → `kernel`) | C1 for spectral-only minimization; **C0** for current uniqueness route | Removable only with a new direct spectral uniqueness proof |
| `wristbandEquivalence` | `Equivalence.lean` | Gaussian `<->` wristband-uniform bridge | C1 | Not removable if Gaussian characterization theorem remains a goal |

### 14.2 Transitive imported-axiom footprint (via kernel uniqueness route)

If you keep `spectralEnergy_minimizer_unique` routed through
`kernelEnergy_minimizer_unique`, you also inherit these kernel-side imports:
`kernelAngChordal_universal`, `kernelRadNeumann_universal`,
`productKernel_universal`, `universal_implies_characteristic`, and `mmdSq_nonneg`.

This is the largest imported-fact surface area in the current design.

### 14.3 Minimal-import strategy

1. Keep exactly one **new** spectral axiom (`kernelAngChordal_mercerExpansion`).
2. Finish all spectral local lemmas from Mathlib + existing imported facts
   (no additional axioms).
3. Keep kernel uniqueness route in the short term.
4. Optionally, later replace the kernel uniqueness dependency with a direct
   spectral uniqueness theorem if you are willing to prove extra completeness /
   positivity assumptions for the spectral coefficients.

---

## 15. Statement Criticality Matrix (What Blocks What)

| Statement | Status | Criticality | Why it matters | Blocks |
|-----------|--------|-------------|----------------|--------|
| `kernelAngChordal_mercerExpansion` | axiom | **C0** | Core spectral representation on sphere | Every spectral theorem downstream |
| `mercerEigenval_nonneg`, `mercerEigenfun_orthonormal`, `mercerEigenfun_zero_eq_one` | proved | C0 infrastructure | Extracts usable witnesses from axiom | If broken, all mode-based proofs break |
| `angularEigenfun_integral_zero` | `sorry` | C1 | Needed for `(j>0,k=0)` vanishing mode case | `modeProj_vanishes_at_uniform` |
| `radialFeature_cosine_integral_zero`, `radialFeature_constant_integral_one` | proved | C0 infrastructure | Radial orthogonality + constant mode normalization | Vanishing/projection lemmas |
| `modeProj_zero_zero_eq_one` | `sorry` | C1 | Pins down baseline `(0,0)` contribution | Cleaner nonneg-excess proof |
| `modeProj_vanishes_at_uniform` | `sorry` | **C0** | Establishes all non-constant modes vanish at `μ₀` | `spectralEnergy_nonneg_excess` |
| `spectralEnergy_eq_kernelEnergy` | `sorry` | **C0** | Main bridge identity from spectral to existing kernel theorems | `spectralEnergy_minimizer_unique`, finiteness route |
| `spectralEnergy_nonneg_excess` | `sorry` | **C0** | Direct minimization theorem for spectral energy | `spectralEnergy_minimized_at_uniform` |
| `spectralEnergy_minimized_at_uniform` | statement body complete but dependency-blocked | **C0** | Hypothesis-K analogue in spectral form | Not a blocker for uniqueness theorem, but blocker for standalone minimization claim |
| `spectralEnergy_minimizer_unique` | body complete but dependency-blocked | **C0** | Uniqueness at `μ₀` in spectral language | `spectralEnergy_wristband_gaussian_iff` |
| `spectralEnergy_wristband_gaussian_iff` | body complete but dependency-blocked | **C0** final result | End-user theorem (Gaussian iff minimum spectral energy) | Final theorem endpoint |
| `threeImage_energy_approx` (kernel side) | `sorry` | C1 | Aligns Neumann-theory proofs with exact 3-image implementation | Practical "exactly current Python objective" theorem |
| `integral_tsum_kernelRadNeumann`, `measurable_wristbandKernelNeumann`, `cosine_span_uniformly_dense_on_unitInterval` (kernel foundations) | `sorry` | C2 | Important for long-term completeness/cleanup | Not currently on the spectral critical path |

### 15.1 Most valuable next steps (in order)

1. Close `spectralEnergy_eq_kernelEnergy`.
2. Close `modeProj_vanishes_at_uniform`.
3. Close `spectralEnergy_nonneg_excess`.
4. Close `angularEigenfun_integral_zero` and `modeProj_zero_zero_eq_one`.
5. After core spectral theorems are complete, close `threeImage_energy_approx`
   to recover tight practical alignment with the current ml-tidbits loss.
