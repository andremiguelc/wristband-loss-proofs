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
| `SpectralMinimization.lean` | 3 main theorems | 1 fully proved, 2 `sorry` |

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
| `modeProj_vanishes_at_uniform` | $\hat{c}_{jk}(\mu_0) = 0$ for $(j,k)\neq(0,0)$ | `sorry` | Fubini (D1) + B1/B2 |
| `spectralEnergy_eq_kernelEnergy` | $\sum'_{jk}\lambda_j\tilde{a}_k\hat{c}_{jk}^2 = \mathcal{E}(P)$ | `sorry` | 7-step algebra (A1 + cosine axiom + C1/C2/C3 + D1) |
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

| Sorry | Difficulty | Mathlib lemma needed | Priority |
|-------|------------|---------------------|----------|
| `modeProj_vanishes_at_uniform` | ★★☆ | `MeasureTheory.integral_prod_mul` (D1) | **1st** |
| `spectralEnergy_eq_kernelEnergy` | ★★★ | C1 (`integral_tsum`) + C2 (`tsum_comm'`) + D1 | **2nd** |
| `spectralEnergy_nonneg_excess` | ★☆☆ | `tsum_nonneg` + previous two | **3rd** |
| `angularEigenfun_integral_zero` | ★☆☆ | `simp` rewrite of orthonormality | **4th** |
| `modeProj_zero_zero_eq_one` | ★☆☆ | `integral_const` on probability measure | **5th** |
| `spectralEnergy_wristband_gaussian_iff` | ★☆☆ | Follows from all above + `wristbandEquivalence` | **6th** |

The critical path is: D1 → `modeProj_vanishes_at_uniform` → C1/C2/C3 →
`spectralEnergy_eq_kernelEnergy` → all theorems.

**Pre-existing sorry's in the kernel branch** that also block the spectral
branch (via `kernelEnergy_minimizer_unique`):

| Sorry | File | Nature |
|-------|------|--------|
| `threeImage_approx_neumann` | `KernelMinimization.lean:666` | Gaussian tail bound |
| `threeImage_energy_approx` | `KernelMinimization.lean:806` | Consequence of above |

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
| Swap $\int$ and $\sum'$ | `MeasureTheory.integral_tsum` | C1 | In Mathlib; needs measurability + nonnegativity |
| Swap $\sum'\sum'$ | `ENNReal.tsum_comm` or `tsum_comm'` | C2 | In Mathlib |
| Factor $\sum f\cdot\sum f = (\sum f)^2$ | `tsum_mul_left`, `tsum_mul_right` | C3 | In Mathlib |
| Factor $\int_{X\times Y}f(x)g(y) = \int f\cdot\int g$ | `MeasureTheory.integral_prod_mul` | D1 | In Mathlib (Fubini) |
| Mercer pointwise convergence | Not in Mathlib | A1 | **Axiom required** |
| Spherical harmonics in $d>2$ | Not in Mathlib | — | Not needed (abstracted by axiom) |

---

## 12. References

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
