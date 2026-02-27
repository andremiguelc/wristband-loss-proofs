# Wristband Loss — Spectral Decomposition Guide

This document is the companion to `docs/proof_guide.md` for the
`WristbandLossProofs/Spectral/` branch.  It covers three questions:

1. **What** the spectral decomposition is (mathematically).
2. **How** it connects to the existing kernel energy proofs.
3. **Where** it lives in the Lean files and which pieces are imported vs proved.

**Related documents:**
- Mathematical derivation (spherical harmonics, Bessel eigenvalues): `docs/posts/spectral/spectral_harmonics.md`
- Narrative overview (motivation, intuition, big picture): `docs/posts/spectral/spectral_narrative.md`
- Python implementation + complexity analysis: `docs/working/_spectral_python.md`

---

## 1. The Central Identity

The wristband repulsion energy is:

$$\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W, W')]$$

where $K = k_\text{ang} \cdot k_\text{rad}$ is the product kernel on the
wristband $S^{d-1}\times[0,1]$.

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

---

## 2. How the Spectral Branch Fits Into the Overall Proof

```
Step 1: Wristband Equivalence         Step 2: Kernel Minimization
  Phi_#Q = mu_0  <=>  Q = gamma        E(P) >= E(mu_0), equality iff P = mu_0
        |                                          |
        +------------------+------ ----------------+
                           |   (reused by spectral branch)
               Spectral Branch
               ---------------
               E(P) = Sum_{j,k} lam_j * a_k * |c_{jk}|^2   (identity)
               => spectralEnergy(P) >= spectralEnergy(mu_0)  (minimization)
               => spectralEnergy uniquely minimized at mu_0   (uniqueness)
               => Q ~ N(0,I) <-> spectral energy at minimum   (characterization)
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
| `SpectralImportedFacts.lean` | Mercer axiom + imported closure bridges + witness extractions | 3 axioms |
| `SpectralFoundations.lean` | Supporting lemmas, bridge consumption, spectral identity | No `sorry` |
| `SpectralMinimization.lean` | 3 main theorems | All bodies complete |

---

## 4. Python × Math × Lean Correspondence

For code, complexity analysis, and engineering decisions, see
`docs/working/_spectral_python.md`.

### 4.1 Spectral definitions

| Python | Math | Lean |
|--------|------|------|
| `cos_mat = cos(π * k_range * t)` (k=0 col is all 1's) | $f_0(t) = 1$; $f_k(t) = \cos(k\pi t)$ for $k \geq 1$ | `radialFeature k t` (`SpectralPrimitives.lean:45`) |
| `a_0 = sqrt(pi/beta)`; `a_k = 2*sqrt(pi/beta)*exp(...)` | $\tilde{a}_0 = a_0$; $\tilde{a}_k = a_{k-1}$ for $k \geq 1$ | `radialCoeff a0 a k` (`SpectralPrimitives.lean:55`) |
| $\ell=0$: constant; $\ell=1$: `sqrt(d)*u_m`. Eigenvalues via Bessel. | $\varphi_j : S^{d-1} \to \mathbb{R}$, orthonormal; $\lambda_j \geq 0$; $\varphi_0 \equiv 1$ | `mercerEigenfun` / `mercerEigenval` (`SpectralImportedFacts.lean`) |
| `c_0k = cos_mat.mean(0)`; `c_1k = sqrt(d)/N * u.T @ cos_mat` | $\hat{c}_{jk}(P) = \mathbb{E}_{(u,t)\sim P}[\varphi_j(u) \cdot f_k(t)]$ | `modeProj φ j k P` (`SpectralPrimitives.lean:74`) |
| `E_0 + E_1` (truncated to $\ell \leq 1$, $K = 6$) | $\mathcal{E}_\text{sp}(P) = \sum_{j,k} \lambda_j \tilde{a}_k \hat{c}_{jk}^2$ | `spectralEnergy φ λv a0 a P` (`SpectralPrimitives.lean:93`) |

### 4.2 Spectral theorems

| Math | Lean | Status |
|------|------|--------|
| $\mathcal{E}_\text{sp}(P) = \mathcal{E}(P)$ | `spectralEnergy_eq_kernelEnergy` (`SpectralFoundations.lean`) | Proved |
| $\mathcal{E}_\text{sp}(\mu_0) \leq \mathcal{E}_\text{sp}(P)$ | `spectralEnergy_minimized_at_uniform` (`SpectralMinimization.lean:38`) | Proved |
| $\mathcal{E}_\text{sp}(P) = \mathcal{E}_\text{sp}(\mu_0) \Rightarrow P = \mu_0$ | `spectralEnergy_minimizer_unique` (`SpectralMinimization.lean:61`) | Proved |
| $Q = \gamma \iff \mathcal{E}_\text{sp}(\Phi_\# Q) = \mathcal{E}_\text{sp}(\mu_0)$ | `spectralEnergy_wristband_gaussian_iff` (`SpectralMinimization.lean:98`) | Proved |

---

## 5. Definitions (`SpectralPrimitives.lean`)

| Name | Type / Formula | Line |
|------|----------------|------|
| `radialFeature k t` | $f_k(t)$: `1` if $k=0$, `cos(k pi t)` if $k \geq 1$ | 45 |
| `radialCoeff a0 a k` | $\tilde{a}_k$: `a0` if $k=0$, `a(k-1)` if $k \geq 1$ | 55 |
| `modeProj phi j k P` | $\hat{c}_{jk}(P) = \int \varphi_j(u)\,f_k(t)\;dP(u,t)$ | 74 |
| `spectralEnergy phi lv a0 a P` | $\sum'_j \sum'_k \lambda_j\tilde{a}_k(\hat{c}_{jk})^2$ | 93 |

**Design note.** The extended index $k = 0$ (constant) allows a single uniform
tsum covering both the constant-mode term $a_0$ and the cosine modes $a_k$.
The $(0,0)$ term is always $\lambda_0\tilde{a}_0 \cdot 1$ for any probability
measure.

---

## 6. Imported Facts

### `kernelAngChordal_mercerExpansion` (`SpectralImportedFacts.lean`)

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

### Closure bridge imports (`SpectralImportedFacts.lean`)

| Axiom | Role |
|------|------|
| `summable_neumannCosineCoeff_imported` | Radial cosine summability witness |
| `spectral_modeL1_factorized_bridge_imported` | Factorized mode-`L¹` majorant package for unconditional closure |

**Reused imported axioms (no change):**

| Axiom | File | Role |
|-------|------|------|
| `kernelRadNeumann_hasCosineExpansion` | `KernelImportedFacts.lean` | Radial eigenvalues $\tilde{a}_k$ |
| `kernelAngChordal_posSemiDef` | `KernelImportedFacts.lean` | Angular PSD (licenses $\lambda_j \geq 0$) |
| `kernelEnergy_minimizer_unique` | `KernelMinimization.lean` | Uniqueness at $\mu_0$ |
| `wristbandEquivalence` | `Equivalence.lean` | Gaussian $\leftrightarrow$ uniform |

---

## 7. Lemmas & Theorems

### 7.1 Lemmas (`SpectralFoundations.lean`)

| Lemma | Statement | Status |
|-------|-----------|--------|
| `mercerEigenval_nonneg` | $\lambda_j \geq 0$ | Proved |
| `mercerEigenfun_orthonormal` | $\int\varphi_j\varphi_{j'}\,d\sigma = \delta_{jj'}$ | Proved |
| `mercerEigenfun_zero_eq_one` | $\varphi_0 \equiv 1$ | Proved |
| `neumannRadialCoeff_nonneg` | $\tilde{a}_k \geq 0$ | Proved |
| `radialFeature_cosine_integral_zero` | $\int_0^1 f_{k+1}\,dt = 0$ | Proved |
| `radialFeature_constant_integral_one` | $\int_0^1 f_0\,dt = 1$ | Proved |
| `angularEigenfun_integral_zero` | $\int_{S^{d-1}}\varphi_j\,d\sigma = 0$ for $j > 0$ | Proved |
| `modeProj_zero_zero_eq_one` | $\hat{c}_{00}(P) = 1$ for any $P$ | Proved |
| `modeProj_vanishes_at_uniform` | $\hat{c}_{jk}(\mu_0) = 0$ for $(j,k)\neq(0,0)$ | Proved |
| `spectralEnergy_eq_kernelEnergy` | $\sum'_{jk}\lambda_j\tilde{a}_k\hat{c}_{jk}^2 = \mathcal{E}(P)$ | Proved |
| `spectralEnergy_nonneg_excess` | $\mathcal{E}_\text{sp}(\mu_0) \leq \mathcal{E}_\text{sp}(P)$ | Proved |

**Closure route used.** The unconditional theorem now closes through the
existing factorized wrapper
`spectralEnergy_eq_kernelEnergy_of_summable_neumannCosineCoeff_and_modeL1_majorant_factorized`,
fed by two imported bridge assumptions in `SpectralImportedFacts.lean`:
- `summable_neumannCosineCoeff_imported`
- `spectral_modeL1_factorized_bridge_imported`

### 7.2 Main theorems (`SpectralMinimization.lean`)

| Theorem | Statement | Status |
|---------|-----------|--------|
| `spectralEnergy_minimized_at_uniform` | $\mathcal{E}_\text{sp}(P) \geq \mathcal{E}_\text{sp}(\mu_0)$ | Proved (delegates to `spectralEnergy_nonneg_excess`) |
| `spectralEnergy_minimizer_unique` | $\mathcal{E}_\text{sp}(P) = \mathcal{E}_\text{sp}(\mu_0) \Rightarrow P = \mu_0$ | Proved (delegates to `kernelEnergy_minimizer_unique` via identity) |
| `spectralEnergy_wristband_gaussian_iff` | $Q = \gamma \iff \mathcal{E}_\text{sp}(\Phi_\#Q) = \mathcal{E}_\text{sp}(\mu_0)$ | Proved (delegates to `wristbandEquivalence`) |

---

## 8. Angular Eigenvalues

$$\lambda_\ell = e^{-c}\,\Gamma(d/2)\,(2/c)^{(d-2)/2}\, I_{\ell+(d-2)/2}(c), \quad c = 2\beta\alpha^2$$

Key properties: $\lambda_\ell \geq 0$ (Schoenberg); super-exponential decay
in $\ell$; $\lambda_1/\lambda_0 \approx c/d$ for $d \gg c$.

For $\ell=1$: $\varphi_{1,m}(u) = \sqrt{d}\,u_m$, so mode projections are
$\hat{c}_{1k} = \frac{\sqrt{d}}{N}U^\top\text{CosMatrix}$.

Full derivation: `docs/posts/spectral_harmonics.md`.

---

## 9. What's Not Formalized

| Python feature | Mathematical content | Notes |
|----------------|---------------------|-------|
| Truncation to $L \leq 1$, $K \leq 6$ | Error bounded by $\sum_{\ell>1}b_\ell + \sum_{k>6}a_k$ | Exponentially small for $\beta=8$ |
| Angular eigenvalue computation | $\lambda_\ell$ via Bessel functions | Precomputed at runtime, not in Lean |
| $\ell=2$ correction | $O(Nd^2K)$ cost, relevant for small $d$ | Not yet designed |
| Gradient analysis | Gradient of mode energy w.r.t. $x_i$ | Not formalized anywhere |

---

## 10. Mathlib Lookups

| Fact | Lean name | Status |
|------|-----------|--------|
| Swap $\int$ and $\sum'$ | `MeasureTheory.integral_tsum` | In Mathlib; needs measurability + dominated bound |
| Swap $\sum'\sum'$ | `tsum_comm'` | In Mathlib |
| Factor $\sum f\cdot\sum f = (\sum f)^2$ | `tsum_mul_left`, `tsum_mul_right` | In Mathlib |
| Factor $\int_{X\times Y}f(x)g(y) = \int f\cdot\int g$ | `MeasureTheory.integral_prod_mul` | In Mathlib (Fubini) |
| Mercer pointwise convergence | Not in Mathlib | **Axiom required** |

---

## 11. Axiom Validation Notes

These notes address potential pitfalls in the axioms and their interaction
with Lean's type system.

---

**Summability and `tsum`.** Lean's `tsum` returns 0 when the sum is not
summable.  The Mercer axiom (clause 3) asserts a `tsum` equality.  The
summability argument is: $\sum'_j \lambda_j |\varphi_j(u)|^2 \leq
k_\text{ang}(u,u) \leq 1$ (diagonal Mercer bound), so by Cauchy-Schwarz
the cross-term sum is also bounded.  A similar bound applies to the radial
series.  The conditional endpoints make this explicit through hypotheses,
and the unconditional identity is now closed by importing the summability and
factorized mode-`L¹` bridge assumptions in `SpectralImportedFacts.lean`.

---

**Product space decomposition.**  The spectral decomposition is stated for
the sphere.  The wristband is $S^{d-1} \times [0,1]$.  This works because
`wristbandKernelNeumann` is a product $k_\text{ang} \cdot k_\text{rad}$.
The decomposition is applied factor-by-factor:

```
K((u,t),(u',t')) = [Sum_j lam_j phi_j(u) phi_j(u')] * [Sum_k b_k f_k(t) f_k(t')]
                 = Sum_{j,k} (lam_j * b_k) [phi_j(u) f_k(t)] [phi_j(u') f_k(t')]
```

No Mercer theorem on the product space is needed.

---

**Interchange justification.**  The interchange $\int\int \sum = \sum \int\int$
requires a dominating function.  The axiom does not provide one explicitly.
The argument is: $|k_\text{ang}(u,v)| \leq k_\text{ang}(u,u) \leq 1$ and
partial sums are similarly bounded, giving a uniform dominating constant.
Since $P$ is a probability measure, the constant function 1 is integrable.
`MeasureTheory.integral_tsum` applies.

---

**Constant-mode identification.**  Clause (4) asserts $\varphi_0 \equiv 1$.
This is a consequence of the kernel being zonal (depending only on $u \cdot u'$):
$\int k(u\cdot v) \cdot 1\, d\sigma(v) = \lambda_0 \cdot 1$ by rotation
invariance.  The normalization $\varphi_0 = 1$ (not $1/\sqrt{\omega_d}$)
follows from $\sigma$ being a probability measure: $\int 1^2\,d\sigma = 1$.
Bundling this in the axiom avoids formalizing the zonality argument.

---

**Finiteness for non-negative excess.**  The proof of
`spectralEnergy_nonneg_excess` requires the spectral energy sum to be finite
(otherwise the inequality is vacuous).  Finiteness follows from
`spectralEnergy_eq_kernelEnergy`: the spectral energy equals the kernel
energy, which is bounded since the kernel is bounded.  This creates a
dependency: the non-negative excess proof depends on the identity.  The
conditional endpoint `spectralEnergy_nonneg_excess_of_summable` handles this
by requiring explicit summability of the mode series.

---

**Measure normalization consistency.**  The axiom has both
$\forall u,\, \varphi_0(u) = 1$ and $\int \varphi_0^2\,d\sigma = 1$.  These
are consistent because `sphereUniform d` is a probability measure
(`IsProbabilityMeasure`), so $\int 1^2\,d\sigma = 1$.  The Lean type
`Distribution (Sphere d)` enforces this.

---

**Basis non-uniqueness.**  Mercer eigenspaces can have multiplicity.  The
spectralEnergy does not depend on which basis is chosen: for any orthonormal
basis of the $\ell$-th eigenspace, $\sum_m \lambda_\ell (\hat{c}_{\ell m,k})^2$
equals the squared norm of the projection of $f_k$ onto the eigenspace, which
is basis-independent.

---

## 12. References

1. Mercer, J. (1909). "Functions of positive and negative type." *Phil. Trans. R.
   Soc. London A* 209, 415-446.
2. Schoenberg, I.J. (1942). "Positive definite functions on spheres." *Duke Math.
   J.* 9(1), 96-108.
3. Steinwart, I. & Christmann, A. (2008). *Support Vector Machines.* Springer.
   (Theorem 4.49: Mercer for compact metric spaces.)
4. Sun, H. & Chen, D. (2008). "Reproducing kernel Banach spaces with the $\ell^1$
   norm." Relevant for PD zonal kernels on $S^{d-1}$.
5. Jupp, P.E. (2008). "Data-driven Sobolev tests of uniformity on compact Riemannian
   manifolds." *Ann. Statist.* 36(3), 1246-1260.  (Mode-truncation argument.)
6. Evans, L.C. (2010). *Partial Differential Equations* (2nd ed.). AMS.
   (Heat equation eigenfunction expansions on bounded domains; Neumann cosine modes.)
7. Folland, G.B. (1999). *Real Analysis* (2nd ed.). Wiley.
   (Tonelli/Fubini foundations used in interchange/majorant arguments.)
