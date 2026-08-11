# Wristband Loss — Lean 4 Formalization Guide

This document maps the Lean 4 formalization to the mathematics behind
[`C_WristbandGaussianLoss`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

**Central claim (population setting):**

$$\Phi_\# Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

The wristband map produces uniform output **if and only if** the input is
standard Gaussian. The kernel energy minimization and spectral decomposition
results characterize the minimum of the repulsion term. Joining the two into a
statement about the whole loss is not formalized; §6 says what remains.

---

## 1. File Map

The `Axioms` column counts `axiom` declarations in the file, and `Sorry` counts deferred
proofs. §5 lists every axiom and §6 every `sorry`.

| File | Contents | Axioms | Sorry |
|------|----------|--------|-------|
| `EquivalencePrimitives.lean` | Types (`Vec`, `VecNZ`, `Sphere`, `Wristband`, `Distribution`), sphere uniform measure, chi-square distribution and CDF, probability integral transform | — | — |
| `EquivalenceImportedFacts.lean` | Gaussian density and polar decomposition, from the literature | 3 | — |
| `EquivalenceFoundations.lean` | `gaussianNZ`, rotation invariance, polar direction uniform, polar independence, polar radius chi-square | — | — |
| `Equivalence.lean` | Wristband map, equivalence theorem (forward + backward + iff) | — | — |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic/universal predicates | — | — |
| `KernelImportedFacts.lean` | PSD, universality, characteristic, cosine series, from the literature | 9 | — |
| `KernelFoundations.lean` | Kernel properties, symmetry, measurability, characteristic proofs | — | 3 |
| `KernelMinimization.lean` | Energy minimization + uniqueness; Neumann-to-3-image approximation | — | 1 |
| `Spectral/SpectralPrimitives.lean` | `radialFeature`, `radialCoeff`, `modeProj`, `spectralEnergy` | — | — |
| `Spectral/SpectralImportedFacts.lean` | Mercer decomposition, addition theorem, degree mass | 5 | — |
| `Spectral/SpectralFoundations.lean` | Spectral–kernel energy identity, mode projections, nonneg excess | — | — |
| `Spectral/SpectralMinimization.lean` | Spectral minimization, uniqueness, Gaussian characterization | — | — |
| `Spectral/SpectralTruncation.lean` | Closed-form truncation error bounds in `L` and `K` | — | — |
| `Poisson/PoissonPrimitives.lean` | Poisson weights, dot-product kernel, Rademacher draw, samplers | — | — |
| `Poisson/PoissonImportedFacts.lean` | Random-feature law for dot-product kernels; uniform minimizes their energy | 2 | — |
| `Poisson/PoissonFoundations.lean` | Maclaurin expansion, the sampler and its unbiasedness | — | — |
| `Poisson/PoissonMinimization.lean` | Sampled energy transfer, minimization, uniqueness, Gaussian iff | — | — |
| `Poisson/PoissonEstimator.lean` | Unbiasedness of the realized `D`-draw energy, feature form of the energy | — | — |
| `Poisson/PoissonVariance.lean` | The `1/D` variance identity, Chebyshev, and the feature-count bounds | — | — |
| `Poisson/PoissonSecondMoment.lean` | Certified lower bound on the gap from the second moment; separation of two estimates | — | — |

Declaration-level contents for the Poisson branch are in
[`docs/posts/poisson/poisson_guide.md`](posts/poisson/poisson_guide.md), and for the
spectral branch in [`docs/posts/spectral/spectral_guide.md`](posts/spectral/spectral_guide.md).

**Build status.** The equivalence, kernel and Poisson modules compile against the pinned
Mathlib (v4.28.0). `Spectral/SpectralFoundations.lean` does not, and
`Spectral/SpectralMinimization.lean` and `Spectral/SpectralTruncation.lean` fail with it
because they import it. The errors are API-shaped, not `sorry`s; see
[`spectral_guide.md`](posts/spectral/spectral_guide.md) §3. Because the root module imports
only `Equivalence`, a plain `lake build` does not surface this — build each branch by module
name.

---

## 2. Dependency Graph

Nodes in brackets are not formalized; §6 lists them.

```
  Wristband Equivalence                  Kernel Energy Minimization
    (Equivalence.lean)                     (KernelMinimization.lean)
    Φ_#Q = μ₀  ⟺  Q = γ                  E(P) ≥ E(μ₀), = iff P = μ₀
            │                       ┌──────────────┴──────────────┐
            │                       ↓                             ↓
            │              Spectral Identity              Poisson Mixture
            │            (SpectralFoundations)          (PoissonFoundations)
            │               E_spec = E_kernel        k_ang = E_m[⟪u,u'⟫^m]
            │                       ↓                             ↓
            │             Spectral Minimization        Poisson Minimization
            │           Gaussian ↔ spectral minimum   minimizer survives sampling
            │                                                     ↓
            │                                              Poisson Estimator
            │                                          the drawn kernel is unbiased
            ↓
  [ Main Correctness Theorem: L_rep uniquely minimized at Q = γ ]
            ↓
  [ Auxiliary Terms Preserve Minimizer ]
```

The spectral and Poisson branches both hang off `KernelMinimization`, and they are
independent of each other. The spectral branch enumerates the angular basis and bounds the
error of truncating it; the Poisson branch samples the same kernel instead, so no basis is
enumerated. Nothing in `Poisson/` depends on `Spectral/`, and nothing in the kernel or
spectral modules depends on `Poisson/`. The Poisson import chain is in
[`poisson_guide.md`](posts/poisson/poisson_guide.md) §2.

---

## 3. Main Theorems

### 3.1 Wristband Equivalence

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

| Direction | Lean | File | Proof idea |
|-----------|------|------|------------|
| Forward LHS $\Rightarrow$ RHS | `wristbandEquivalence_forward` | `Equivalence.lean` | Reverse PIT + spherical law reconstruction |
| Backward RHS $\Rightarrow$ LHS | `wristbandEquivalence_backward` | `Equivalence.lean` | Gaussian polar decomposition + probability integral transform |
| Iff | `wristbandEquivalence` | `Equivalence.lean` | Combines forward + backward |

Fully proven (sorry-free). The $d \ge 2$ guard is needed because $S^0 = \{-1,+1\}$ is discrete.

### 3.2 Kernel Energy Minimization

For the Neumann kernel $K_N$ with $\beta > 0$, $\alpha > 0$, $d \ge 2$:

$$\mathcal{E}(P) \;\ge\; \mathcal{E}(\mu_0), \qquad \text{with equality iff } P = \mu_0.$$

| Theorem | Lean | File |
|---------|------|------|
| Minimization | `kernelEnergy_minimized_at_uniform` | `KernelMinimization.lean` |
| Uniqueness | `kernelEnergy_minimizer_unique` | `KernelMinimization.lean` |

Proven via the MMD pathway: (1) $K_N$ is PSD $\Rightarrow$ $\mathrm{MMD}^2 \ge 0$; (2) constant potential $\Rightarrow$ $\mathcal{E}(P) - \mathcal{E}(\mu_0) = \mathrm{MMD}^2$; (3) $K_N$ is characteristic $\Rightarrow$ equality iff $P = \mu_0$.

### 3.3 Neumann-to-3-Image Approximation

The 3-image radial kernel keeps only the $n \in \{-1,0,1\}$ terms from the
infinite Neumann reflection series. The truncation error is $O(e^{-\beta})$.

| Theorem | Lean | File | Status |
|---------|------|------|--------|
| Pointwise: $\lvert k_{\mathrm{3img}} - k_N \rvert \le C(\beta)$ | `threeImage_approx_neumann` | `KernelMinimization.lean` | Proven |
| Energy: $\lvert \mathcal{E}_{\mathrm{3img}} - \mathcal{E}_N \rvert \le C(\beta)$ | `threeImage_energy_approx` | `KernelMinimization.lean` | `sorry` |

$C(\beta) = 2(e^{-\beta} + e^{-4\beta})/(1 - e^{-4\beta})$, so the leading order is
$e^{-\beta}$, not $e^{-4\beta}$. This bounds the pointwise kernel error, not the potential
oscillation.

### 3.4 Spectral Decomposition

Decomposes the kernel energy into a doubly-indexed sum of nonneg mode
contributions $\lambda_j \cdot a_k \cdot |\pi_{j,k}(P)|^2$.

| Theorem | Lean | File |
|---------|------|------|
| Spectral–kernel identity | `spectralEnergy_eq_kernelEnergy` | `SpectralFoundations.lean` |
| Minimization | `spectralEnergy_minimized_at_uniform` | `SpectralMinimization.lean` |
| Uniqueness | `spectralEnergy_minimizer_unique` | `SpectralMinimization.lean` |
| Gaussian characterization | `spectralEnergy_wristband_gaussian_iff` | `SpectralMinimization.lean` |

All sorry-free. Depends on the kernel and spectral axioms, and on no `sorry`: none of the
four deferred lemmas of §6 is on any path used here.

Closed-form truncation error bounds in the angular degree $L$ and the radial mode count $K$
are in `SpectralTruncation.lean`; see [`spectral_guide.md`](posts/spectral/spectral_guide.md) §4.3.

### 3.5 Poisson Mode Sampling

The angular kernel is a Poisson mixture over powers of $\langle u, u'\rangle$. An unbiased
sampler of that mixture *is* the kernel pointwise, so the minimization results transfer by
rewriting.

| Theorem | Lean | File |
|---------|------|------|
| Maclaurin expansion | `kernelAngChordal_maclaurinExpansion` | `PoissonFoundations.lean` |
| Sampler unbiasedness | `poissonAngularSampler_unbiased` | `PoissonFoundations.lean` |
| Energy transfer | `sampledEnergy_eq_kernelEnergy` | `PoissonMinimization.lean` |
| Uniqueness | `sampledEnergy_minimizer_unique` | `PoissonMinimization.lean` |
| Gaussian characterization | `sampledEnergy_wristband_gaussian_iff` | `PoissonMinimization.lean` |
| Unbiasedness of the realized energy | `realizedEnergy_unbiased` | `PoissonEstimator.lean` |
| Variance falls as $1/D$ | `realizedEnergy_variance` | `PoissonVariance.lean` |
| Feature count from Chebyshev | `featureCount_suffices` | `PoissonVariance.lean` |
| Gap bounded below by the second moment | `angularGap_ge_secondMomentGap_of_uniform` | `PoissonSecondMoment.lean` |

Sorry-free, and no `sorryAx` on any path. Per-theorem axiom use is tabulated in
[`poisson_guide.md`](posts/poisson/poisson_guide.md) §7.

---

## 4. Python-to-Lean Correspondence

All Python references are to
[`EmbedModels.py`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

### 4.1 Types

All in `EquivalencePrimitives.lean`.

| Math | Python | Lean |
|------|--------|------|
| $\mathbb{R}^d$ | tensors of shape `(..., N, D)` | `Vec d` = `EuclideanSpace ℝ (Fin d)` |
| $\mathbb{R}^d \setminus \{0\}$ | `clamp_min(eps)` guards | `VecNZ d` = `{z : Vec d // z ≠ 0}` |
| $S^{d-1}$ | `u = x * rsqrt(s)` | `Sphere d` = `Metric.sphere 0 1` |
| $[0, 1]$ | `clamp(eps, 1-eps)` | `UnitInterval` = `Set.Icc 0 1` |
| $S^{d-1} \times [0,1]$ | `(u, t)` pair | `Wristband d` = `Sphere d × UnitInterval` |

### 4.2 Wristband Map

| Python | Math | Lean | File |
|--------|------|------|------|
| `s = xw.square().sum(-1).clamp_min(eps)` | $s(x) = \lVert x \rVert^2$ | `radiusSq` | `EquivalencePrimitives.lean` |
| `u = xw * rsqrt(s)[..., :, None]` | $u(x) = x / \lVert x \rVert$ | `direction` | `EquivalencePrimitives.lean` |
| `t = gammainc(d/2, s/2).clamp(eps, 1-eps)` | $t(x) = F_{\chi^2_d}(\lVert x \rVert^2)$ | `chiSqCDFToUnit` | `EquivalencePrimitives.lean` |
| `(u, t)` used downstream | $\Phi(z) = (u(z),\, t(z))$ | `wristbandMap` | `Equivalence.lean` |

The Python `gammainc(d/2, s/2)` is the regularized lower incomplete gamma function,
which equals the chi-square CDF: $\texttt{gammainc}(d/2, s/2) = F_{\chi^2_d}(s)$.

### 4.3 Chi-Square Distribution & CDF

All in `EquivalencePrimitives.lean`.

| Math | Lean |
|------|------|
| $\chi^2_d = \mathrm{Gamma}(d/2, 1/2)$ | `chiSqMeasureR d` |
| Law of $\lVert Z\rVert^2$ on $\mathbb{R}_{\ge 0}$ | `chiSqRadiusLaw d` |
| $F_{\chi^2_d}$ continuous ($d \ge 1$) | `chiSqCDFToUnit_isContinuousCDF` |
| $F_{\chi^2_d}$ strictly increasing ($d \ge 1$) | `chiSqCDFToUnit_isStrictlyIncreasingCDF` |

### 4.4 Probability Integral Transform

All in `EquivalencePrimitives.lean`.

| Statement | Lean |
|-----------|------|
| $X \sim \mu$, $F_\mu$ continuous $\Rightarrow$ $F(X) \sim \mathrm{Unif}[0,1]$ | `probabilityIntegralTransform` |
| $F(X) \sim \mathrm{Unif}[0,1]$ + $F$ strictly increasing $\Rightarrow$ $X \sim \mu$ | `probabilityIntegralTransform_reverse` |

### 4.5 Distributions & Pushforward

| Math | Lean | File |
|------|------|------|
| Probability measure (total mass 1) | `Distribution α` = `ProbabilityMeasure α` | `EquivalencePrimitives.lean` |
| $f_\# Q(B) = Q(f^{-1}(B))$ | `pushforward f Q hf` | `EquivalencePrimitives.lean` |
| $P_Q = \Phi_\# Q$ | `wristbandLaw d Q` | `Equivalence.lean` |
| $\mu_0 = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$ | `wristbandUniform d` | `EquivalencePrimitives.lean` |

### 4.6 Kernel Definitions

All in `KernelPrimitives.lean`.

| Python | Math | Lean |
|--------|------|------|
| `g = (u @ u.T).clamp(-1, 1)` | $\langle u, u' \rangle$ | `sphereInner` |
| `exp(2·β·α²·(g - 1))` | $\exp\!\big(2\beta\alpha^2(\langle u,u'\rangle - 1)\big)$ | `kernelAngChordal` |
| `exp(-β·diff²)` for 3 reflected diffs | $\sum_{j \in \{0,1,2\}} e^{-\beta \cdot \delta_j^2}$ | `kernelRad3Image` |
| — (infinite series) | $\sum_{n \in \mathbb{Z}} e^{-\beta(t - t' - 2n)^2}$ | `kernelRadNeumann` |
| angular × radial | $K(w, w') = k_{\mathrm{ang}} \cdot k_{\mathrm{rad}}$ | `wristbandKernel` / `wristbandKernelNeumann` |
| `total / (3n² - n)` | $\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W,W')]$ | `kernelEnergy` |

The angular factor is equivalent to a chordal RBF: $\exp(-\beta\alpha^2 \lVert u - u'\rVert^2)$,
since $\lVert u - u'\rVert^2 = 2(1 - \langle u, u'\rangle)$.

---

## 5. Literature Axioms

These are well-known results stated as Lean `axiom`s (accepted without proof)
because they are not yet available in Mathlib.

**Total: 19** — 3 equivalence, 9 kernel, 5 spectral, 2 Poisson. To regenerate the list:

```bash
grep -rnE "^(private )?axiom [A-Za-z_]" WristbandLossProofs/
```

Two parts of that pattern are load-bearing. The `private ` alternative is required, because
`gaussianFull_witness` is a private axiom and a plain `^axiom` pattern misses it. The
trailing `[A-Za-z_]` is required, because prose lines beginning "axioms …" appear in module
comments and otherwise count as declarations.

Several results that appear as axioms in older revisions of this guide have since been
derived; each subsection below names them.

### 5.1 Gaussian density and polar decomposition (`EquivalenceImportedFacts.lean`)

Each axiom transcribes one theorem of Muirhead (1982).

| Axiom | Math | Source |
|-------|------|--------|
| `gaussianFull_witness` (private) | The standard isotropic Gaussian on `Vec d` exists and has the usual density | Thm 1.2.9, at $\mu = 0$, $\Sigma = I_d$ |
| `spherical_polar_decomposition` | Any spherical law splits as direction $\times$ radius, independent, direction uniform | Thm 1.5.6 |
| `gaussianFull_normSq_chiSq` | $\lVert Z\rVert^2 \sim \chi^2_d$ for $Z \sim \mathcal{N}(0,I_d)$ | Thm 1.4.1(a) |

`gaussianNZ`, `gaussianPolar_direction_uniform`, `gaussianPolar_radius_chiSq`,
`gaussianPolar_independent`, `sphereUniform_rotationInvariant` and
`sphereUniform_isProbability` were **axioms and are not any more** — they are derived in
`EquivalenceFoundations.lean` and `EquivalencePrimitives.lean`, with their signatures
preserved so downstream call sites did not change.

### 5.2 Kernel theory (`KernelImportedFacts.lean`)

| Axiom | What it says |
|-------|-------------|
| `kernelAngChordal_posSemiDef` | Chordal RBF on $S^{d-1}$ is PSD |
| `gaussian_periodization_cosine_series_period_two` | Periodized Gaussian has a cosine series of period 2 |
| `productKernel_posSemiDef_imported` | Product of PSD kernels is PSD |
| `kernelAngChordal_universal` | Chordal RBF is universal |
| `kernelRadNeumann_universal` | Neumann kernel is universal |
| `productKernel_universal_compact_imported` | Product of universal kernels on compacta is universal |
| `universal_implies_characteristic` | Universal $\Rightarrow$ characteristic |
| `orthogonal_group_transitive_on_sphere` | $O(d)$ acts transitively on $S^{d-1}$ |
| `mmdSq_nonneg` | $\mathrm{MMD}^2 \ge 0$ for PSD kernels |

`kernelRadNeumann_posSemiDef`, `neumannPotential_constant` and
`kernelRadNeumann_hasCosineExpansion` were **axioms and are not any more** — they are
theorems in `KernelFoundations.lean`.

### 5.3 Spectral theory (`SpectralImportedFacts.lean`)

| Axiom | What it says |
|-------|-------------|
| `kernelAngChordal_zonalHarmonicExpansion_ge3` | Zonal harmonic expansion of the angular kernel, $d \ge 3$ |
| `kernelAngChordal_mercerExpansion` | Mercer decomposition of angular kernel into eigenfunctions/eigenvalues |
| `mercerEigenfun_addition_theorem` | Addition theorem for the Mercer eigenfunctions |
| `mercerDegreeMass_total_eq_one` | The degree masses sum to one |
| `mercer_modeProjSqSum_per_degree_le_mass` | Per-degree mode projections are bounded by the degree mass |

`summable_neumannCosineCoeff`, `spectral_modeL1_factorized_bridge` and
`neumannCosineCoeff_le_gaussianBound` are theorems in `SpectralFoundations.lean`, not
axioms.

### 5.4 Poisson mode sampling (`PoissonImportedFacts.lean`)

| Axiom | What it says | Source |
|-------|-------------|--------|
| `randomMaclaurin_law_exists` | A dot-product kernel with non-negative summable Maclaurin coefficients is the expected product of two random Maclaurin features | Kar & Karnick (2012) |
| `dotProductKernel_energy_minimized_at_uniform` | The uniform measure minimizes the energy of a dot-product kernel with non-negative Maclaurin coefficients | Schoenberg (1942), Björck (1956) |

Both attributions come from recollection, and neither is checked against the source. The
axiom docstrings in `PoissonImportedFacts.lean` state what is open in each.

---

## 6. Proof Status

### Deferred proofs

These lemmas use `sorry` (Lean keyword for a deferred proof). All are in the kernel branch.
To regenerate: `grep -rn "sorry$" WristbandLossProofs/`.

| File | Lemma | Nature |
|------|-------|--------|
| `KernelFoundations.lean` | `measurable_wristbandKernelNeumann` | Measurability (routine) |
| `KernelFoundations.lean` | `integral_tsum_kernelRadNeumann` | Fubini for tsum (routine) |
| `KernelFoundations.lean` | `cosine_span_uniformly_dense_on_unitInterval` | Density of cosine span (Fourier / Stone-Weierstrass) |
| `KernelMinimization.lean` | `threeImage_energy_approx` | Neumann-to-3-image energy bound |

No other declaration in the repository references any of them, so the spectral and Poisson
branches are not blocked by them. `#print axioms` reports no `sorryAx` in either branch.

### Not yet formalized

| Python feature | Reference | Notes |
|----------------|-----------|-------|
| Angular-only auxiliary loss | angular loss block | Separate from joint kernel |
| Radial quantile penalty (Cramer-von Mises) | `_RadialLoss` | 1D Wasserstein on sorted $t$ |
| Moment penalties (`w2`, `kl`, `jeff`) | moment penalty block | $W_2^2$ to $\mathcal{N}(0,I)$ |
| Z-score calibration | final aggregation block | Affine rescaling (preserves minimizers) |
| Geodesic angular branch | geodesic option | Only chordal branch formalized |
| `per_point` reduction | default reduction mode | Only `global` branch matches population energy |
| The logarithm | `(1/β) log Ê` | The energy estimate is unbiased; its logarithm is not |
| The sampler's variance | — | `PoissonVariance.lean` bounds the feature count given a variance bound, but no theorem bounds the variance itself |

Two results remain open. The main correctness theorem combines the equivalence and
minimization results through monotonicity of $\log$. The auxiliary-term result shows each
additional penalty is $\ge 0$ and vanishes at the Gaussian, so the unique minimizer
survives.

---

## 7. References

Sources of the axioms of §5:

1. R.J. Muirhead. *Aspects of Multivariate Statistical Theory.* Wiley, 1982. (§5.1)
2. I. Steinwart, A. Christmann. *Support Vector Machines.* Springer, 2008. (§5.2)
3. B.K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Scholkopf, G.R.G. Lanckriet. "Hilbert space embeddings and metrics on probability measures." *JMLR* 11:1517-1561, 2010. (§5.2)
4. K. Atkinson, W. Han. *Spherical Harmonics and Approximations on the Unit Sphere.* Springer, 2012. (§5.3)
5. P. Kar, H. Karnick. "Random Feature Maps for Dot Product Kernels." *AISTATS* 2012, *PMLR* 22:583-591. (§5.4)
6. I.J. Schoenberg. "Positive definite functions on spheres." *Duke Math. J.* 9:96-108, 1942. (§5.4)
7. G. Björck. "Distributions of positive mass, which maximize a certain generalized energy integral." *Ark. Mat.* 3:255-269, 1956. (§5.4)

Background:

8. K.T. Fang, S. Kotz, K.W. Ng. *Symmetric Multivariate and Related Distributions.* Chapman & Hall, 1990.
9. G. Casella, R.L. Berger. *Statistical Inference.* 2nd ed., Duxbury, 2002.
10. A. Berlinet, C. Thomas-Agnan. *Reproducing Kernel Hilbert Spaces in Probability and Statistics.* Springer, 2004.
11. R.J. Serfling. *Approximation Theorems of Mathematical Statistics.* Wiley, 1980.
