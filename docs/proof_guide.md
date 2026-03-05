# Wristband Loss — Lean 4 Formalization Guide

This document maps the Lean 4 formalization to the mathematics behind
[`C_WristbandGaussianLoss`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

**Central claim (population setting):**

$$\Phi_\# Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

The wristband map produces uniform output **if and only if** the input is
standard Gaussian. Combined with the kernel energy minimization and spectral
decomposition results, this implies the wristband repulsion loss has a
**unique minimizer** at the Gaussian.

---

## 1. File Map

| File | Contents | Status |
|------|----------|--------|
| `EquivalenceFoundations.lean` | Types, chi-square distribution, CDF, probability integral transform | Fully proven |
| `EquivalenceImportedFacts.lean` | Gaussian polar decomposition (axioms from literature) | 5 axioms |
| `Equivalence.lean` | Wristband map, equivalence theorem (forward + backward + iff) | Fully proven |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic/universal predicates | Definitions only |
| `KernelImportedFacts.lean` | PSD, universality, constant-potential axioms (from literature) | 11 axioms |
| `KernelFoundations.lean` | Kernel properties, symmetry, measurability, characteristic proofs | Mostly proven (3 `sorry`) |
| `KernelMinimization.lean` | Energy minimization + uniqueness; Neumann-to-3-image approximation | Proven; 1 `sorry` in energy approximation |
| `Spectral/SpectralPrimitives.lean` | `radialFeature`, `radialCoeff`, `modeProj`, `spectralEnergy` | Definitions only |
| `Spectral/SpectralImportedFacts.lean` | Mercer decomposition, summability, L¹ factorization (axioms) | 3 axioms |
| `Spectral/SpectralFoundations.lean` | Spectral–kernel energy identity, mode projections, nonneg excess | Fully proven |
| `Spectral/SpectralMinimization.lean` | Spectral minimization, uniqueness, Gaussian characterization | Fully proven |

---

## 2. Dependency Graph

```
Wristband Equivalence              Kernel Energy Minimization
  (Equivalence.lean)                 (KernelMinimization.lean)
  Φ_#Q = μ₀  ⟺  Q = γ              E(P) ≥ E(μ₀), = iff P = μ₀
         \                              /       \
          \                            /    Spectral Identity
           ↘                          ↙     (SpectralFoundations.lean)
       Main Correctness Theorem         E_spec = E_kernel
       L_rep uniquely minimized            ↓
       at Q = γ  [not yet formal]    Spectral Minimization
                |                    (SpectralMinimization.lean)
                ↓                    Gaussian ↔ spectral minimum
       Auxiliary Terms Preserve
       Minimizer [not yet formal]
```

---

## 3. Main Theorems

### 3.1 Wristband Equivalence

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

| Direction | Lean | File | Proof idea |
|-----------|------|------|------------|
| Forward ($\Rightarrow$) | `wristbandEquivalence_forward` | `Equivalence.lean:515` | Gaussian polar decomposition + probability integral transform |
| Backward ($\Leftarrow$) | `wristbandEquivalence_backward` | `Equivalence.lean:695` | Reverse PIT + spherical law reconstruction |
| Iff | `wristbandEquivalence` | `Equivalence.lean:999` | Combines forward + backward |

Fully proven (sorry-free). The $d \ge 2$ guard is needed because $S^0 = \{-1,+1\}$ is discrete.

### 3.2 Kernel Energy Minimization

For the Neumann kernel $K_N$ with $\beta > 0$, $\alpha > 0$, $d \ge 2$:

$$\mathcal{E}(P) \;\ge\; \mathcal{E}(\mu_0), \qquad \text{with equality iff } P = \mu_0.$$

| Theorem | Lean | File |
|---------|------|------|
| Minimization | `kernelEnergy_minimized_at_uniform` | `KernelMinimization.lean:133` |
| Uniqueness | `kernelEnergy_minimizer_unique` | `KernelMinimization.lean:155` |

Proven via the MMD pathway: (1) $K_N$ is PSD $\Rightarrow$ $\mathrm{MMD}^2 \ge 0$; (2) constant potential $\Rightarrow$ $\mathcal{E}(P) - \mathcal{E}(\mu_0) = \mathrm{MMD}^2$; (3) $K_N$ is characteristic $\Rightarrow$ equality iff $P = \mu_0$.

### 3.3 Neumann-to-3-Image Approximation

The 3-image radial kernel keeps only the $n \in \{-1,0,1\}$ terms from the
infinite Neumann reflection series. The truncation error is $O(e^{-\beta})$.

| Theorem | Lean | File | Status |
|---------|------|------|--------|
| Pointwise: $\lvert k_{\mathrm{3img}} - k_N \rvert \le C(\beta)$ | `threeImage_approx_neumann` | `KernelMinimization.lean:666` | Proven |
| Energy: $\lvert \mathcal{E}_{\mathrm{3img}} - \mathcal{E}_N \rvert \le C(\beta)$ | `threeImage_energy_approx` | `KernelMinimization.lean:806` | `sorry` |

### 3.4 Spectral Decomposition

Decomposes the kernel energy into a doubly-indexed sum of nonneg mode
contributions $\lambda_j \cdot a_k \cdot |\pi_{j,k}(P)|^2$.

| Theorem | Lean | File |
|---------|------|------|
| Spectral–kernel identity | `spectralEnergy_eq_kernelEnergy` | `SpectralFoundations.lean:2203` |
| Minimization | `spectralEnergy_minimized_at_uniform` | `SpectralMinimization.lean:38` |
| Uniqueness | `spectralEnergy_minimizer_unique` | `SpectralMinimization.lean:61` |
| Gaussian characterization | `spectralEnergy_wristband_gaussian_iff` | `SpectralMinimization.lean:98` |

All sorry-free in spectral files. Depends transitively on kernel and spectral axioms.

---

## 4. Python-to-Lean Correspondence

All Python references are to
[`EmbedModels.py`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

### 4.1 Types

| Math | Python | Lean | File |
|------|--------|------|------|
| $\mathbb{R}^d$ | tensors of shape `(..., N, D)` | `Vec d` = `EuclideanSpace ℝ (Fin d)` | `EquivalenceFoundations.lean:24` |
| $\mathbb{R}^d \setminus \{0\}$ | `clamp_min(eps)` guards | `VecNZ d` = `{z : Vec d // z ≠ 0}` | `EquivalenceFoundations.lean:32` |
| $S^{d-1}$ | `u = x * rsqrt(s)` | `Sphere d` = `Metric.sphere 0 1` | `EquivalenceFoundations.lean:28` |
| $[0, 1]$ | `clamp(eps, 1-eps)` | `UnitInterval` = `Set.Icc 0 1` | `EquivalenceFoundations.lean:36` |
| $S^{d-1} \times [0,1]$ | `(u, t)` pair | `Wristband d` = `Sphere d × UnitInterval` | `EquivalenceFoundations.lean:40` |

### 4.2 Wristband Map

| Python | Math | Lean | File |
|--------|------|------|------|
| `s = xw.square().sum(-1).clamp_min(eps)` | $s(x) = \lVert x \rVert^2$ | `radiusSq` | `EquivalenceFoundations.lean:103` |
| `u = xw * rsqrt(s)[..., :, None]` | $u(x) = x / \lVert x \rVert$ | `direction` | `EquivalenceFoundations.lean:114` |
| `t = gammainc(d/2, s/2).clamp(eps, 1-eps)` | $t(x) = F_{\chi^2_d}(\lVert x \rVert^2)$ | `chiSqCDFToUnit` | `EquivalenceFoundations.lean:451` |
| `(u, t)` used downstream | $\Phi(z) = (u(z),\, t(z))$ | `wristbandMap` | `Equivalence.lean:14` |

The Python `gammainc(d/2, s/2)` is the regularized lower incomplete gamma function,
which equals the chi-square CDF: $\texttt{gammainc}(d/2, s/2) = F_{\chi^2_d}(s)$.

### 4.3 Chi-Square Distribution & CDF

| Math | Lean | File |
|------|------|------|
| $\chi^2_d = \mathrm{Gamma}(d/2, 1/2)$ | `chiSqMeasureR d` | `EquivalenceFoundations.lean:258` |
| Law of $\lVert Z\rVert^2$ on $\mathbb{R}_{\ge 0}$ | `chiSqRadiusLaw d` | `EquivalenceFoundations.lean:282` |
| $F_{\chi^2_d}$ continuous ($d \ge 1$) | `chiSqCDFToUnit_isContinuousCDF` | `EquivalenceFoundations.lean:482` |
| $F_{\chi^2_d}$ strictly increasing ($d \ge 1$) | `chiSqCDFToUnit_isStrictlyIncreasingCDF` | `EquivalenceFoundations.lean:495` |

### 4.4 Probability Integral Transform

| Statement | Lean | File |
|-----------|------|------|
| $X \sim \mu$, $F_\mu$ continuous $\Rightarrow$ $F(X) \sim \mathrm{Unif}[0,1]$ | `probabilityIntegralTransform` | `EquivalenceFoundations.lean:535` |
| $F(X) \sim \mathrm{Unif}[0,1]$ + $F$ strictly increasing $\Rightarrow$ $X \sim \mu$ | `probabilityIntegralTransform_reverse` | `EquivalenceFoundations.lean:660` |

### 4.5 Distributions & Pushforward

| Math | Lean | File |
|------|------|------|
| Probability measure (total mass 1) | `Distribution α` = `ProbabilityMeasure α` | `EquivalenceFoundations.lean:68` |
| $f_\# Q(B) = Q(f^{-1}(B))$ | `pushforward f Q hf` | `EquivalenceFoundations.lean:73` |
| $P_Q = \Phi_\# Q$ | `wristbandLaw d Q` | `Equivalence.lean:23` |
| $\mu_0 = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$ | `wristbandUniform d` | `EquivalenceFoundations.lean:162` |

### 4.6 Kernel Definitions

| Python | Math | Lean | File |
|--------|------|------|------|
| `g = (u @ u.T).clamp(-1, 1)` | $\langle u, u' \rangle$ | `sphereInner` | `KernelPrimitives.lean:35` |
| `exp(2·β·α²·(g - 1))` | $\exp\!\big(2\beta\alpha^2(\langle u,u'\rangle - 1)\big)$ | `kernelAngChordal` | `KernelPrimitives.lean:53` |
| `exp(-β·diff²)` for 3 reflected diffs | $\sum_{j \in \{0,1,2\}} e^{-\beta \cdot \delta_j^2}$ | `kernelRad3Image` | `KernelPrimitives.lean:76` |
| — (infinite series) | $\sum_{n \in \mathbb{Z}} e^{-\beta(t - t' - 2n)^2}$ | `kernelRadNeumann` | `KernelPrimitives.lean:105` |
| angular × radial | $K(w, w') = k_{\mathrm{ang}} \cdot k_{\mathrm{rad}}$ | `wristbandKernel` / `wristbandKernelNeumann` | `KernelPrimitives.lean:189,195` |
| `total / (3n² - n)` | $\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W,W')]$ | `kernelEnergy` | `KernelPrimitives.lean:215` |

The angular factor is equivalent to a chordal RBF: $\exp(-\beta\alpha^2 \lVert u - u'\rVert^2)$,
since $\lVert u - u'\rVert^2 = 2(1 - \langle u, u'\rangle)$.

---

## 5. Literature Axioms

These are well-known results stated as Lean `axiom`s (accepted without proof)
because they are not yet available in Mathlib.

### 5.1 Gaussian polar decomposition (`EquivalenceImportedFacts.lean`)

| Axiom | Math | Line |
|-------|------|------|
| `gaussianNZ` | $\mathcal{N}(0,I_d)$ restricted to $\mathbb{R}^d \setminus \{0\}$ | 34 |
| `gaussianPolar_direction_uniform` | $Z/\lVert Z\rVert \sim \sigma_{d-1}$ | 42 |
| `gaussianPolar_radius_chiSq` | $\lVert Z\rVert^2 \sim \chi^2_d$ | 52 |
| `gaussianPolar_independent` | $Z/\lVert Z\rVert \perp \lVert Z\rVert^2$ | 60 |
| `sphereUniform_rotationInvariant` | $O_\# \sigma_{d-1} = \sigma_{d-1}$ | 73 |

Also: `sphereUniform_isProbability` (`EquivalenceFoundations.lean:149`).

### 5.2 Kernel theory (`KernelImportedFacts.lean`)

| Axiom | What it says | Line |
|-------|-------------|------|
| `kernelAngChordal_posSemiDef` | Chordal RBF on $S^{d-1}$ is PSD | 28 |
| `kernelRadNeumann_hasCosineExpansion` | Neumann kernel has cosine series expansion | 38 |
| `productKernel_posSemiDef_imported` | Product of PSD kernels is PSD | 62 |
| `kernelRadNeumann_posSemiDef_imported` | Neumann radial kernel is PSD | 78 |
| `neumannPotential_constant_imported` | Neumann potential is constant under uniform | 91 |
| `kernelAngChordal_universal` | Chordal RBF is universal | 101 |
| `kernelRadNeumann_universal` | Neumann kernel is universal | 108 |
| `productKernel_universal` | Product of universal kernels is universal | 115 |
| `universal_implies_characteristic` | Universal $\Rightarrow$ characteristic | 128 |
| `orthogonal_group_transitive_on_sphere` | $O(d)$ acts transitively on $S^{d-1}$ | 138 |
| `mmdSq_nonneg` | $\mathrm{MMD}^2 \ge 0$ for PSD kernels | 150 |

### 5.3 Spectral theory (`SpectralImportedFacts.lean`)

| Axiom | What it says | Line |
|-------|-------------|------|
| `kernelAngChordal_mercerExpansion` | Mercer decomposition of angular kernel into eigenfunctions/eigenvalues | 77 |
| `summable_neumannCosineCoeff_imported` | Neumann cosine coefficients are summable | 133 |
| `spectral_modeL1_factorized_bridge_imported` | Factorized L¹ majorant for mode integrals (Fubini/Tonelli) | 152 |

---

## 6. Proof Status

### Deferred proofs

Four lemmas use `sorry` (Lean keyword for a deferred proof):

| File | Lemma | Nature |
|------|-------|--------|
| `KernelFoundations.lean` | `measurable_wristbandKernelNeumann` | Measurability (routine) |
| `KernelFoundations.lean` | `integral_tsum_kernelRadNeumann` | Fubini for tsum (routine) |
| `KernelFoundations.lean` | `cosine_span_uniformly_dense_on_unitInterval` | Density of cosine span (Fourier / Stone-Weierstrass) |
| `KernelMinimization.lean` | `threeImage_energy_approx` | Neumann-to-3-image energy bound |

### Not yet formalized

| Python feature | Reference | Notes |
|----------------|-----------|-------|
| Angular-only auxiliary loss | angular loss block | Separate from joint kernel |
| Radial quantile penalty (Cramer-von Mises) | `rad_loss` (lines 755-759) | 1D Wasserstein on sorted $t$ |
| Moment penalties (`w2`, `kl`, `jeff`) | moment penalty block | $W_2^2$ to $\mathcal{N}(0,I)$ |
| Z-score calibration | final aggregation block | Affine rescaling (preserves minimizers) |
| Geodesic angular branch | geodesic option | Only chordal branch formalized |
| `per_point` reduction | default reduction mode | Only `global` branch matches population energy |

### Future directions

- **Main correctness theorem**: combine the equivalence and minimization results via $\log$ monotonicity.
- **Auxiliary terms**: show each additional penalty is $\ge 0$ and vanishes at the Gaussian, preserving the unique minimizer.

---

## 7. References

1. K.T. Fang, S. Kotz, K.W. Ng. *Symmetric Multivariate and Related Distributions.* Chapman & Hall, 1990.
2. G. Casella, R.L. Berger. *Statistical Inference.* 2nd ed., Duxbury, 2002.
3. B.K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Scholkopf, G.R.G. Lanckriet. "Hilbert space embeddings and metrics on probability measures." *JMLR* 11:1517-1561, 2010.
4. I. Steinwart, A. Christmann. *Support Vector Machines.* Springer, 2008.
5. A. Berlinet, C. Thomas-Agnan. *Reproducing Kernel Hilbert Spaces in Probability and Statistics.* Springer, 2004.
6. R.J. Serfling. *Approximation Theorems of Mathematical Statistics.* Wiley, 1980.
