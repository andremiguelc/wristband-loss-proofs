# Wristband Loss — Lean Proof Guide

This document is for ML practitioners who want to verify that the Lean 4
formalization faithfully captures the mathematics behind
[`C_WristbandGaussianLoss`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

**Central claim (population setting):**

$$\Phi_\# Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

In words: the wristband map produces uniform output **if and only if** the
input is standard Gaussian. Combined with the kernel energy minimization
result, this implies the wristband repulsion loss has a **unique minimizer**
at the Gaussian.

---

## 1. Lean File Map

| File | Contents | Status |
|------|----------|--------|
| `EquivalenceFoundations.lean` | Types, chi-square distribution, CDF, probability integral transform | Fully proven |
| `EquivalenceImportedFacts.lean` | Gaussian polar decomposition (axioms from literature) | 5 axioms |
| `Equivalence.lean` | Wristband map, equivalence theorem (forward + backward + iff) | Fully proven |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic/universal predicates | Definitions only |
| `KernelImportedFacts.lean` | PSD, universality, constant-potential axioms (from literature) | 11 axioms |
| `KernelFoundations.lean` | Kernel properties, symmetry, measurability, characteristic proofs, constant-potential proofs | Mostly proven (3 `sorry`) |
| `KernelMinimization.lean` | Energy minimization + uniqueness at uniform; Neumann-to-3-image bridge | Proven for Neumann kernel; 3-image bridge `sorry` |

---

## 2. Proof Architecture

```
Step 1: Wristband Equivalence          Step 2: Kernel Energy Minimization
   (Equivalence.lean)                     (KernelMinimization.lean)
   Φ_#Q = μ₀  ⟺  Q = γ                  E(P) ≥ E(μ₀), equality iff P = μ₀
          \                                  /
           \                                /
            ↘                              ↙
         Step 3: Main Correctness Theorem
         The repulsion loss L_rep(Q) = (1/β)·log E[K]
         is uniquely minimized at Q = γ
                        |
                        ↓
         Step 4: Extra Terms Preserve Minimizer
         Radial, moment, angular penalties are ≥ 0
         and vanish at γ  →  same unique minimizer
```

| Step | Statement | Status |
|------|-----------|--------|
| 1 | $\Phi_\# Q = \mu_0 \iff Q = \gamma$ | **Complete** (sorry-free) |
| 2 | $\mathcal{E}(P) \ge \mathcal{E}(\mu_0)$, equality iff $P = \mu_0$ | **Complete** for Neumann kernel |
| 3 | Combine Steps 1 + 2 via $\log$ monotonicity | Not yet formalized |
| 4 | Nonneg-addon lemma for auxiliary terms | Not yet formalized |

Steps 1 and 2 are independent. Step 3 combines them. Step 4 extends Step 3.

---

## 3. Python-to-Lean Correspondence

All Python references are to
[`EmbedModels.py`](https://github.com/mvparakhin/ml-tidbits/blob/main/python/embed_models/EmbedModels.py).

### 3.1 Types

| Math | Python | Lean | File |
|------|--------|------|------|
| $\mathbb{R}^d$ | tensors of shape `(..., N, D)` | `Vec d` = `EuclideanSpace ℝ (Fin d)` | `EquivalenceFoundations.lean:24` |
| $\mathbb{R}^d \setminus \{0\}$ | `clamp_min(eps)` guards | `VecNZ d` = `{z : Vec d // z ≠ 0}` | `EquivalenceFoundations.lean:32` |
| $S^{d-1}$ | `u = x * rsqrt(s)` | `Sphere d` = `Metric.sphere 0 1` | `EquivalenceFoundations.lean:28` |
| $[0, 1]$ | `clamp(eps, 1-eps)` | `UnitInterval` = `Set.Icc 0 1` | `EquivalenceFoundations.lean:36` |
| $S^{d-1} \times [0,1]$ | `(u, t)` pair | `Wristband d` = `Sphere d × UnitInterval` | `EquivalenceFoundations.lean:40` |

### 3.2 Wristband Map

| Python | Math | Lean | File |
|--------|------|------|------|
| `s = xw.square().sum(-1).clamp_min(eps)` | $s(x) = \lVert x \rVert^2$ | `radiusSq` | `EquivalenceFoundations.lean:103` |
| `u = xw * rsqrt(s)[..., :, None]` | $u(x) = x / \lVert x \rVert$ | `direction` | `EquivalenceFoundations.lean:114` |
| `t = gammainc(d/2, s/2).clamp(eps, 1-eps)` | $t(x) = F_{\chi^2_d}(\lVert x \rVert^2)$ | `chiSqCDFToUnit` | `EquivalenceFoundations.lean:451` |
| `(u, t)` used downstream | $\Phi(z) = (u(z),\, t(z))$ | `wristbandMap` | `Equivalence.lean:14` |

The Python `gammainc(d/2, s/2)` is the regularized lower incomplete gamma function,
which equals the chi-square CDF: $\texttt{gammainc}(d/2, s/2) = F_{\chi^2_d}(s)$.

### 3.3 Chi-Square Distribution & CDF

| Math | Lean | File |
|------|------|------|
| $\chi^2_d = \mathrm{Gamma}(d/2, 1/2)$ | `chiSqMeasureR d` | `EquivalenceFoundations.lean:258` |
| Law of $\lVert Z\rVert^2$ on $\mathbb{R}_{\ge 0}$ | `chiSqRadiusLaw d` | `EquivalenceFoundations.lean:282` |
| $F_{\chi^2_d}$ continuous ($d \ge 1$) | `chiSqCDFToUnit_isContinuousCDF` | `EquivalenceFoundations.lean:482` |
| $F_{\chi^2_d}$ strictly increasing ($d \ge 1$) | `chiSqCDFToUnit_isStrictlyIncreasingCDF` | `EquivalenceFoundations.lean:495` |

### 3.4 Probability Integral Transform

These theorems formalize why applying the CDF to the radial coordinate works.

| Statement | Lean | File | Status |
|-----------|------|------|--------|
| $X \sim \mu$, $F_\mu$ continuous with $F(0)=0$ $\Rightarrow$ $F(X) \sim \mathrm{Unif}[0,1]$ | `probabilityIntegralTransform` | `EquivalenceFoundations.lean:535` | Proven |
| $F(X) \sim \mathrm{Unif}[0,1]$ + $F$ strictly increasing $\Rightarrow$ $X \sim \mu$ | `probabilityIntegralTransform_reverse` | `EquivalenceFoundations.lean:660` | Proven |

The reverse PIT is what makes `gammainc` the *uniquely correct* radial
transform — not just a convenient choice. If the CDF-transformed radius is
uniform, the original radius **must** be chi-square.

### 3.5 Distributions & Pushforward

| Math | Lean | File |
|------|------|------|
| Probability measure (total mass 1) | `Distribution α` = `ProbabilityMeasure α` | `EquivalenceFoundations.lean:68` |
| $f_\# Q(B) = Q(f^{-1}(B))$ | `pushforward f Q hf` | `EquivalenceFoundations.lean:73` |
| $P_Q = \Phi_\# Q$ | `wristbandLaw d Q` | `Equivalence.lean:23` |
| $\mu_0 = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$ | `wristbandUniform d` | `EquivalenceFoundations.lean:162` |

### 3.6 Kernel Definitions

| Python | Math | Lean | File |
|--------|------|------|------|
| `g = (u @ u.T).clamp(-1, 1)` | $\langle u, u' \rangle$ | `sphereInner` | `KernelPrimitives.lean:35` |
| `exp(2·β·α²·(g - 1))` | $\exp\!\big(2\beta\alpha^2(\langle u,u'\rangle - 1)\big)$ | `kernelAngChordal` | `KernelPrimitives.lean:53` |
| `exp(-β·diff²)` for 3 reflected diffs | $\sum_{j \in \{0,1,2\}} e^{-\beta \cdot \delta_j^2}$ | `kernelRad3Image` | `KernelPrimitives.lean:76` |
| — (infinite series) | $\sum_{n \in \mathbb{Z}} e^{-\beta(t - t' - 2n)^2}$ | `kernelRadNeumann` | `KernelPrimitives.lean:105` |
| angular × radial | $K(w, w') = k_{\mathrm{ang}} \cdot k_{\mathrm{rad}}$ | `wristbandKernel` / `wristbandKernelNeumann` | `KernelPrimitives.lean:189,195` |
| `total / (3n² - n)` | $\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W,W')]$ | `kernelEnergy` | `KernelPrimitives.lean:215` |

The angular factor $k_{\mathrm{ang}}$ is algebraically equivalent to
$\exp(-\beta\alpha^2 \lVert u - u' \rVert^2)$ (chordal RBF on the sphere),
since $\lVert u - u'\rVert^2 = 2(1 - \langle u, u'\rangle)$.

The 3-image radial kernel uses reflected copies at $-t'$ and $2-t'$ to correct
boundary effects on $[0,1]$ — this is the method-of-images trick from KDE
boundary correction. The Neumann kernel is the full infinite reflection series;
the 3-image version keeps only the $n \in \{-1, 0, 1\}$ terms, with omitted
terms exponentially small in $\beta$.

---

## 4. Main Theorems

### 4.1 Wristband Equivalence

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \;\iff\; Q = \mathcal{N}(0, I_d), \qquad d \ge 2.$$

| Direction | Lean | File | Proof idea |
|-----------|------|------|------------|
| Forward ($\Rightarrow$) | `wristbandEquivalence_forward` | `Equivalence.lean:515` | Gaussian polar decomposition + PIT |
| Backward ($\Leftarrow$) | `wristbandEquivalence_backward` | `Equivalence.lean:695` | Reverse PIT + spherical law reconstruction |
| Iff | `wristbandEquivalence` | `Equivalence.lean:999` | Combines forward + backward |

**Status:** Fully proven (sorry-free).

The $d \ge 2$ guard is intentional: $d = 1$ gives $S^0 = \{-1, +1\}$
(discrete), while the continuous sphere geometry requires $d \ge 2$.
Python allows $d \ge 1$ but practical usage is high-dimensional.

### 4.2 Kernel Energy Minimization

For the Neumann kernel $K_N$ with $\beta > 0$, $\alpha > 0$, $d \ge 2$:

$$\mathcal{E}(P) \;\ge\; \mathcal{E}(\mu_0), \qquad \text{with equality iff } P = \mu_0.$$

| Theorem | Lean | File |
|---------|------|------|
| Minimization | `kernelEnergy_minimized_at_uniform` | `KernelMinimization.lean:133` |
| Uniqueness | `kernelEnergy_minimizer_unique` | `KernelMinimization.lean:155` |

**Status:** Proven for the Neumann kernel (given imported facts).

The proof follows the standard MMD pathway:
1. $K_N$ is PSD $\Rightarrow$ $\mathrm{MMD}^2(P, \mu_0) \ge 0$
2. Potential $h(w) = \mathbb{E}_{W' \sim \mu_0}[K_N(w, W')]$ is constant $\Rightarrow$ $\mathcal{E}(P) - \mathcal{E}(\mu_0) = \mathrm{MMD}^2(P, \mu_0)$
3. $K_N$ is characteristic $\Rightarrow$ $\mathrm{MMD}^2 = 0$ iff $P = \mu_0$

### 4.3 Neumann-to-3-Image Bridge

| Theorem | Lean | File | Status |
|---------|------|------|--------|
| Pointwise bound: $\lvert k_{\mathrm{3img}} - k_N \rvert \le C(\beta)$ | `threeImage_approx_neumann` | `KernelMinimization.lean:666` | `sorry` (bound stated, proof pending) |
| Energy bound: $\lvert \mathcal{E}_{\mathrm{3img}} - \mathcal{E}_N \rvert \le C(\beta)$ | `threeImage_energy_approx` | `KernelMinimization.lean:806` | `sorry` |

The truncation error bound $C(\beta)$ is $O(e^{-\beta})$, exponentially small
in the kernel bandwidth.

---

## 5. Axioms & Imported Facts

These are well-known results from the literature, stated as Lean `axiom`s
because they are not yet available in Mathlib.

### 5.1 Gaussian polar decomposition (`EquivalenceImportedFacts.lean`)

| Axiom | Math | Line |
|-------|------|------|
| `gaussianNZ` | $\mathcal{N}(0,I_d)$ restricted to $\mathbb{R}^d \setminus \{0\}$ | 34 |
| `gaussianPolar_direction_uniform` | $Z/\lVert Z\rVert \sim \sigma_{d-1}$ | 42 |
| `gaussianPolar_radius_chiSq` | $\lVert Z\rVert^2 \sim \chi^2_d$ | 52 |
| `gaussianPolar_independent` | $Z/\lVert Z\rVert \perp \lVert Z\rVert^2$ | 60 |
| `sphereUniform_rotationInvariant` | $O_\# \sigma_{d-1} = \sigma_{d-1}$ | 73 |

Also: `sphereUniform_isProbability` (`EquivalenceFoundations.lean:149`) —
normalized surface measure has mass 1.

**Gap:** `gaussianNZ` is declared as a primitive, with no bridge from an
ambient Gaussian on all of $\mathbb{R}^d$. In principle this requires
$\gamma_d(\{0\}) = 0$, which is standard but not yet in Mathlib.

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

---

## 6. Remaining Work

### Deferred proofs (`sorry`)

| File | What | Nature |
|------|------|--------|
| `KernelFoundations.lean` | `measurable_wristbandKernelNeumann` | Measurability (routine) |
| `KernelFoundations.lean` | `integral_tsum_kernelRadNeumann` | Fubini for tsum (routine) |
| `KernelFoundations.lean` | `cosine_span_uniformly_dense_on_unitInterval` | Density of cosine span (standard Fourier argument) |
| `KernelMinimization.lean` | `threeImage_approx_neumann` | Neumann-to-3-image pointwise bound |
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

### Steps 3-4 (not started)

- **Step 3** combines Steps 1+2 via $\log$ monotonicity — immediate once bridged.
- **Step 4** applies a nonneg-addon lemma to each auxiliary term — short, self-contained.

---

## 7. References

1. K.T. Fang, S. Kotz, K.W. Ng. *Symmetric Multivariate and Related Distributions.* Chapman & Hall, 1990.
2. G. Casella, R.L. Berger. *Statistical Inference.* 2nd ed., Duxbury, 2002.
3. B.K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Scholkopf, G.R.G. Lanckriet. "Hilbert space embeddings and metrics on probability measures." *JMLR* 11:1517-1561, 2010.
4. I. Steinwart, A. Christmann. *Support Vector Machines.* Springer, 2008.
5. A. Berlinet, C. Thomas-Agnan. *Reproducing Kernel Hilbert Spaces in Probability and Statistics.* Springer, 2004.
6. R.J. Serfling. *Approximation Theorems of Mathematical Statistics.* Wiley, 1980.
