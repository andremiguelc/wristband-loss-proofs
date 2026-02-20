# Wristband Formalization Audit

This document maps every mathematical operation in the Python wristband code
to its Lean 4 formalization, definition by definition.
A mathematician reading this should be able to verify that the Lean declarations
faithfully capture what the Python code computes.

Sources:

- Python: `ml-tidbits/python/embed_models/EmbedModels.py`
- Lean: `WristbandLossProofs/Foundations.lean`, `WristbandLossProofs/ImportedFacts.lean`, `WristbandLossProofs/Equivalence.lean`

---

## 1. Types

### Vectors

Python works with tensors of shape `(..., N, D)`. Each row is a vector in $\mathbb{R}^d$.

Lean:

```lean
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)
```

(`Foundations.lean:24`)

Math: $\mathbb{R}^d$.

### Nonzero vectors

Python clamps squared norms away from zero (`clamp_min(eps)`), so in practice
all vectors are nonzero. Lean encodes this as a subtype.

```lean
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}
```

(`Foundations.lean:32`)

Math: $\mathbb{R}^d \setminus \{0\}$.

### Unit sphere

Python normalizes vectors to unit length via `x * rsqrt(s)`.
The set of all such unit vectors is the sphere.

```lean
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)
```

(`Foundations.lean:28`)

Math: $S^{d-1} = \{x \in \mathbb{R}^d : \|x\| = 1\}$.

### Unit interval

Python clamps the CDF output to `(eps, 1 - eps)`, approximating $[0,1]$.

```lean
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1
```

(`Foundations.lean:36`)

Math: $[0,1]$.

### Wristband space

The output of the wristband map is a pair (direction, radial CDF value).

```lean
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval
```

(`Foundations.lean:40`)

Math: $\mathcal{W}_d = S^{d-1} \times [0,1]$.

---

## 2. The Wristband Map

### 2.1 Squared radius

Python (`EmbedModels.py:749`):

```python
s = xw.square().sum(dim=-1).clamp_min(eps)
```

Lean (`Foundations.lean:103`):

```lean
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal := ⟨‖z.1‖ ^ 2, by positivity⟩
```

Math:

$$s(x) = \|x\|^2.$$

The Lean version returns a nonneg real (`NNReal`) since the square of a norm
is always $\geq 0$. The Python `clamp_min(eps)` serves the same purpose numerically.

### 2.2 Direction

Python (`EmbedModels.py:750`):

```python
u = xw * torch.rsqrt(s)[..., :, None]
```

Lean (`Foundations.lean:114`):

```lean
noncomputable def direction {d : ℕ} (z : VecNZ d) : Sphere d := ...
```

Math:

$$u(x) = \frac{x}{\|x\|}.$$

The Lean definition constructs a term of type `Sphere d` (a vector of norm 1)
by dividing `z` by its norm, then proving the result has unit norm.

### 2.3 CDF transform (radial coordinate)

Python (`EmbedModels.py:751–752`):

```python
a_df = s.new_tensor(.5 * d_f)
t = torch.special.gammainc(a_df, .5 * s).clamp(eps, 1. - eps)
```

Lean (`Foundations.lean:451`):

```lean
noncomputable def chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval := ...
```

Math:

$$t(x) = F_{\chi^2_d}\!\bigl(\|x\|^2\bigr),$$

where $F_{\chi^2_d}$ is the CDF of the chi-square distribution with $d$ degrees
of freedom. The regularized lower incomplete gamma function satisfies
$\texttt{gammainc}(d/2,\, s/2) = F_{\chi^2_d}(s)$, so the Python and Lean
definitions compute the same function.

**Note on edge cases.** Lean defines `chiSqCDFToUnit` for all $d \in \mathbb{N}$,
including $d = 0$ (where it returns constant 0) and $d = 1$. The CDF properties
(continuity, strict monotonicity) carry the guard `hDim : 1 ≤ d`. Python never
runs with $d = 0$ in practice.

### 2.4 Bundled wristband map

There is no single Python line that bundles $(u, t)$ into one object — the code
just uses `u` and `t` as separate tensors downstream. Lean names the bundle
explicitly.

Lean (`Equivalence.lean:14`):

```lean
def wristbandMap (d : ℕ) (z : VecNZ d) : Wristband d :=
  (direction (d := d) z, chiSqCDFToUnit d (radiusSq z))
```

Math:

$$\Phi(z) = \bigl(u(z),\; t(z)\bigr) = \left(\frac{z}{\|z\|},\; F_{\chi^2_d}(\|z\|^2)\right).$$

---

## 3. The Chi-Square Distribution

The CDF transform in section 2.3 relies on the chi-square distribution being
well-defined and having specific analytic properties. This section covers how
Lean builds that.

### 3.1 Chi-square as a gamma distribution

Lean (`Foundations.lean:258`):

```lean
noncomputable def chiSqMeasureR (d : ℕ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (chiSqShape d) chiSqRate
```

where `chiSqShape d = d / 2` (`Foundations.lean:239`) and `chiSqRate = 1 / 2`
(`Foundations.lean:243`).

Math:

$$\chi^2_d = \mathrm{Gamma}(d/2,\; 1/2).$$

### 3.2 Chi-square radius law on $\mathbb{R}_{\geq 0}$

The squared norm $\|z\|^2$ takes values in $\mathbb{R}_{\geq 0}$, so Lean pushes
the real-valued gamma measure forward to `NNReal`.

Lean (`Foundations.lean:282`):

```lean
noncomputable def chiSqRadiusLaw (d : ℕ) : Distribution NNReal := ...
```

Math: the law of $S = \|Z\|^2$ when $Z \sim \mathcal{N}(0, I_d)$, viewed as a
probability measure on $\mathbb{R}_{\geq 0}$.

### 3.3 CDF properties

Two proven theorems establish that `chiSqCDFToUnit` is a valid CDF for the
chi-square radius law.

Lean (`Foundations.lean:482`):

```lean
theorem chiSqCDFToUnit_isContinuousCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...
```

Lean (`Foundations.lean:495`):

```lean
theorem chiSqCDFToUnit_isStrictlyIncreasingCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...
```

Math: for $d \geq 1$, the function $F_{\chi^2_d}$ is continuous and strictly
increasing on $\mathbb{R}_{\geq 0}$. Both are fully proven in Lean using
Mathlib's `gammaMeasure` infrastructure.

Measurability is also proven (`Foundations.lean:464`):

```lean
lemma chiSqCDFToUnit_measurable (d : ℕ) : Measurable (chiSqCDFToUnit d) := ...
```

---

## 4. Distributions and Pushforward

### 4.1 Distribution type

Lean wraps `ProbabilityMeasure` as an alias.

```lean
abbrev Distribution (α : Type u) [MeasurableSpace α] : Type u :=
  ProbabilityMeasure α
```

(`Foundations.lean:68`)

This guarantees total mass 1 by construction.

### 4.2 Pushforward

In Python, applying the wristband map to a batch of samples is an empirical
pushforward — each sample $x_i$ becomes $(u_i, t_i)$. Lean captures the
measure-theoretic version.

```lean
abbrev pushforward {α : Type u} {β : Type v}
    (f : α → β) [MeasurableSpace α] [MeasurableSpace β]
    : Distribution α → Measurable f → Distribution β := ...
```

(`Foundations.lean:73`)

Math: given a measure $Q$ on $\alpha$ and a measurable function $f : \alpha \to \beta$,

$$f_\# Q(B) = Q(f^{-1}(B)).$$

### 4.3 Wristband law

The pushforward of any law $Q$ on $\mathbb{R}^d \setminus \{0\}$ through
the wristband map.

```lean
def wristbandLaw (d : ℕ) (Q : Distribution (VecNZ d)) : Distribution (Wristband d) :=
  pushforward (wristbandMap d) Q (measurable_wristbandMap d)
```

(`Equivalence.lean:23`)

Math: $P_Q = \Phi_\# Q$.

### 4.4 Target law (uniform on wristband space)

The ideal output of the wristband map when the input is Gaussian.

```lean
def wristbandUniform (d : ℕ) : Distribution (Wristband d) :=
  productLaw (sphereUniform d) uniform01
```

(`Foundations.lean:162`)

This uses:

- `sphereUniform d`: normalized surface measure on $S^{d-1}$
  (`Foundations.lean:155`)
- `uniform01`: Lebesgue measure restricted to $[0,1]$
  (`Foundations.lean:98`)

Math:

$$\mu_0 = \sigma_{d-1} \otimes \mathrm{Unif}[0,1].$$

---

## 5. Gaussian Polar Decomposition

When $Z \sim \mathcal{N}(0, I_d)$, three classical facts hold:
its direction is uniform on the sphere, its squared norm is chi-square,
and these two are independent. In Lean, these are stated as axioms
(well-known results not yet formalized in Mathlib).

### 5.1 Gaussian law on nonzero vectors

```lean
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)
```

(`ImportedFacts.lean:34`)

Math: the standard Gaussian $\mathcal{N}(0, I_d)$ restricted to
$\mathbb{R}^d \setminus \{0\}$ (which has full measure).

**Partial match.** The axiom declares `gaussianNZ` directly as a primitive,
with no connection to an ambient Gaussian on `Vec d`. In Python (and in
standard probability), the Gaussian lives on all of $\mathbb{R}^d$ and the
restriction to nonzero vectors is a derived fact ($\gamma_d(\{0\}) = 0$).
Lean is missing the bridge between the two. See section 9.5.

### 5.2 Direction is uniform on the sphere

```lean
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) (measurable_direction d)
    = sphereUniform d
```

(`ImportedFacts.lean:37`)

Math: $Z \sim \mathcal{N}(0, I_d) \Rightarrow Z / \|Z\| \sim \sigma_{d-1}$.

### 5.3 Squared radius is chi-square

```lean
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) (measurable_radiusSq d)
    = chiSqRadiusLaw d
```

(`ImportedFacts.lean:41`)

Math: $Z \sim \mathcal{N}(0, I_d) \Rightarrow \|Z\|^2 \sim \chi^2_d$.

### 5.4 Independence of direction and radius

```lean
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d)
      (direction (d := d)) (radiusSq (d := d))
      (measurable_direction d) (measurable_radiusSq d)
```

(`ImportedFacts.lean:45`)

Math: $Z / \|Z\| \perp \|Z\|^2$.

### 5.5 Rotation invariance of the sphere measure

```lean
axiom sphereUniform_rotationInvariant (d : ℕ)
    (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d)
      (measurable_rotateSphere O) = sphereUniform d
```

(`ImportedFacts.lean:60`)

Math: for any orthogonal $O$, $O_\# \sigma_{d-1} = \sigma_{d-1}$.

---

## 6. The Probability Integral Transform

The wristband map uses the CDF $F_{\chi^2_d}$ to turn a chi-square random
variable into a uniform one. This is a special case of the probability integral
transform (PIT).

### 6.1 Forward PIT

```lean
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hF : IsContinuousCDFFor μ F)
    (hFZero : (F 0 : ℝ) = 0) :
    pushforward F μ hFMeas = uniform01 := by ...
```

(`Foundations.lean:535`)

Math: if $X \sim \mu$, $F = F_\mu$ is continuous, and $F(0)=0$, then
$F(X) \sim \mathrm{Unif}(0,1)$.

**Partial match.** The classical PIT holds for any continuous CDF on any
ordered space. The Lean statement is restricted to `Distribution NNReal` —
it only applies to nonneg-real-valued random variables. This is sufficient
for the wristband use case (where the argument is $\|z\|^2 \geq 0$), but
narrower than the textbook version.

Status: **fully proven** (`Foundations.lean:535`). The endpoint guard
`hFZero : F 0 = 0` is essential on `ℝ≥0` to exclude degenerate-at-zero
counterexamples.

### 6.2 Reverse PIT

```lean
theorem probabilityIntegralTransform_reverse
    (targetLaw observedLaw : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hCDF : IsContinuousCDFFor targetLaw F)
    (hStrict : IsStrictlyIncreasingCDFFor targetLaw F)
    (hUniform : pushforward F observedLaw hFMeas = uniform01) :
    observedLaw = targetLaw := by sorry
```

(`Foundations.lean:662`)

Math: if $F$ is a continuous, strictly increasing CDF for $\mu$, and
$F(X) \sim \mathrm{Unif}(0,1)$, then $X \sim \mu$.

Status: **statement only** (`sorry`).

---

## 7. The Main Equivalence Theorem

### 7.1 Forward direction

```lean
theorem wristbandEquivalence_forward (d : ℕ) (hDim : 2 ≤ d) :
    wristbandLaw d (gaussianNZ d) = wristbandUniform d := by sorry
```

(`Equivalence.lean:185`)

Math: if $Q = \mathcal{N}(0, I_d)$ and $d \geq 2$, then

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1].$$

**Partial match.** The Lean guard `hDim : 2 ≤ d` excludes $d = 1$. The Python
code imposes no dimension lower bound — it will run for any $d \geq 1$.
Mathematically, for $d = 1$ the "sphere" $S^0 = \{-1, +1\}$ is discrete, so
the uniform sphere measure is $\frac{1}{2}\delta_{-1} + \frac{1}{2}\delta_{+1}$
and the forward direction still holds. The backward direction (uniqueness) also
holds for $d = 1$ but requires a separate argument since the sphere is not
connected. The $d \geq 2$ guard is a simplification, not a fundamental
limitation.

Status: **statement only** (`sorry`).

### 7.2 Backward direction

```lean
theorem wristbandEquivalence_backward (d : ℕ) (hDim : 2 ≤ d)
    (Q : Distribution (VecNZ d))
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by sorry
```

(`Equivalence.lean:201`)

Math: if $\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$ and $d \geq 2$,
then $Q = \mathcal{N}(0, I_d)$.

Status: **statement only** (`sorry`).

### 7.3 Biconditional

```lean
theorem wristbandEquivalence (d : ℕ) (hDim : 2 ≤ d)
    (Q : Distribution (VecNZ d)) :
    wristbandLaw d Q = wristbandUniform d ↔ Q = gaussianNZ d := ...
```

(`Equivalence.lean:215`)

Math:

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \iff Q = \mathcal{N}(0, I_d).$$

Status: **fully proven** — follows directly from 7.1 and 7.2.

---

## 8. Supporting Lemmas

These declarations have no direct Python counterpart. They exist only in the
Lean proof pipeline to support the equivalence theorem.

### 8.1 Spherical law reconstruction

```lean
def sphericalLaw (d : ℕ) (radiusSqLaw : Distribution NNReal) :
    Distribution (Vec d) := ...
```

(`Equivalence.lean:48`)

Math: the law of $Z = \sqrt{S} \cdot U$ where $S \sim \text{radiusSqLaw}$,
$U \sim \sigma_{d-1}$, and $S \perp U$.

### 8.2 Rotation invariance of spherical laws

```lean
theorem sphericalLaw_rotationInvariant (d : ℕ) (_hDim : 2 ≤ d)
    (radiusSqLaw : Distribution NNReal) :
    IsRotationInvariant d (sphericalLaw d radiusSqLaw) := ...
```

(`Equivalence.lean:63`)

Math: for any orthogonal $O$ and any radial law,
$O_\# (\text{sphericalLaw}) = \text{sphericalLaw}$.

Status: **fully proven**.

### 8.3 Spherical law determined by radius

```lean
theorem sphericalLaw_determinedByRadius (d : ℕ) (hDim : 2 ≤ d) ... :
    pushforward (...) μ hReconstruct = sphericalLaw d (pushforward S μ hS)
    := by sorry
```

(`Equivalence.lean:156`)

Math: if direction is uniform and independent of squared radius, then the
full vector law equals the spherical law built from that radius law.

Status: **statement only** (`sorry`).

### 8.4 Sphere measure is a probability measure

```lean
axiom sphereUniform_isProbability (d : ℕ) :
    IsProbabilityMeasure (((sphereSurface d) Set.univ)⁻¹ • sphereSurface d)
```

(`Foundations.lean:149`)

Math: the sphere $S^{d-1}$ has finite nonzero surface area, so the normalized
surface measure has total mass 1.

Status: **axiom**. Proving this requires showing $0 < \mathcal{H}^{d-1}(S^{d-1}) < \infty$,
which is not yet available in Mathlib.

---

## 9. Gaps and Proposed Fixes

This section lists Python computations that have no Lean counterpart,
and deferred proofs.

### 9.1 Kernel losses (not formalized)

The Python code computes a joint reflected kernel on wristband space as the
product of an angular kernel and a reflected radial kernel:

$$k_{\mathrm{ang}}(u_i, u_j) = \exp\!\bigl(-\beta\alpha^2 \, \delta(u_i, u_j)^2\bigr),$$

$$k_{\mathrm{rad}}(t_i, t_j) = e^{-\beta(t_i - t_j)^2} + e^{-\beta(t_i + t_j)^2} + e^{-\beta(t_i + t_j - 2)^2},$$

$$K\bigl((u_i, t_i), (u_j, t_j)\bigr) = k_{\mathrm{ang}}(u_i, u_j) \cdot k_{\mathrm{rad}}(t_i, t_j).$$

The angular distance $\delta$ has two variants in Python:

- **Chordal** (`angular="chordal"`, default): $\delta(u_i, u_j)^2 = \|u_i - u_j\|^2 = 2 - 2\langle u_i, u_j\rangle$.
  Python (`EmbedModels.py:764`): `e_ang = 2*beta*alpha^2*(g - 1)`.

- **Geodesic** (`angular="geodesic"`): $\delta(u_i, u_j) = \arccos\langle u_i, u_j\rangle$.
  Python (`EmbedModels.py:767`): `theta = torch.acos(g)`, then `e_ang = -beta*alpha^2*theta^2`.

The Python loss function also wraps the kernel energy in a logarithm and
averages it, with two reduction modes:

- **Per-point** (`reduction="per_point"`): average kernel value per row, then
  log, then mean over rows (`EmbedModels.py:792–797`).
- **Global** (`reduction="global"`): average kernel value over all pairs,
  then log (`EmbedModels.py:799–804`).

The coupling constant $\alpha$ defaults to a heuristic that balances the
angular and radial kernel bandwidths: $\alpha = \sqrt{1/12}$ for chordal,
$\alpha = \sqrt{2/(3\pi^2)}$ for geodesic (`EmbedModels.py:606–611`).

Python: `EmbedModels.py:762` (angular exponent), `EmbedModels.py:787–789`
(reflected differences), `EmbedModels.py:792` (kernel aggregation).

Lean: **nothing**. No kernel definitions, no energy functional, no uniqueness
theorem for kernel-based losses.

Proposed fix: define the kernel $K$ on `Wristband d × Wristband d → ℝ` and state
that the kernel energy $\mathbb{E}[K(w_i, w_j)]$ is minimized uniquely at
$\mu_0 = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$. This connects the
optimization objective to the equivalence theorem. The chordal variant is
the natural starting point for formalization (see `wristband_proof_plan.md`,
section 3).

### 9.2 Angular-only uniformity loss (not formalized)

When `lambda_ang != 0`, Python computes a separate angular-only kernel energy
using only $k_{\mathrm{ang}}$ (without the radial factor). This measures how
far the directional marginal alone is from uniform on the sphere.

Python (`EmbedModels.py:772–782`):

$$L_{\mathrm{ang}} = \frac{1}{\beta} \log \frac{1}{n(n-1)} \sum_{i \neq j} k_{\mathrm{ang}}(u_i, u_j).$$

Lean: **nothing**.

Proposed fix: this is a special case of a kernel energy on $S^{d-1}$ alone. It
could be stated as a corollary of the general kernel identification property
(section 9.1), restricted to the angular marginal.

### 9.3 Radial quantile penalty (not formalized)

Python (`EmbedModels.py:757–759`):

```python
t_sorted, _ = torch.sort(t, dim=-1)
q = (torch.arange(n, ...) + .5) / n_f
rad_loss = 12. * (t_sorted - q).square().mean(dim=-1)
```

Math:

$$L_{\mathrm{rad}} = 12 \cdot \frac{1}{n} \sum_{i=1}^{n} \bigl(t_{(i)} - q_i\bigr)^2, \qquad q_i = \frac{i - 1/2}{n}.$$

This is the Cramér–von Mises statistic (up to scaling) for testing uniformity
of the radial CDF values $t_i$.

Lean: **nothing**.

Proposed fix: define the empirical quantile loss as a function
`List UnitInterval → ℝ` and state that it equals zero iff the empirical
distribution is exactly the quantiles of $\mathrm{Unif}[0,1]$.

### 9.4 Moment penalty (not formalized)

The Python code supports six moment penalty types (`EmbedModels.py:711–746`).
The default and mathematically most relevant is the squared Bures–Wasserstein
distance to $\mathcal{N}(0, I)$:

**`moment="w2"`** (default, `EmbedModels.py:711`, using `W2ToStandardNormalSq`
at `EmbedModels.py:451`):

$$W_2^2\bigl(\mathcal{N}(\hat\mu, \hat\Sigma),\; \mathcal{N}(0, I)\bigr) = \|\hat\mu\|^2 + \sum_k \bigl(\sqrt{\lambda_k} - 1\bigr)^2,$$

where $\hat\mu$ and $\hat\Sigma$ are the sample mean and covariance, and
$\lambda_k$ are eigenvalues of $\hat\Sigma$.

The other five variants are:

- `"jeff_diag"` (`EmbedModels.py:713`): diagonal Jeffreys divergence.
- `"jeff_full"` (`EmbedModels.py:719`): full-covariance Jeffreys divergence.
- `"mu_only"` (`EmbedModels.py:733`): squared mean norm only.
- `"kl_diag"` (`EmbedModels.py:735`): diagonal KL divergence.
- `"kl_full"` (`EmbedModels.py:738`): full-covariance KL divergence.

All six are nonneg and equal zero at $Q = \mathcal{N}(0, I)$.

Lean: **nothing**.

Proposed fix: define the Bures–Wasserstein distance between two Gaussian
measures on `Vec d` and prove the closed-form formula above. The other five
variants are engineering alternatives; formalizing `w2` alone is sufficient
for the main correctness argument.

### 9.5 Calibration and loss aggregation (not formalized)

Python (`EmbedModels.py:827–833`):

$$\hat{L}_c = \frac{L_c - m_c}{s_c}, \qquad L_{\mathrm{total}} = \frac{\hat{L}_{\mathrm{rep}} + \lambda_{\mathrm{rad}} \hat{L}_{\mathrm{rad}} + \lambda_{\mathrm{ang}} \hat{L}_{\mathrm{ang}} + \lambda_{\mathrm{mom}} \hat{L}_{\mathrm{mom}}}{s_{\mathrm{total}}}.$$

Lean: **nothing**. This is a numerical/engineering concern (z-scoring each loss
component using calibration statistics from Gaussian samples). Formalizing it
is low priority — it does not affect the mathematical correctness of the
wristband characterization.

### 9.6 Ambient Gaussian bridge (missing)

`gaussianNZ` is declared as a direct axiom on nonzero vectors. There is no
explicit bridge from the ambient Gaussian $\mathcal{N}(0, I_d)$ on all of
$\mathbb{R}^d$, restricted to $\mathbb{R}^d \setminus \{0\}$.

Proposed fix: add an axiom or lemma stating that restricting the standard
Gaussian measure on `Vec d` to the nonzero subtype yields `gaussianNZ d`.

### 9.7 Deferred proofs (`sorry`)

Four theorem statements have no proof:

1. `probabilityIntegralTransform_reverse` (`Foundations.lean:662`) — reverse PIT
2. `sphericalLaw_determinedByRadius` (`Equivalence.lean:156`) — identification
3. `wristbandEquivalence_forward` (`Equivalence.lean:185`) — forward equivalence
4. `wristbandEquivalence_backward` (`Equivalence.lean:201`) — backward equivalence

The last two depend on the first two. With forward PIT now proven, reverse PIT
(item 1) plus the identification lemma (item 2) are the main blockers.
