# Wristband Formalization Audit

This document maps every mathematical operation in the Python wristband code
to its Lean 4 formalization, definition by definition.
A mathematician reading this should be able to verify that the Lean declarations
faithfully capture what the Python code computes.

Sources:

- Python: `ml-tidbits/python/embed_models/EmbedModels.py`
- Lean (equivalence core): `WristbandLossProofs/EquivalenceFoundations.lean`, `WristbandLossProofs/EquivalenceImportedFacts.lean`, `WristbandLossProofs/Equivalence.lean`
- Lean (kernel step): `WristbandLossProofs/KernelFoundations.lean`, `WristbandLossProofs/KernelImportedFacts.lean`, `WristbandLossProofs/KernelMinimization.lean`

---

## 1. Types

### Vectors

Python works with tensors of shape `(..., N, D)`. Each row is a vector in $\mathbb{R}^d$.

Lean:

```lean
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)
```

(`EquivalenceFoundations.lean:24`)

Math: $\mathbb{R}^d$.

### Nonzero vectors

Python clamps squared norms away from zero (`clamp_min(eps)`), so in practice
all vectors are nonzero. Lean encodes this as a subtype.

```lean
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}
```

(`EquivalenceFoundations.lean:32`)

Math: $\mathbb{R}^d \setminus \{0\}$.

### Unit sphere

Python normalizes vectors to unit length via `x * rsqrt(s)`.
The set of all such unit vectors is the sphere.

```lean
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)
```

(`EquivalenceFoundations.lean:28`)

Math: $S^{d-1} = \{x \in \mathbb{R}^d : \|x\| = 1\}$.

### Unit interval

Python clamps the CDF output to `(eps, 1 - eps)`, approximating $[0,1]$.

```lean
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1
```

(`EquivalenceFoundations.lean:36`)

Math: $[0,1]$.

### Wristband space

The output of the wristband map is a pair (direction, radial CDF value).

```lean
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval
```

(`EquivalenceFoundations.lean:40`)

Math: $\mathcal{W}_d = S^{d-1} \times [0,1]$.

---

## 2. The Wristband Map

### 2.1 Squared radius

Python (`EmbedModels.py:749`):

```python
s = xw.square().sum(dim=-1).clamp_min(eps)
```

Lean (`EquivalenceFoundations.lean:103`):

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

Lean (`EquivalenceFoundations.lean:114`):

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

Lean (`EquivalenceFoundations.lean:451`):

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

Lean (`EquivalenceFoundations.lean:258`):

```lean
noncomputable def chiSqMeasureR (d : ℕ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (chiSqShape d) chiSqRate
```

where `chiSqShape d = d / 2` (`EquivalenceFoundations.lean:239`) and `chiSqRate = 1 / 2`
(`EquivalenceFoundations.lean:243`).

Math:

$$\chi^2_d = \mathrm{Gamma}(d/2,\; 1/2).$$

### 3.2 Chi-square radius law on $\mathbb{R}_{\geq 0}$

The squared norm $\|z\|^2$ takes values in $\mathbb{R}_{\geq 0}$, so Lean pushes
the real-valued gamma measure forward to `NNReal`.

Lean (`EquivalenceFoundations.lean:282`):

```lean
noncomputable def chiSqRadiusLaw (d : ℕ) : Distribution NNReal := ...
```

Math: the law of $S = \|Z\|^2$ when $Z \sim \mathcal{N}(0, I_d)$, viewed as a
probability measure on $\mathbb{R}_{\geq 0}$.

### 3.3 CDF properties

Two proven theorems establish that `chiSqCDFToUnit` is a valid CDF for the
chi-square radius law.

Lean (`EquivalenceFoundations.lean:482`):

```lean
theorem chiSqCDFToUnit_isContinuousCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...
```

Lean (`EquivalenceFoundations.lean:495`):

```lean
theorem chiSqCDFToUnit_isStrictlyIncreasingCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...
```

Math: for $d \geq 1$, the function $F_{\chi^2_d}$ is continuous and strictly
increasing on $\mathbb{R}_{\geq 0}$. Both are fully proven in Lean using
Mathlib's `gammaMeasure` infrastructure.

Measurability is also proven (`EquivalenceFoundations.lean:464`):

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

(`EquivalenceFoundations.lean:68`)

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

(`EquivalenceFoundations.lean:73`)

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

(`EquivalenceFoundations.lean:162`)

This uses:

- `sphereUniform d`: normalized surface measure on $S^{d-1}$
  (`EquivalenceFoundations.lean:155`)
- `uniform01`: Lebesgue measure restricted to $[0,1]$
  (`EquivalenceFoundations.lean:98`)

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

(`EquivalenceImportedFacts.lean:34`)

Math: the standard Gaussian $\mathcal{N}(0, I_d)$ restricted to
$\mathbb{R}^d \setminus \{0\}$ (which has full measure).

**Partial match.** The axiom declares `gaussianNZ` directly as a primitive,
with no connection to an ambient Gaussian on `Vec d`. In Python (and in
standard probability), the Gaussian lives on all of $\mathbb{R}^d$ and the
restriction to nonzero vectors is a derived fact ($\gamma_d(\{0\}) = 0$).
Lean is missing the bridge between the two. See Section 10 (Axiom-level gaps).

### 5.2 Direction is uniform on the sphere

```lean
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) (measurable_direction d)
    = sphereUniform d
```

(`EquivalenceImportedFacts.lean:37`)

Math: $Z \sim \mathcal{N}(0, I_d) \Rightarrow Z / \|Z\| \sim \sigma_{d-1}$.

### 5.3 Squared radius is chi-square

```lean
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) (measurable_radiusSq d)
    = chiSqRadiusLaw d
```

(`EquivalenceImportedFacts.lean:41`)

Math: $Z \sim \mathcal{N}(0, I_d) \Rightarrow \|Z\|^2 \sim \chi^2_d$.

### 5.4 Independence of direction and radius

```lean
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d)
      (direction (d := d)) (radiusSq (d := d))
      (measurable_direction d) (measurable_radiusSq d)
```

(`EquivalenceImportedFacts.lean:45`)

Math: $Z / \|Z\| \perp \|Z\|^2$.

### 5.5 Rotation invariance of the sphere measure

```lean
axiom sphereUniform_rotationInvariant (d : ℕ)
    (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d)
      (measurable_rotateSphere O) = sphereUniform d
```

(`EquivalenceImportedFacts.lean:60`)

Math: for any orthogonal $O$, $O_\# \sigma_{d-1} = \sigma_{d-1}$.

---

## 6. CDF-to-Uniform Transform

### 6.1 Forward CDF-to-uniform theorem

Python (`EmbedModels.py:751–752`):

```python
a_df = s.new_tensor(.5 * d_f)
t = torch.special.gammainc(a_df, .5 * s).clamp(eps, 1. - eps)
```

This applies $F_{\chi^2_d}$ to the batch of squared norms `s`. The result `t`
is expected to be approximately uniform on $[0,1]$ when the input is Gaussian.
The Lean theorem formalizes exactly this expectation at the distributional level.

Lean (`EquivalenceFoundations.lean:535`):

```lean
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hF : IsContinuousCDFFor μ F)
    (hFZero : (F 0 : ℝ) = 0) :
    pushforward F μ hFMeas = uniform01 := by ...
```

Math: if $X \sim \mu$ and $F = F_\mu$ is continuous with $F(0)=0$, then

$$F(X) \sim \mathrm{Unif}(0,1).$$

The guard `hFZero` is needed because the domain is $\mathbb{R}_{\geq 0}$
(half-line, not all of $\mathbb{R}$); it is satisfied by `chiSqCDFToUnit d`
for all $d \geq 1$.

Status: **fully proven**.

### 6.2 Reverse CDF-to-law theorem

```lean
theorem probabilityIntegralTransform_reverse
    (targetLaw observedLaw : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hCDF : IsContinuousCDFFor targetLaw F)
    (hStrict : IsStrictlyIncreasingCDFFor targetLaw F)
    (hUniform : pushforward F observedLaw hFMeas = uniform01) :
    observedLaw = targetLaw := by ...
```

(`EquivalenceFoundations.lean:660`)

Math: if $F$ is a continuous, strictly increasing CDF for $\mu$, and
$F(X) \sim \mathrm{Unif}(0,1)$, then $X \sim \mu$.

Python correspondence: the code path computes
`t = torch.special.gammainc(a_df, .5 * s).clamp(eps, 1. - eps)`
(`EmbedModels.py:751–752`) and then penalizes radial non-uniformity via
`rad_loss` (`EmbedModels.py:755–759`). The theorem is the exact converse of
Section 6.1 in the idealized setting: if this CDF-transformed radial variable
is uniform (and the CDF is strictly increasing), then the original radial law
is uniquely identified.

Status: **fully proven**.

---

## 7. The Main Equivalence Theorem

### 7.1 Forward direction

```lean
theorem wristbandEquivalence_forward (d : ℕ) (hDim : 2 ≤ d) :
    wristbandLaw d (gaussianNZ d) = wristbandUniform d := by ...
```

(`Equivalence.lean:515`)

Math: if $Q = \mathcal{N}(0, I_d)$ and $d \geq 2$, then

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1].$$

**Code correspondence.**

- **Same wristband variables.**
  The Lean map $\Phi(z) = \bigl(z/\|z\|,\; F_{\chi^2_d}(\|z\|^2)\bigr)$ matches
  the Python computation in `_Compute`:
  `s = xw.square().sum(...)` (`ml-tidbits/python/embed_models/EmbedModels.py:749`),
  `u = xw * rsqrt(s)` (`ml-tidbits/python/embed_models/EmbedModels.py:750`),
  `t = gammainc(d/2, s/2)` (`ml-tidbits/python/embed_models/EmbedModels.py:752`).

- **Same Gaussian reference mechanism.**
  The theorem is about the Gaussian case (`Q = γ`), and the code calibrates the
  wristband loss by repeatedly sampling Gaussian batches
  (`x_gauss = torch.randn(...)` in `ml-tidbits/python/embed_models/EmbedModels.py:642`).

- **Same target factorization idea.**
  The theorem target is `sphereUniform × uniform01`. In code, this is reflected
  by the separate radial-uniform term (`rad_loss`, lines 755–759) and the
  directional/joint repulsion built on `(u, t)` (lines 761–805), both in
  `ml-tidbits/python/embed_models/EmbedModels.py`.

**Scope difference on dimension (`d`).**

- Lean requires `hDim : 2 ≤ d` in this theorem.
- Python accepts any `d ≥ 1`:
  `d = int(x.shape[-1])` (`ml-tidbits/python/embed_models/EmbedModels.py:693`),
  with early return only for `d < 1`
  (`ml-tidbits/python/embed_models/EmbedModels.py:696`).
- So `d = 1` is executable in Python, but `d = 1` gives `S^0 = {-1,+1}`, a
  discrete directional space. The continuous sphere geometry that drives the
  main argument appears for `d ≥ 2`.
- The practical usage in this repo is also high-dimensional (`embed_dim = 8` in
  `ml-tidbits/python/tests/DeterministicGAE.py:123`).

**Ideal theorem vs implementation details.**

- The Lean theorem is an exact pushforward-law identity.
- The Python code uses finite-batch empirical objectives and numerical
  stabilizers (`clamp_min(eps)` at line 749 and endpoint clamping for `t` at
  line 752), so it is an approximation/optimization surrogate of that ideal
  statement.

Bottom line: the theorem and code align on the core transformation and target
structure; the `d ≥ 2` guard is an intentional formal scope choice, not a
conceptual mismatch.

Status: **fully proven**.

### 7.2 Backward direction

```lean
theorem wristbandEquivalence_backward (d : ℕ) (hDim : 2 ≤ d)
    (Q : Distribution (VecNZ d))
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by ...
```

(`Equivalence.lean:695`)

Math: if $\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1]$ and $d \geq 2$,
then $Q = \mathcal{N}(0, I_d)$.

**Code correspondence.**

- **Same backward target as training objective.**
  The hypothesis `wristbandLaw d Q = wristbandUniform d` is the idealized
  population form of the code goal that wristband features `(u, t)` match the
  uniform wristband target (computed from `u = x/‖x‖`, `t = gammainc(d/2, s/2)`
  at `ml-tidbits/python/embed_models/EmbedModels.py:749–752`).

- **Same radial-identification mechanism.**
  Lean uses reverse PIT (`probabilityIntegralTransform_reverse`) to conclude the
  squared-radius law is `χ²_d` from uniformity of `t`; this is the exact
  population converse of the radial-uniform enforcement used by `rad_loss`
  (`EmbedModels.py:755–759`).

- **Same Gaussian bridge.**
  Lean matches recovered polar data against imported Gaussian polar laws and
  concludes `Q = γ`; in code this corresponds to using Gaussian reference
  samples for calibration (`x_gauss = torch.randn(...)`, `EmbedModels.py:642`).

Status: **fully proven**.

### 7.3 Biconditional

```lean
theorem wristbandEquivalence (d : ℕ) (hDim : 2 ≤ d)
    (Q : Distribution (VecNZ d)) :
    wristbandLaw d Q = wristbandUniform d ↔ Q = gaussianNZ d := ...
```

(`Equivalence.lean:999`)

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
    := by ...
```

(`Equivalence.lean:154`)

Math: if direction is uniform and independent of squared radius, then the
full vector law equals the spherical law built from that radius law.

Code correspondence: there is no direct Python function that reconstructs
`z` from `(u, s)` in the training loop, but this theorem is the formal
identification principle behind the same factorization used by the wristband
pipeline (`u = x/‖x‖`, `s = ‖x‖²`, and CDF-transformed radial coordinate `t`):
once directional law and radial law are fixed under independence, the ambient
vector law is fixed.

Status: **fully proven**.

Proof shape (Lean): rewrite the reconstruction pushforward as
`map radialReconstruct` of the joint pushforward of `(S,U)`, replace that
joint law by a product law via `hIndep`, substitute `hU` for the directional
marginal, and unfold `sphericalLaw`.

### 8.4 Sphere measure is a probability measure

```lean
axiom sphereUniform_isProbability (d : ℕ) :
    IsProbabilityMeasure (((sphereSurface d) Set.univ)⁻¹ • sphereSurface d)
```

(`EquivalenceFoundations.lean:149`)

Math: the sphere $S^{d-1}$ has finite nonzero surface area, so the normalized
surface measure has total mass 1.

Status: **axiom**. Proving this requires showing $0 < \mathcal{H}^{d-1}(S^{d-1}) < \infty$,
which is not yet available in Mathlib.

---

## 9. Kernel Energy Minimization Theorems

This section audits the kernel formalization against the Python implementation
and checks whether it targets the big theorem we want:

- `kernelEnergy_minimized_at_uniform`
- `kernelEnergy_minimizer_unique`

Primary sources for this section:

- Python implementation: `ml-tidbits/python/embed_models/EmbedModels.py`
- Lean formalization: `WristbandLossProofs/KernelFoundations.lean`,
  `WristbandLossProofs/KernelImportedFacts.lean`,
  `WristbandLossProofs/KernelMinimization.lean`

### 9.1 Kernel formula correspondence (Python -> Lean)

Python defines the chordal angular exponent and reflected radial differences:

```python
g = (u @ u.transpose(-1, -2)).clamp(-1., 1.)
e_ang = (2. * self.beta_alpha2) * (g - 1.)
diff0 = tc - tr
diff1 = tc + tr
diff2 = diff1 - 2.
```

and uses them inside the joint repulsion kernel via:

```python
torch.exp(torch.addcmul(e_ang, diff0, diff0, value=-beta))
torch.exp(torch.addcmul(e_ang, diff1, diff1, value=-beta))
torch.exp(torch.addcmul(e_ang, diff2, diff2, value=-beta))
```

Lean mirrors this as:

```lean
def sphereInner {d : ℕ} (u u' : Sphere d) : ℝ := ...
def kernelAngChordal {d : ℕ} (β α : ℝ) (u u' : Sphere d) : ℝ :=
  Real.exp (2 * β * α ^ 2 * (sphereInner u u' - 1))

def kernelRad3Image (β : ℝ) (t t' : UnitInterval) : ℝ :=
  exp (-β * (t - t')^2) + exp (-β * (t + t')^2) + exp (-β * (t + t' - 2)^2)

def wristbandKernel {d : ℕ} (β α : ℝ) (w w' : Wristband d) : ℝ :=
  kernelAngChordal β α w.1 w'.1 * kernelRad3Image β w.2 w'.2
```

Validation:

- **Exact match (chordal mode).**
  `kernelAngChordal` is algebraically identical to
  `exp((2*beta_alpha2)*(g-1))` when `beta_alpha2 = β·α²`.
- **Exact match (3-image radial).**
  `kernelRad3Image` matches `diff0`, `diff1`, `diff2` exactly.
- **Exact match (joint kernel).**
  Python adds exponents before `exp`; Lean multiplies factors afterward.
  These are equivalent.
- **Numerical-stability vs analytic-domain split is intentional.**
  Python uses `clamp` and `eps` for finite-precision robustness; Lean works on
  exact mathematical domains (`Sphere d`, `UnitInterval`) and states the ideal
  population formulas.

### 9.2 Repulsion objective vs population energy

Python global repulsion loss is:

```python
total -= n_f
mean_k = total / (3. * n_f * n_f - n_f)
rep_loss = torch.log(mean_k + eps) / beta
```

Lean defines population kernel energy:

```lean
def kernelEnergy (K : X → X → ℝ) (P : Distribution X) : ℝ :=
  ∫ w, ∫ w', K w w' ∂P ∂P
```

This is the idealized limit of `mean_k` in Python. The following differences are
intentional implementation details in Python, not conceptual mismatches:

- self-pair removal (`total -= n_f` or `row_sum -= 1`)
- finite-batch normalization (`3n^2-n` or `3n-1`)
- `eps` stabilization in `log(mean_k + eps)`

Crucially, the Python loss `rep_loss = (1/β) · log(mean_k + eps)` is a strictly
monotone transformation of `mean_k`, so it has the same minimizers over
distributions as the Lean population energy `E(P) = E_{W,W'~P}[K(W,W')]`.

So the Lean objective is **population-equivalent**, not bitwise-identical to a
finite-batch implementation.

Scope note vs full production loss: `EmbedModels.py` combines repulsion with
radial, angular, and moment terms plus z-score calibration. This theorem track
formalizes the repulsion kernel pathway.

### 9.3 Neumann idealization and truncation bridge

Lean also defines an infinite-series Neumann radial kernel:

```lean
def kernelRadNeumann (β : ℝ) (t t' : UnitInterval) : ℝ := ∑' n : ℤ, ...
def wristbandKernelNeumann {d : ℕ} (β α : ℝ) : Wristband d → Wristband d → ℝ := ...
```

Main theorems are stated for this Neumann kernel because constant
potential is exact there. Python computes only the 3-image truncation.

Lean includes explicit truncation-bridge theorem statements:

```lean
theorem threeImage_approx_neumann ... := by sorry
theorem threeImage_energy_approx ... := by sorry
```

Meaning: the formalization target is correct for the big proof architecture,
but exact transfer from Neumann to 3-image is still a deferred proof.

### 9.4 Imported facts boundary

`KernelImportedFacts.lean` is now **external-only** by construction. It imports
theorem-sized literature facts and no local theorem scaffolding.

Imported axioms:

- PSD block: `kernelAngChordal_posSemiDef`,
  `kernelRadNeumann_hasCosineExpansion`,
  `productKernel_posSemiDef_imported`,
  `kernelRadNeumann_posSemiDef_imported`
- Constant-potential block:
  `neumannPotential_constant_imported`
- Universality/characteristic bridge block:
  `kernelAngChordal_universal`, `kernelRadNeumann_universal`,
  `productKernel_universal`, `universal_implies_characteristic`
- Symmetry/transitivity block:
  `orthogonal_group_transitive_on_sphere`
- MMD block:
  `mmdSq_nonneg`

### 9.5 Main theorem statements and status

```lean
theorem kernelEnergy_minimized_at_uniform ... :
  kernelEnergy (wristbandKernelNeumann β α) P ≥
    kernelEnergy (wristbandKernelNeumann β α) (wristbandUniform d)

theorem kernelEnergy_minimizer_unique ... :
  kernelEnergy (...) P = kernelEnergy (...) (wristbandUniform d) →
  P = wristbandUniform d
```

This is exactly the right mathematical claim for
"energy is minimized at uniform distribution." Current status is **statement
complete, proof deferred** (`sorry`).

Alignment verdict:

- **Python alignment:** yes, for the kernel repulsion term being formalized and
  for the Neumann/3-image proof architecture.
- **Theorem alignment:** yes, the Lean development is aimed at the two target
  theorems above (minimization and uniqueness at uniform).
- **Formal framework strength:** improved by the explicit external/local split;
  remaining risk is proof debt (`sorry`), not ambiguity in formal targets.

---

## 10. What Is Not Yet Formalized/Proven

| Python feature / proof need | Code ref | Lean status |
|----------------------------|----------|-------------|
| Joint repulsion kernel (chordal + 3-image) | `EmbedModels.py` (joint repulsion kernel block) | **Formalized** in `KernelFoundations.lean` (exact formulas) |
| Energy minimization at uniform | population claim | **Stated** in `KernelMinimization.lean`, proofs currently `sorry` |
| 3-image to Neumann transfer bound | `EmbedModels.py` reflected-kernel block vs ideal Neumann | **Stated** (`threeImage_approx_neumann`, `threeImage_energy_approx`), proofs `sorry` |
| Angular-only auxiliary loss | `EmbedModels.py` angular-only loss block | Not formalized yet |
| Radial quantile penalty (Cramér–von Mises) | `EmbedModels.py` radial quantile block | Not formalized yet |
| Moment penalties (`w2`, `kl`, `jeff`) | `EmbedModels.py` moment-penalty block | Not formalized yet |
| Z-score calibration + weighted aggregation | `EmbedModels.py` final aggregation/calibration block | Not formalized yet |
| Geodesic angular branch | `EmbedModels.py` geodesic angular option | Not formalized yet (chordal branch only) |

### Axiom-level gaps

- **Ambient Gaussian bridge.** `gaussianNZ` is axiomatic on nonzero vectors
  (`EquivalenceImportedFacts.lean`) without an explicit derived bridge from
  ambient Gaussian on all of $\mathbb{R}^d$.
- **Kernel external facts.** `KernelImportedFacts.lean` is intentionally
  external-only (literature building blocks as axioms). The project-specific
  kernel consequences that were costly but standard (PSD product closure,
  Neumann PSD, Neumann constant potential) are imported as explicit
  theorem-sized axioms with source links.

### Deferred proofs (`sorry`)

- `WristbandLossProofs/KernelFoundations.lean`: remaining deferred results are
  measurability of `wristbandKernelNeumann`, `integral_tsum_kernelRadNeumann`,
  and cosine-span density on `[0,1]`.
- `WristbandLossProofs/KernelMinimization.lean`: remaining deferred results are
  the two truncation-bridge bounds (`threeImage_approx_neumann`,
  `threeImage_energy_approx`).

Sections 1–8 (equivalence pipeline) remain fully proven; deferred work is now
concentrated in the new kernel files.
