import Mathlib

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Geometry

These types encode the domain and codomain of the wristband map `Φ`.

Python side (`ml-tidbits/.../EmbedModels.py`):
- A sample is a vector `x` (tensor with last dim = `d`).
- The wristband map sends `x ↦ (u, t)` where `u = x/‖x‖` and `t = F_{χ²_d}(‖x‖²)`.

Lean encodes these as subtypes of Euclidean space and the unit interval.
-/

/-- Ambient Euclidean space `ℝ^d`, encoded as `EuclideanSpace ℝ (Fin d)`.
    Python: a single sample vector of dimension `d`. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The unit sphere `S^{d-1}` as a subtype, aligned with Mathlib's `Metric.sphere`.
    Python: the direction `u = x / ‖x‖` lives here. -/
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)

/-- Nonzero vectors `ℝ^d \ {0}`, used because `z / ‖z‖` is undefined at the origin.
    This is the domain of the wristband map `Φ`. -/
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}

/-- The closed unit interval `[0,1]` as a subtype of real numbers.
    Python: the radial percentile `t = F_{χ²_d}(‖x‖²)` lives here. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-- Wristband space `S^{d-1} × [0,1]`: direction coordinate plus radial-percentile coordinate.
    This is the codomain of the wristband map `Φ(z) = (direction(z), CDF(‖z‖²))`. -/
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval

instance instMeasurableSpaceSphere (d : ℕ) : MeasurableSpace (Sphere d) := by
  unfold Sphere; infer_instance

instance instMeasurableSpaceVecNZ (d : ℕ) : MeasurableSpace (VecNZ d) := by
  unfold VecNZ; infer_instance

instance instMeasurableSpaceUnitInterval : MeasurableSpace UnitInterval := by
  unfold UnitInterval; infer_instance

/-! ## Distributions

`Distribution α` wraps Mathlib's `ProbabilityMeasure α`, which carries a proof
that the total mass is 1. This replaces the earlier design where `Distribution`
was a raw `Measure` alias and probability had to be tracked separately.

Key operations:
- `pushforward f μ hf`: law of `f(X)` when `X ~ μ`. Python analogy: feeding a
  batch through a map and looking at the output distribution.
- `productLaw μ ν`: joint law of independent `(X, Y)`.
- `IndepLaw`: `X ⊥ Y` iff joint law = product of marginals.
-/

universe u v w

/-- `Distribution α` means "a probability law on `α`".
    Wraps `ProbabilityMeasure α` so total mass = 1 is enforced by the type. -/
abbrev Distribution (α : Type u) [MeasurableSpace α] : Type u := ProbabilityMeasure α

/-- Pushforward of a distribution along a random-variable map.
    Math: if `X ~ μ`, then `f(X) ~ pushforward f μ`.
    Python analogy: applying `wristbandMap` to a batch transforms the distribution. -/
abbrev pushforward {α : Type u} {β : Type v} (f : α → β)
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Measurable f → Distribution β
  | μ, hf => μ.map hf.aemeasurable

/-- Product law constructor for independent couplings.
    Math: `μ ⊗ ν`, the joint law when the two coordinates are independent. -/
def productLaw {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Distribution β → Distribution (α × β)
  | μ, ν => μ.prod ν

/-- Independence encoded by: joint law of `(X, Y)` equals product of marginals.
    Math: `X ⊥ Y` iff `Law(X, Y) = Law(X) ⊗ Law(Y)`. -/
def IndepLaw {Ω : Type u} {α : Type v} {β : Type w}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Distribution Ω) (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) : Prop :=
  pushforward (fun ω => (X ω, Y ω)) μ (hX.prodMk hY) =
    productLaw (pushforward X μ hX) (pushforward Y μ hY)

/-- Uniform (Lebesgue) law on `[0,1]`.
    This is the target marginal for the radial percentile coordinate `t`.
    Python: the radial quantile loss compares sorted `t` values against
    uniform quantiles `q_i = (i - 0.5) / n` (EmbedModels.py:757). -/
def uniform01 : Distribution UnitInterval :=
  ⟨(volume : Measure UnitInterval), by infer_instance⟩

/-- Squared radius of a nonzero vector: `s(z) = ‖z‖²`, stored in `ℝ≥0`.
    Python: `s = xw.square().sum(dim=-1)` (EmbedModels.py:749). -/
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal :=
  ⟨‖z.1‖ ^ 2, by positivity⟩

/-- Measurability of `radiusSq` — needed for pushforward constructions. -/
lemma measurable_radiusSq (d : ℕ) : Measurable (radiusSq (d := d)) := by
  unfold radiusSq
  refine Measurable.subtype_mk ?_
  simpa using ((continuous_norm.pow 2).measurable.comp measurable_subtype_coe)

/-- Direction map `z ↦ z / ‖z‖` into the unit sphere.
    Python: `u = xw * torch.rsqrt(s)[..., :, None]` (EmbedModels.py:750). -/
noncomputable def direction {d : ℕ} (z : VecNZ d) : Sphere d := by
  refine ⟨(‖z.1‖)⁻¹ • z.1, ?_⟩
  have hz : ‖z.1‖ ≠ 0 := norm_ne_zero_iff.mpr z.2
  have hnorm : ‖(‖z.1‖)⁻¹ • z.1‖ = 1 := by
    calc
      ‖(‖z.1‖)⁻¹ • z.1‖ = ‖(‖z.1‖)⁻¹‖ * ‖z.1‖ := norm_smul _ _
      _ = (‖z.1‖)⁻¹ * ‖z.1‖ := by simp
      _ = 1 := by simp [hz]
  simpa [Metric.mem_sphere, dist_eq_norm] using hnorm

/-- Measurability of `direction` — needed for pushforward constructions. -/
lemma measurable_direction (d : ℕ) : Measurable (direction (d := d)) := by
  unfold direction
  refine Measurable.subtype_mk ?_
  exact ((measurable_norm.comp measurable_subtype_coe).inv.smul measurable_subtype_coe)

/-! ## Sphere Measure

The uniform law on `S^{d-1}` is the target marginal for the direction coordinate.
We construct it by normalizing the ambient surface measure (Hausdorff measure
restricted to the sphere) so total mass is 1.

Axiom: `sphereUniform_isProbability` — the normalized surface measure is a
probability measure. Proving this from scratch would require showing the sphere
has finite nonzero surface area, which is nontrivial in Mathlib currently.
-/

/-- Surface measure on the unit sphere induced from ambient `volume`.
    Uses Mathlib's `Measure.toSphere` which restricts the ambient Hausdorff measure. -/
noncomputable def sphereSurface (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (Vec d)).toSphere

/-- **Axiom**: the normalized sphere surface measure has total mass 1.
    This is the only axiom in Foundations.lean. It asserts that `S^{d-1}` has
    finite nonzero surface area so normalization produces a probability measure. -/
axiom sphereUniform_isProbability
    (d : ℕ) :
    IsProbabilityMeasure (((sphereSurface d) Set.univ)⁻¹ • sphereSurface d)

/-- Uniform probability law on the unit sphere `S^{d-1}`.
    Math: `σ_{d-1}`, the normalized surface measure. -/
noncomputable def sphereUniform (d : ℕ) : Distribution (Sphere d) :=
  ⟨((sphereSurface d) Set.univ)⁻¹ • sphereSurface d, sphereUniform_isProbability d⟩

/-- Target wristband law `μ₀ = σ_{d-1} ⊗ Unif[0,1]`.
    This is the "ideal" distribution on wristband space: direction is uniform on
    the sphere and the radial percentile is uniform on `[0,1]`, independently.
    Python: the wristband loss drives the embedding distribution toward this target. -/
def wristbandUniform (d : ℕ) : Distribution (Wristband d) :=
  productLaw (sphereUniform d) uniform01

/-- Rotate a point on the sphere via a linear isometric equivalence.
    Used in the rotation-invariance proof for spherical laws. -/
def rotateSphere {d : ℕ} (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) (u : Sphere d) : Sphere d := by
  refine ⟨O u.1, ?_⟩
  have hu : ‖u.1‖ = 1 := by simp
  have hOu : ‖O u.1‖ = 1 := by
    calc ‖O u.1‖ = ‖u.1‖ := O.norm_map u.1
      _ = 1 := hu
  simp [hOu]

/-- Measurability of sphere rotations. -/
lemma measurable_rotateSphere {d : ℕ} (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    Measurable (rotateSphere O) := by
  unfold rotateSphere
  refine Measurable.subtype_mk ?_
  simpa [Function.comp] using
    (O.continuous.comp continuous_subtype_val).measurable

/-! ## CDF and PIT Definitions

These predicates formalize what it means for `F` to be "the CDF" of a law `μ`.
They are used by the Probability Integral Transform (PIT) theorems below.

The CDF is the key bridge between the squared-radius law and the radial
percentile coordinate. In Python:
  `t = torch.special.gammainc(d/2, s/2)` (EmbedModels.py:752)
computes the chi-square CDF value, which is exactly what `chiSqCDFToUnit` does
in Lean.
-/

/-- CDF of a probability law on `ℝ≥0`, evaluated at `x`: `F(x) = μ((-∞, x])`.
    Returns a real number (will be in `[0,1]` for probability measures). -/
noncomputable def cdfNNReal (μ : Distribution NNReal) (x : NNReal) : ℝ :=
  ((μ : Measure NNReal) (Set.Iic x)).toReal

/-- Predicate: `F` is the CDF of `μ` and is continuous.
    Used as the hypothesis for the forward PIT (`F(X) ~ Unif[0,1]`). -/
def IsContinuousCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ Continuous (fun x => (F x : ℝ))

/-- Predicate: `F` is the CDF of `μ` and is strictly increasing.
    Used as the hypothesis for the reverse PIT (`F(X) ~ Unif ⟹ X ~ μ`). -/
def IsStrictlyIncreasingCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ StrictMono (fun x => (F x : ℝ))

/-! ## Chi-Square CDF Bridge (Mathlib)

This section builds the chi-square radius law and its CDF from Mathlib's
`gammaMeasure`, replacing what were previously axioms.

**Mathematical background:**
The chi-square distribution with `d` degrees of freedom is a Gamma distribution
with shape `α = d/2` and rate `β = 1/2`:
  `χ²_d = Gamma(d/2, 1/2)`.

**Python correspondence:**
  `torch.special.gammainc(d/2, s/2)` (EmbedModels.py:752)
computes the regularized lower incomplete gamma function, which is exactly the
CDF of `Gamma(d/2, 1/2)` evaluated at `s`. So `gammainc(d/2, s/2) = F_{χ²_d}(s)`.

**Construction pipeline:**
1. `chiSqMeasureR d` — gamma measure on `ℝ` with parameters `(d/2, 1/2)`.
2. `chiSqRadiusMeasurePos d` — pushforward to `ℝ≥0` via `Real.toNNReal`.
3. `chiSqRadiusLaw d` — wrapped as a `ProbabilityMeasure NNReal`.
4. `chiSqCDFToUnit d` — CDF map `ℝ≥0 → [0,1]` using Mathlib's `ProbabilityTheory.cdf`.

**What was proved (previously axioms):**
- `chiSqCDFToUnit_isContinuousCDF` — CDF is continuous (via no-atoms of gamma).
- `chiSqCDFToUnit_isStrictlyIncreasingCDF` — CDF is strictly increasing
  (via positive density on all intervals).
-/

/-- Chi-square shape parameter `α = d/2`, expressed over reals.
    Python: the first argument to `gammainc(d/2, ...)`. -/
noncomputable def chiSqShape (d : ℕ) : ℝ := (d : ℝ) / 2

/-- Chi-square rate parameter `β = 1/2`.
    Combined with shape `d/2`, this gives `Gamma(d/2, 1/2) = χ²_d`. -/
noncomputable def chiSqRate : ℝ := (1 : ℝ) / 2

/-- Shape parameter is positive when `d ≥ 1`. -/
lemma chiSqShape_pos (d : ℕ) (hDim : 1 ≤ d) : 0 < chiSqShape d := by
  have hdNat : 0 < d := Nat.succ_le_iff.mp hDim
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdNat
  unfold chiSqShape
  exact div_pos hd (by norm_num)

/-- Rate parameter `1/2` is positive. -/
lemma chiSqRate_pos : 0 < chiSqRate := by
  norm_num [chiSqRate]

/-- Chi-square measure on `ℝ`, realized as `gammaMeasure(d/2, 1/2)`.
    This is a measure on all of `ℝ` (concentrated on `[0,∞)`). -/
noncomputable def chiSqMeasureR (d : ℕ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (chiSqShape d) chiSqRate

/-- Pushforward of the real-valued chi-square measure to `ℝ≥0` via `Real.toNNReal`.
    Since `χ²` is supported on `[0,∞)`, this loses no mass. -/
noncomputable def chiSqRadiusMeasurePos (d : ℕ) : Measure NNReal :=
  Measure.map Real.toNNReal (chiSqMeasureR d)

/-- Chi-square radius law as a probability measure on `ℝ≥0`, for `d ≥ 1`.
    Wraps the pushed-forward gamma measure with a proof that it has total mass 1. -/
noncomputable def chiSqRadiusLawPos (d : ℕ) (hDim : 1 ≤ d) : Distribution NNReal := by
  have hProbR : IsProbabilityMeasure (chiSqMeasureR d) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (chiSqShape_pos d hDim) chiSqRate_pos
  have hProbNN : IsProbabilityMeasure (chiSqRadiusMeasurePos d) := by
    letI : IsProbabilityMeasure (chiSqMeasureR d) := hProbR
    simpa [chiSqRadiusMeasurePos] using
      (Measure.isProbabilityMeasure_map (μ := chiSqMeasureR d) measurable_real_toNNReal.aemeasurable)
  exact ⟨chiSqRadiusMeasurePos d, hProbNN⟩

/-- Chi-square radius law on `ℝ≥0` for all `d : ℕ`.
    For `d ≥ 1`: the gamma-based law (`chiSqRadiusLawPos`).
    For `d = 0`: a degenerate Dirac mass at `0` (fallback so the definition is total).

    Previously an axiom; now a concrete definition backed by Mathlib's `gammaMeasure`. -/
noncomputable def chiSqRadiusLaw (d : ℕ) : Distribution NNReal :=
  if hDim : 1 ≤ d then
    chiSqRadiusLawPos d hDim
  else
    ⟨Measure.dirac (0 : NNReal), by infer_instance⟩

/-- Simp lemma: for `d ≥ 1`, `chiSqRadiusLaw` unfolds to the gamma-based version. -/
@[simp] lemma chiSqRadiusLaw_eq_pos (d : ℕ) (hDim : 1 ≤ d) :
    chiSqRadiusLaw d = chiSqRadiusLawPos d hDim := by
  simp [chiSqRadiusLaw, hDim]

/-- Technical lemma: the preimage of `[0, x]` under `toNNReal` is `(-∞, x]`.
    This works because `toNNReal` clamps negatives to `0 ≤ x`. -/
lemma preimage_toNNReal_Iic (x : NNReal) :
    (Real.toNNReal ⁻¹' Set.Iic x) = Set.Iic (x : ℝ) := by
  ext t
  simp [Real.toNNReal_le_iff_le_coe]

/-- The pushed-forward `NNReal` measure on `[0, x]` equals the real gamma measure
    on `(-∞, x]`. Bridge between the two worlds. -/
lemma chiSqRadiusMeasurePos_apply_Iic (d : ℕ) (x : NNReal) :
    chiSqRadiusMeasurePos d (Set.Iic x) = chiSqMeasureR d (Set.Iic (x : ℝ)) := by
  rw [chiSqRadiusMeasurePos, Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  simp [preimage_toNNReal_Iic]

/-- **Key bridge lemma**: our `cdfNNReal` of the `NNReal` chi-square law equals
    Mathlib's `ProbabilityTheory.cdf` of the real-valued gamma measure.
    This connects our CDF definition to Mathlib's CDF infrastructure. -/
lemma cdfNNReal_chiSqRadiusLawPos_eq_cdf (d : ℕ) (hDim : 1 ≤ d) (x : NNReal) :
    cdfNNReal (chiSqRadiusLawPos d hDim) x = ProbabilityTheory.cdf (chiSqMeasureR d) x := by
  have hProbR : IsProbabilityMeasure (chiSqMeasureR d) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (chiSqShape_pos d hDim) chiSqRate_pos
  rw [cdfNNReal]
  change (chiSqRadiusMeasurePos d (Set.Iic x)).toReal = ProbabilityTheory.cdf (chiSqMeasureR d) x
  rw [chiSqRadiusMeasurePos_apply_Iic]
  simpa [MeasureTheory.measureReal_def] using
    (ProbabilityTheory.cdf_eq_real (μ := chiSqMeasureR d) (x := (x : ℝ))).symm

/-- **Positive mass on intervals**: the gamma measure assigns positive mass to
    every nonempty interval `(x, y]` with `0 ≤ x < y`.
    This is the engine behind strict monotonicity of the CDF: if `x < y` then
    `F(y) - F(x) = μ((x,y]) > 0`, so `F(x) < F(y)`. -/
lemma gammaMeasure_Ioc_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {x y : NNReal} (hxy : x < y) :
    0 < (ProbabilityTheory.gammaMeasure a r) (Set.Ioc (x : ℝ) (y : ℝ)) := by
  rw [ProbabilityTheory.gammaMeasure, withDensity_apply _ measurableSet_Ioc]
  have hMeasGamma : Measurable (ProbabilityTheory.gammaPDF a r) := by
    simpa [ProbabilityTheory.gammaPDF] using
      ((ProbabilityTheory.measurable_gammaPDFReal a r).ennreal_ofReal)
  rw [MeasureTheory.setLIntegral_pos_iff hMeasGamma]
  have hxyR : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hIoo :
      Set.Ioo (x : ℝ) (y : ℝ) ⊆
        Function.support (ProbabilityTheory.gammaPDF a r) ∩ Set.Ioc (x : ℝ) (y : ℝ) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt (by exact_mod_cast x.2) ht.1
    have ht_pdf_pos_real : 0 < ProbabilityTheory.gammaPDFReal a r t :=
      ProbabilityTheory.gammaPDFReal_pos ha hr ht_pos
    have ht_pdf_pos : 0 < ProbabilityTheory.gammaPDF a r t := by
      unfold ProbabilityTheory.gammaPDF
      exact ENNReal.ofReal_pos.mpr ht_pdf_pos_real
    refine ⟨?_, ?_⟩
    · simpa [Function.mem_support, ht_pdf_pos.ne']
    · exact ⟨ht.1, ht.2.le⟩
  have hvolIoo : 0 < (volume (Set.Ioo (x : ℝ) (y : ℝ))) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxyR)
  exact lt_of_lt_of_le hvolIoo (measure_mono hIoo)

/-- **CDF continuity for gamma measures**: the CDF `F(x) = μ((-∞, x])` is
    continuous on all of `ℝ`.
    Proof idea: gamma measures have no atoms (since they're absolutely continuous
    w.r.t. Lebesgue measure via `withDensity`), so the CDF has no jumps.
    A monotone function with no jumps is continuous. -/
lemma continuous_cdf_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Continuous (fun x : ℝ => (ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r)) x) := by
  let μ : Measure ℝ := ProbabilityTheory.gammaMeasure a r
  have hProb : IsProbabilityMeasure μ := ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha hr
  have hMono : Monotone (ProbabilityTheory.cdf μ) := ProbabilityTheory.monotone_cdf μ
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  rw [hMono.continuousAt_iff_leftLim_eq_rightLim]
  have hNoAtoms : NoAtoms μ := by
    simpa [μ, ProbabilityTheory.gammaMeasure] using
      (MeasureTheory.noAtoms_withDensity (μ := (volume : Measure ℝ)) (ProbabilityTheory.gammaPDF a r))
  have hSingletonZero : (ProbabilityTheory.cdf μ).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf μ]
    simpa [μ] using (NoAtoms.measure_singleton (μ := μ) x)
  have hLeZero : (ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x) ≤ 0 := by
    have hOfRealZero : ENNReal.ofReal
        (ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x) = 0 := by
      have hSingleton :
          (ProbabilityTheory.cdf μ).measure {x} = ENNReal.ofReal
            (ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x) :=
        StieltjesFunction.measure_singleton (ProbabilityTheory.cdf μ) x
      rw [hSingletonZero] at hSingleton
      simpa using hSingleton.symm
    exact ENNReal.ofReal_eq_zero.mp hOfRealZero
  have hLeftLe : Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x :=
    Monotone.leftLim_le hMono (le_rfl : x ≤ x)
  have hValLe : ProbabilityTheory.cdf μ x ≤ Function.leftLim (ProbabilityTheory.cdf μ) x := by
    linarith
  have hLeftEq : Function.leftLim (ProbabilityTheory.cdf μ) x = ProbabilityTheory.cdf μ x :=
    le_antisymm hLeftLe hValLe
  rw [StieltjesFunction.rightLim_eq, hLeftEq]

/-- **CDF strict monotonicity for gamma measures** (restricted to `ℝ≥0`):
    if `0 ≤ x < y`, then `F(x) < F(y)`.
    Proof: `F(y) - F(x) = μ((x,y]) > 0` by `gammaMeasure_Ioc_pos`. -/
lemma strictMono_cdf_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    StrictMono (fun x : NNReal => ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r) x) := by
  intro x y hxy
  have hProb : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure a r) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha hr
  have hIocPos : 0 < (ProbabilityTheory.gammaMeasure a r) (Set.Ioc (x : ℝ) (y : ℝ)) :=
    gammaMeasure_Ioc_pos ha hr hxy
  have hMeasureEq :
      (ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r)).measure =
        ProbabilityTheory.gammaMeasure a r :=
    ProbabilityTheory.measure_cdf (μ := ProbabilityTheory.gammaMeasure a r)
  have hIocPosCdf :
      0 < (ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r)).measure
            (Set.Ioc (x : ℝ) (y : ℝ)) := by
    simpa [hMeasureEq] using hIocPos
  have hDiffPosENN :
      0 < ENNReal.ofReal
        (ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r) y -
          ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r) x) := by
    simpa [StieltjesFunction.measure_Ioc] using hIocPosCdf
  have hDiffPos :
      0 <
        (ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r) y -
          ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure a r) x) :=
    ENNReal.ofReal_pos.mp hDiffPosENN
  linarith

/-- Specialization: chi-square CDF is continuous on `ℝ`. -/
lemma continuous_cdf_chiSqMeasureR (d : ℕ) (hDim : 1 ≤ d) :
    Continuous (fun x : ℝ => ProbabilityTheory.cdf (chiSqMeasureR d) x) := by
  simpa [chiSqMeasureR] using
    (continuous_cdf_gammaMeasure (a := chiSqShape d) (r := chiSqRate)
      (chiSqShape_pos d hDim) chiSqRate_pos)

/-- Specialization: chi-square CDF is continuous when restricted to `ℝ≥0`. -/
lemma continuous_cdf_chiSqMeasureR_onNNReal (d : ℕ) (hDim : 1 ≤ d) :
    Continuous (fun x : NNReal => ProbabilityTheory.cdf (chiSqMeasureR d) x) := by
  exact (continuous_cdf_chiSqMeasureR d hDim).comp continuous_subtype_val

/-- Specialization: chi-square CDF is strictly increasing on `ℝ≥0`. -/
lemma strictMono_cdf_chiSqMeasureR (d : ℕ) (hDim : 1 ≤ d) :
    StrictMono (fun x : NNReal => ProbabilityTheory.cdf (chiSqMeasureR d) x) := by
  simpa [chiSqMeasureR] using
    (strictMono_cdf_gammaMeasure (a := chiSqShape d) (r := chiSqRate)
      (chiSqShape_pos d hDim) chiSqRate_pos)

/-- Chi-square CDF as a map `ℝ≥0 → [0,1]` for `d ≥ 1`.
    This wraps Mathlib's `ProbabilityTheory.cdf` with a proof that values lie in `[0,1]`.
    Python: `torch.special.gammainc(d/2, s/2)` (EmbedModels.py:752).
    Previously an axiom; now a concrete definition. -/
noncomputable def chiSqCDFToUnitPos (d : ℕ) (_hDim : 1 ≤ d) : NNReal → UnitInterval :=
  fun x =>
    ⟨ProbabilityTheory.cdf (chiSqMeasureR d) x,
      ⟨ProbabilityTheory.cdf_nonneg (μ := chiSqMeasureR d) (x := x),
        ProbabilityTheory.cdf_le_one (μ := chiSqMeasureR d) (x := x)⟩⟩

/-- Chi-square CDF map `ℝ≥0 → [0,1]` for all dimensions.
    For `d ≥ 1`: the gamma-based CDF (`chiSqCDFToUnitPos`).
    For `d = 0`: constant `0` (fallback so the definition is total).
    Previously an axiom; now a concrete definition backed by Mathlib. -/
noncomputable def chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval :=
  if hDim : 1 ≤ d then
    chiSqCDFToUnitPos d hDim
  else
    fun _ => ⟨0, by simp⟩

/-- Simp lemma: for `d ≥ 1`, `chiSqCDFToUnit` unfolds to the gamma-based version. -/
@[simp] lemma chiSqCDFToUnit_eq_pos (d : ℕ) (hDim : 1 ≤ d) :
    chiSqCDFToUnit d = chiSqCDFToUnitPos d hDim := by
  simp [chiSqCDFToUnit, hDim]

/-- Measurability of `chiSqCDFToUnit` — needed for pushforward constructions.
    Previously an axiom; now proven from CDF continuity. -/
lemma chiSqCDFToUnit_measurable (d : ℕ) : Measurable (chiSqCDFToUnit d) := by
  by_cases hDim : 1 ≤ d
  · rw [chiSqCDFToUnit_eq_pos d hDim]
    refine Measurable.subtype_mk ?_
    simpa [chiSqCDFToUnitPos] using (continuous_cdf_chiSqMeasureR_onNNReal d hDim).measurable
  · simp [chiSqCDFToUnit, hDim]

/-- The `chiSqCDFToUnitPos` function agrees with `cdfNNReal` of the chi-square law.
    This is the pointwise bridge between our CDF definition and the measure-theoretic CDF. -/
lemma chiSqCDFToUnitPos_eq_cdfNNReal (d : ℕ) (hDim : 1 ≤ d) (x : NNReal) :
    ((chiSqCDFToUnitPos d hDim x : UnitInterval) : ℝ) =
      cdfNNReal (chiSqRadiusLawPos d hDim) x := by
  simpa [chiSqCDFToUnitPos] using (cdfNNReal_chiSqRadiusLawPos_eq_cdf d hDim x).symm

/-- **CDF contract (continuity)**: `chiSqCDFToUnit` is the continuous CDF of
    `chiSqRadiusLaw` when `d ≥ 1`.
    This was listed as **missing** in the audit (section 4.1); now proven.
    Needed by the forward PIT to conclude `F(X) ~ Unif[0,1]`. -/
theorem chiSqCDFToUnit_isContinuousCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [chiSqRadiusLaw_eq_pos d hDim, chiSqCDFToUnit_eq_pos d hDim]
    exact chiSqCDFToUnitPos_eq_cdfNNReal d hDim x
  · rw [chiSqCDFToUnit_eq_pos d hDim]
    simpa [chiSqCDFToUnitPos] using (continuous_cdf_chiSqMeasureR_onNNReal d hDim)

/-- **CDF contract (strict monotonicity)**: `chiSqCDFToUnit` is a strictly
    increasing CDF of `chiSqRadiusLaw` when `d ≥ 1`.
    This was listed as **missing** in the audit (section 4.1); now proven.
    Needed by the reverse PIT to conclude `F(X) ~ Unif ⟹ X ~ χ²`. -/
theorem chiSqCDFToUnit_isStrictlyIncreasingCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [chiSqRadiusLaw_eq_pos d hDim, chiSqCDFToUnit_eq_pos d hDim]
    exact chiSqCDFToUnitPos_eq_cdfNNReal d hDim x
  · rw [chiSqCDFToUnit_eq_pos d hDim]
    simpa [chiSqCDFToUnitPos] using (strictMono_cdf_chiSqMeasureR d hDim)

/-!
### Probability Integral Transform

Theorem shape tracked here:
\[
  X \sim F \ \text{continuous} \implies U := F(X) \sim \mathrm{Unif}(0,1).
\]
Conversely, with generalized inverse \(F^{-1}\):
\[
  U \sim \mathrm{Unif}(0,1) \implies F^{-1}(U) \sim F.
\]

External bibliography:
- Lancaster University. *MATH230 Notes*, "Probability Integral Transformation" (Theorem 4.3.1).
  https://www.lancaster.ac.uk/~prendivs/accessible/math230/math230_notes.tex/Ch4.S3.html
-/

/-- **Probability Integral Transform (forward direction).**
    If `X ~ μ` and `F` is the continuous CDF of `μ`, then `F(X) ~ Unif[0,1]`.

    Application to wristband: with `X = ‖Z‖²` (chi-square) and `F = chiSqCDFToUnit`,
    this gives `t = F(‖Z‖²) ~ Unif[0,1]`, which is the radial percentile coordinate.

    Proof status: deferred (`sorry`). This is a classical result; formalization
    requires careful handling of measure-theoretic CDF inversion. -/
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hF : IsContinuousCDFFor μ F) :
    pushforward F μ hFMeas = uniform01 := by
  -- Deferred in this pass: concrete CDF formalization details.
  sorry

/-- **Probability Integral Transform (reverse direction).**
    If `F(X) ~ Unif[0,1]` and `F` is a strictly increasing continuous CDF of
    `targetLaw`, then `X ~ targetLaw`.

    Application to wristband (backward direction): if the radial percentile is
    uniform, the squared-radius must follow the chi-square law.

    Proof status: deferred (`sorry`). Needs generalized inverse / quantile function. -/
theorem probabilityIntegralTransform_reverse
    (targetLaw observedLaw : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hCDF : IsContinuousCDFFor targetLaw F)
    (hStrict : IsStrictlyIncreasingCDFFor targetLaw F)
    (hUniform : pushforward F observedLaw hFMeas = uniform01) :
    observedLaw = targetLaw := by
  -- Deferred for the same reason as `probabilityIntegralTransform`.
  sorry

end WristbandLossProofs
