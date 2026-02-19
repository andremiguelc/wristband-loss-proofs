import Mathlib

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Geometry -/

/-- Ambient Euclidean space `ℝ^d`, encoded as `EuclideanSpace ℝ (Fin d)`. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The unit sphere as a subtype, aligned with Mathlib's `Metric.sphere`. -/
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)

/-- Nonzero vectors, used because `z / ‖z‖` is undefined at the origin. -/
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}

/-- The closed unit interval `[0,1]` as a subtype of real numbers. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-- Wristband space: direction coordinate plus radial-percentile coordinate. -/
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval

instance instMeasurableSpaceSphere (d : ℕ) : MeasurableSpace (Sphere d) := by
  unfold Sphere; infer_instance

instance instMeasurableSpaceVecNZ (d : ℕ) : MeasurableSpace (VecNZ d) := by
  unfold VecNZ; infer_instance

instance instMeasurableSpaceUnitInterval : MeasurableSpace UnitInterval := by
  unfold UnitInterval; infer_instance

/-! ## Distributions -/

universe u v w

/-- `Distribution α` means "a probability law on `α`". -/
abbrev Distribution (α : Type u) [MeasurableSpace α] : Type u := ProbabilityMeasure α

/-- Pushforward of a distribution along a random-variable map. -/
abbrev pushforward {α : Type u} {β : Type v} (f : α → β)
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Measurable f → Distribution β
  | μ, hf => μ.map hf.aemeasurable

/-- Product law constructor for independent couplings. -/
def productLaw {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Distribution β → Distribution (α × β)
  | μ, ν => μ.prod ν

/-- Independence encoded by joint law equals product of marginals. -/
def IndepLaw {Ω : Type u} {α : Type v} {β : Type w}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Distribution Ω) (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) : Prop :=
  pushforward (fun ω => (X ω, Y ω)) μ (hX.prodMk hY) =
    productLaw (pushforward X μ hX) (pushforward Y μ hY)

/-- Uniform law on `[0,1]`. -/
def uniform01 : Distribution UnitInterval :=
  ⟨(volume : Measure UnitInterval), by infer_instance⟩

/-- Squared radius of a nonzero vector, stored in nonnegative reals. -/
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal :=
  ⟨‖z.1‖ ^ 2, by positivity⟩

/-- Measurability of `radiusSq`. -/
lemma measurable_radiusSq (d : ℕ) : Measurable (radiusSq (d := d)) := by
  unfold radiusSq
  refine Measurable.subtype_mk ?_
  simpa using ((continuous_norm.pow 2).measurable.comp measurable_subtype_coe)

/-- Direction map `z ↦ z / ‖z‖` into the unit sphere. -/
noncomputable def direction {d : ℕ} (z : VecNZ d) : Sphere d := by
  refine ⟨(‖z.1‖)⁻¹ • z.1, ?_⟩
  have hz : ‖z.1‖ ≠ 0 := norm_ne_zero_iff.mpr z.2
  have hnorm : ‖(‖z.1‖)⁻¹ • z.1‖ = 1 := by
    calc
      ‖(‖z.1‖)⁻¹ • z.1‖ = ‖(‖z.1‖)⁻¹‖ * ‖z.1‖ := norm_smul _ _
      _ = (‖z.1‖)⁻¹ * ‖z.1‖ := by simp
      _ = 1 := by simp [hz]
  simpa [Metric.mem_sphere, dist_eq_norm] using hnorm

/-- Measurability of `direction`. -/
lemma measurable_direction (d : ℕ) : Measurable (direction (d := d)) := by
  unfold direction
  refine Measurable.subtype_mk ?_
  exact ((measurable_norm.comp measurable_subtype_coe).inv.smul measurable_subtype_coe)

/-! ## Sphere Measure -/

/-- Surface measure on the unit sphere induced from ambient `volume`. -/
noncomputable def sphereSurface (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (Vec d)).toSphere

/--
Uniform sphere law as normalized surface measure.

This is the ambient-surface measure scaled by inverse total mass.
-/
axiom sphereUniform_isProbability
    (d : ℕ) :
    IsProbabilityMeasure (((sphereSurface d) Set.univ)⁻¹ • sphereSurface d)

noncomputable def sphereUniform (d : ℕ) : Distribution (Sphere d) :=
  ⟨((sphereSurface d) Set.univ)⁻¹ • sphereSurface d, sphereUniform_isProbability d⟩

/-- Target wristband law `μ₀ = σ_{d-1} ⊗ λ`. -/
def wristbandUniform (d : ℕ) : Distribution (Wristband d) :=
  productLaw (sphereUniform d) uniform01

/-- Rotate a point on the sphere via a linear isometric equivalence. -/
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

/-! ## CDF and PIT Definitions -/

/-- A concrete CDF-on-`NNReal` associated to a measure `μ` on `NNReal`. -/
noncomputable def cdfNNReal (μ : Distribution NNReal) (x : NNReal) : ℝ :=
  ((μ : Measure NNReal) (Set.Iic x)).toReal

/-- `F` is the CDF of `μ` and is continuous. -/
def IsContinuousCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ Continuous (fun x => (F x : ℝ))

/-- `F` is the CDF of `μ` and is strictly increasing. -/
def IsStrictlyIncreasingCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ StrictMono (fun x => (F x : ℝ))

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

/--
If `X` has continuous CDF `F`, then `F(X)` has uniform law on `[0,1]`.
-/
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hFMeas : Measurable F)
    (hF : IsContinuousCDFFor μ F) :
    pushforward F μ hFMeas = uniform01 := by
  -- Deferred in this pass: concrete CDF formalization details.
  sorry

/--
Reverse PIT used in the backward direction of Wristband Equivalence.

If `F(X)` is uniform and `F` is the strictly increasing CDF of `targetLaw`,
then `X` must follow `targetLaw`.
-/
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
