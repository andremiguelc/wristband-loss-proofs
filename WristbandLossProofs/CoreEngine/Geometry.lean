import Mathlib

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Basic Geometric Types -/

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
  unfold Sphere
  infer_instance

instance instMeasurableSpaceVecNZ (d : ℕ) : MeasurableSpace (VecNZ d) := by
  unfold VecNZ
  infer_instance

instance instMeasurableSpaceUnitInterval : MeasurableSpace UnitInterval := by
  unfold UnitInterval
  infer_instance

/-! ## Concrete Distribution Interface (Mathlib Measures) -/

universe u v w

/-- `Distribution α` means "a law on `α`". -/
abbrev Distribution (α : Type u) [MeasurableSpace α] : Type u := Measure α

/-- Pushforward of a distribution along a random-variable map. -/
def pushforward {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    (α → β) → Distribution α → Distribution β
  | f, μ => Measure.map f μ

/-- Product law constructor for independent couplings. -/
def productLaw {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Distribution β → Distribution (α × β)
  | μ, ν => μ.prod ν

/-- Independence encoded by joint law equals product of marginals. -/
def IndepLaw {Ω : Type u} {α : Type v} {β : Type w}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Distribution Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  pushforward (fun ω => (X ω, Y ω)) μ =
    productLaw (pushforward X μ) (pushforward Y μ)

/-- Uniform law on `[0,1]`. -/
def uniform01 : Distribution UnitInterval := (volume : Measure UnitInterval)

/-- Squared radius of a nonzero vector, stored in nonnegative reals. -/
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal :=
  ⟨‖z.1‖ ^ 2, by positivity⟩

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

end WristbandLossProofs
