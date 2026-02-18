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

/-! ## Sphere Measure -/

/-- Surface measure on the unit sphere induced from ambient `volume`. -/
noncomputable def sphereSurface (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (Vec d)).toSphere

/--
Uniform sphere law as normalized surface measure.

This is the ambient-surface measure scaled by inverse total mass.
-/
noncomputable def sphereUniform (d : ℕ) : Distribution (Sphere d) :=
  let μs : Measure (Sphere d) := sphereSurface d
  (μs Set.univ)⁻¹ • μs

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

/-! ## CDF and PIT Definitions -/

/-- A concrete CDF-on-`NNReal` associated to a measure `μ` on `NNReal`. -/
noncomputable def cdfNNReal (μ : Distribution NNReal) (x : NNReal) : ℝ :=
  (μ (Set.Iic x)).toReal

/-- `F` is the CDF of `μ` and is continuous. -/
def IsContinuousCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ Continuous (fun x => (F x : ℝ))

/-- `F` is the CDF of `μ` and is strictly increasing. -/
def IsStrictlyIncreasingCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ StrictMono (fun x => (F x : ℝ))

/-! ## Imported Theorem Debt -/

/-!
### Gaussian Polar Decomposition

Mathematical content represented here as imported theorem debt.

Let \(G \sim \mathcal{N}(0, I_d)\), and define
\[
  R := \|G\|, \qquad \Theta := \frac{G}{\|G\|}.
\]
Imported facts:
\[
  \Theta \sim \mathrm{Unif}(S^{d-1}), \qquad R \perp \Theta, \qquad
  R^2 = \sum_{i=1}^d G_i^2 \sim \chi^2_d.
\]

Chi-square CDF (also imported here):
\[
  F_{\chi^2_d}(x) =
  \frac{\gamma\!\left(\frac d2,\frac x2\right)}{\Gamma\!\left(\frac d2\right)}.
\]

External bibliography:
- NIST/SEMATECH (2012). *e-Handbook of Statistical Methods*, "Chi-Square Distribution".
  https://www.itl.nist.gov/div898/handbook/eda/section3/eda3666.htm
- Vershynin, R. (2018). *High-Dimensional Probability*. Cambridge University Press.
  https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-book.pdf
-/

/-- Standard Gaussian law, encoded on nonzero vectors for the wristband map domain. -/
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)

/-- The chi-square law for squared radius. -/
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal

/-- Chi-square CDF map used by the wristband transform, landing in `[0,1]`. -/
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval

/-- Imported Gaussian polar fact: direction is uniform. -/
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) = sphereUniform d

/-- Imported Gaussian polar fact: squared radius has chi-square law. -/
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) = chiSqRadiusLaw d

/-- Imported Gaussian polar fact: direction and radius are independent. -/
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d) (direction (d := d)) (radiusSq (d := d))

/-!
### Sphere Rotation Invariance

TODO theorem debt: prove using
`LinearIsometryEquiv.measurePreserving` + `toSphere` invariance + normalization.
-/

/-- Imported: uniform sphere measure is invariant under linear isometries. -/
axiom sphereUniform_rotationInvariant
    (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d) = sphereUniform d

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
    (hF : IsContinuousCDFFor μ F) :
    pushforward F μ = uniform01 := by
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
    (hCDF : IsContinuousCDFFor targetLaw F)
    (hStrict : IsStrictlyIncreasingCDFFor targetLaw F)
    (hUniform : pushforward F observedLaw = uniform01) :
    observedLaw = targetLaw := by
  -- Deferred for the same reason as `probabilityIntegralTransform`.
  sorry

end WristbandLossProofs
