import WristbandLossProofs.CoreEngine.Geometry
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

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
  have hu : ‖u.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.2
  have hOu : ‖O u.1‖ = 1 := by
    calc
      ‖O u.1‖ = ‖u.1‖ := O.norm_map u.1
      _ = 1 := hu
  simpa [Metric.mem_sphere, dist_eq_norm] using hOu

/--
TODO theorem debt: prove invariance using
`LinearIsometryEquiv.measurePreserving` + `toSphere` invariance + normalization.
-/
axiom sphereUniform_rotationInvariant
    (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d) = sphereUniform d

end WristbandLossProofs
