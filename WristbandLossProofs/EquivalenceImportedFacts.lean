import WristbandLossProofs.EquivalencePrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! # Imported Theorem Debt

External mathematical results assumed without Lean proof. Each axiom block below
transcribes one theorem from:

  Muirhead, R. J. (1982). *Aspects of Multivariate Statistical Theory*.
  Wiley Series in Probability and Mathematical Statistics. John Wiley & Sons.

Validator contract: each axiom names a single Muirhead theorem (with any
specialization). Reading the axiom requires reading that theorem in the source.
Everything *derived* from these axioms lives in `EquivalenceFoundations`.

This file contains: the three axioms, plus the witness-extraction definition
`gaussianFull` and its density theorem `gaussianFull_density` — neither is a
derivation, both are just unwrappings of the existential axiom, named here so
the chi-squared axiom can refer to them. -/

/-! ## Axioms -/

/-- Standard isotropic Gaussian density on `Vec d` — Muirhead Thm 1.2.9
    specialized to `μ = 0`, `Σ = I_d`. Witness pattern packages existence
    and the density formula into a single axiom. -/
private axiom gaussianFull_witness (d : ℕ) :
    ∃ μ : Distribution (Vec d), ∀ {s : Set (Vec d)}, MeasurableSet s →
        μ.val s
          = ∫⁻ x in s,
              ENNReal.ofReal
                ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
              ∂(volume : Measure (Vec d))

/-- Polar decomposition for spherical distributions — Muirhead Thm 1.5.6. -/
axiom spherical_polar_decomposition (d : ℕ) (hDim : 1 ≤ d)
    (μ : Distribution (VecNZ d))
    (hSpherical : ∀ O : (Vec d) ≃ₗᵢ[ℝ] Vec d,
        pushforward (rotateVecNZ O) μ (measurable_rotateVecNZ O) = μ) :
    pushforward (direction (d := d)) μ (measurable_direction d) = sphereUniform d hDim
      ∧ IndepLaw μ (direction (d := d)) (radiusSq (d := d))
          (measurable_direction d) (measurable_radiusSq d)

/-! ## Witness unwrapping (so the chi-squared axiom can name `gaussianFull`) -/

/-- The standard isotropic Gaussian, named from the witness axiom. -/
def gaussianFull (d : ℕ) : Distribution (Vec d) := (gaussianFull_witness d).choose

/-- Density formula for `gaussianFull` (Thm 1.2.9 specialized). -/
theorem gaussianFull_density (d : ℕ) {s : Set (Vec d)} (hs : MeasurableSet s) :
    (gaussianFull d).val s
      = ∫⁻ x in s,
          ENNReal.ofReal
            ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
          ∂(volume : Measure (Vec d)) :=
  (gaussianFull_witness d).choose_spec hs

/-- Squared norm of `gaussianFull` is χ²_d — Muirhead Thm 1.4.1(a)
    specialized to `μ = 0`, `Σ = I_d`. Stated about `gaussianFull` rather than
    `gaussianNZ` so the axiom does not depend on a derivation. -/
axiom gaussianFull_normSq_chiSq (d : ℕ) (hDim : 1 ≤ d) :
    pushforward (radiusSqVec (d := d)) (gaussianFull d) (measurable_radiusSqVec d)
      = chiSqRadiusLaw d

end WristbandLossProofs
