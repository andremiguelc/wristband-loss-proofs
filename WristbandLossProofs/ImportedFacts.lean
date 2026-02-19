import WristbandLossProofs.Foundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Imported Theorem Debt

This file isolates externally sourced mathematical results that are currently
assumed as axioms. Keeping these declarations separate from core definitions
makes the trust boundary explicit.
-/

/-!
### Gaussian Polar Decomposition

Imported facts for `G ~ N(0, I_d)`:
- direction `G / ‖G‖` is uniform on `S^{d-1}`,
- squared radius `‖G‖^2` follows `χ²_d`,
- direction and squared radius are independent.

References:
- NIST/SEMATECH (2012), e-Handbook of Statistical Methods, Chi-Square.
  https://www.itl.nist.gov/div898/handbook/eda/section3/eda3666.htm
- Vershynin, R. (2018), High-Dimensional Probability.
  https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-book.pdf
-/

/-- Standard Gaussian law, encoded on nonzero vectors for wristband-map domain. -/
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)

/-- Imported: Gaussian law is a probability measure. -/
axiom gaussianNZ_isProbability (d : ℕ) :
    IsProbabilityMeasure (gaussianNZ d)

attribute [instance] gaussianNZ_isProbability

/-- Chi-square law for squared radius. -/
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal

/-- Imported: chi-square radius law is a probability measure. -/
axiom chiSqRadiusLaw_isProbability (d : ℕ) :
    IsProbabilityMeasure (chiSqRadiusLaw d)

attribute [instance] chiSqRadiusLaw_isProbability

/-- Chi-square CDF map used by the wristband transform, valued in `[0,1]`. -/
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval

/-- Imported Gaussian polar fact: direction is uniform on the sphere. -/
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) = sphereUniform d

/-- Imported Gaussian polar fact: squared radius has chi-square law. -/
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) = chiSqRadiusLaw d

/-- Imported Gaussian polar fact: direction and squared radius are independent. -/
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d) (direction (d := d)) (radiusSq (d := d))

/-!
### Sphere Rotation Invariance

TODO theorem debt: prove via Mathlib transport/invariance lemmas for `toSphere`.
-/

/-- Imported: normalized sphere law is invariant under linear isometries. -/
axiom sphereUniform_rotationInvariant
    (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d) = sphereUniform d

/-- Imported: sphere-uniform law is a probability measure. -/
axiom sphereUniform_isProbability (d : ℕ) :
    IsProbabilityMeasure (sphereUniform d)

attribute [instance] sphereUniform_isProbability

end WristbandLossProofs
