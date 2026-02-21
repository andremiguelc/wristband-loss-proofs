import WristbandLossProofs.Foundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Imported Theorem Debt

All declarations here are `axiom`s — external mathematical results assumed
without Lean proof. Trust boundary:
- `gaussianNZ` is the sole **existential** axiom (posits a measure's existence).
- The remaining four are **relational** (equations over already-defined terms);
  they cannot introduce new objects or contradict each other.

A validator should check per axiom: does the Lean statement faithfully encode
the cited result at the indicated source? -/

/-! ### Gaussian Polar Decomposition

For G ~ N(0, I_d): direction G/‖G‖ is uniform on S^{d-1}, ‖G‖² ~ χ²_d, and
the two are independent. Primary source for all three: Muirhead (1982), Thm 1.5.6. -/

/-- G ~ N(0, I_d) as a probability measure on ℝ^d \ {0}.

    N(0, I_d) has a Lebesgue density (Vershynin 2026, §3.3.1 Eq. 3.11), so
    P({0}) = 0 and the restriction to {x ≠ 0} is a probability measure.

    Note: derivable (not truly axiomatic) once Mathlib has the ambient Gaussian
    on Vec d; see audit §9.6 for the proposed bridge. -/
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)

/-- G/‖G‖ ~ σ_{d-1} when G ~ N(0, I_d).

    Muirhead (1982), Thm 1.5.6: "T(X) is uniformly distributed on S_m."
    N(0, I_d) is spherical, satisfying the theorem's hypothesis P(X=0) = 0.

    `direction z = z/‖z‖ : Sphere d` and `sphereUniform d` = σ_{d-1}. -/
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) (measurable_direction d) = sphereUniform d

/-- ‖G‖² ~ χ²_d when G ~ N(0, I_d).

    Muirhead (1982), Ch. 1 (before Thm 1.5.6): "r² = X'X has the familiar
    χ²_m density." Definitionally: χ²_d = Σ Z_i² for Z_i iid N(0,1).

    `radiusSq z = ‖z‖² : NNReal`; `chiSqRadiusLaw d` is defined in
    Foundations.lean via Mathlib's gammaMeasure (not an axiom). -/
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) (measurable_radiusSq d) = chiSqRadiusLaw d

/-- G/‖G‖ ⊥ ‖G‖² when G ~ N(0, I_d).

    Muirhead (1982), Thm 1.5.6: "T(X) and r are independent."
    Independence extends from r to r² because σ(r) = σ(r²) on [0,∞).
    Historical: Maxwell (1860), Phil. Mag. 19, pp. 19–32. -/
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw
      (gaussianNZ d)
      (direction (d := d))
      (radiusSq (d := d))
      (measurable_direction d)
      (measurable_radiusSq d)

/-! ### Sphere Rotation Invariance

Planned for a Lean proof via Mathlib isometry-transport lemmas for `toSphere`. -/

/-- O_# σ_{d-1} = σ_{d-1} for any linear isometry O. -/
axiom sphereUniform_rotationInvariant
    (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d) (measurable_rotateSphere O) = sphereUniform d

end WristbandLossProofs
