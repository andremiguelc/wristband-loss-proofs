import WristbandLossProofs.Spectral.SpectralPrimitives
import WristbandLossProofs.KernelImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Spectral Imported Facts

External spectral results assumed without Lean proof, plus the
extracted definitions used across the spectral branch.

References:
- Atkinson, K.; Han, W. (2012). *Spherical Harmonics and Approximations
  on the Unit Sphere*, Theorem 2.9. Springer.
- Mercer, J. (1909). "Functions of positive and negative type."
  *Phil. Trans. R. Soc. Lond. A* 209, 415–446.
- Schoenberg, I.J. (1942). "Positive definite functions on spheres."
  *Duke Math. J.* 9(1), 96–108.
- Steinwart, I.; Christmann, A. (2008). *Support Vector Machines.*
  Springer (Theorem 4.49).
-/

/-! ## Axioms -/

/-- Mercer expansion of `kernelAngChordal` with degree-block structure —
    Mercer (1909); Steinwart-Christmann Thm 4.49. Witnesses an orthonormal
    basis of continuous angular eigenfunctions with nonnegative eigenvalues,
    pointwise expansion, the constant zeroth mode, a degree accessor with the
    correct block multiplicity, and constancy of `λv` on each degree fibre. -/
axiom kernelAngChordal_mercerExpansion
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (hDim1 : 1 ≤ d := by omega) :
    ∃ (φ : ℕ → Sphere d → ℝ) (lambdaV : ℕ → ℝ) (degAt : ℕ → ℕ),
      (∀ j : ℕ, 0 ≤ lambdaV j) ∧
      (∀ j : ℕ, Continuous (φ j)) ∧
      (∀ j j' : ℕ,
        ∫ u, φ j u * φ j' u ∂(sphereUniform d hDim1 : Measure (Sphere d)) =
          if j = j' then 1 else 0) ∧
      (∀ u v : Sphere d,
        kernelAngChordal β α u v =
          ∑' j : ℕ, lambdaV j * φ j u * φ j v) ∧
      (∀ u : Sphere d, φ 0 u = 1) ∧
      (∀ ℓ : ℕ,
        Set.ncard {j : ℕ | degAt j = ℓ} = sphericalHarmonicDim d ℓ) ∧
      (∀ j j' : ℕ, degAt j = degAt j' → lambdaV j = lambdaV j')

/-! ## Witness extraction -/

/-- Angular eigenfunctions extracted from the Mercer axiom. -/
noncomputable def mercerEigenfun
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ℕ → Sphere d → ℝ :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose

/-- Angular eigenvalues extracted from the Mercer axiom. -/
noncomputable def mercerEigenval
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ℕ → ℝ :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose

/-- Degree accessor extracted from the Mercer axiom: the angular degree
    `ℓ` of the `j`-th flat eigenmode. -/
noncomputable def mercerDegAt
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ℕ → ℕ :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.choose

/-- Constant-mode coefficient from the explicit Neumann radial cosine
expansion. Its value is derived in `kernelRadNeumann_explicitCosineExpansion`,
which in turn is built from the imported Jacobi periodization identity
`gaussian_periodization_cosine_series_period_two`. -/
noncomputable def neumannConstantCoeff (β : ℝ) (_hβ : 0 < β) : ℝ :=
  Real.sqrt (Real.pi / β)

/-- Cosine-mode coefficients from the explicit Neumann radial cosine
expansion. The coefficients match the standard Neumann heat-kernel formula
on `[0,1]`; see `kernelRadNeumann_explicitCosineExpansion` for the derived
expansion identity built from
`gaussian_periodization_cosine_series_period_two`. -/
noncomputable def neumannCosineCoeff (β : ℝ) (_hβ : 0 < β) : ℕ → ℝ :=
  fun k => 2 * Real.sqrt (Real.pi / β) *
    Real.exp (-(((k + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2) / (4 * β))

/-- Extended radial coefficient sequence assembling `a0` and `a k`. -/
noncomputable def neumannRadialCoeff (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  radialCoeff (neumannConstantCoeff β hβ) (neumannCosineCoeff β hβ)

/-- Addition theorem for spherical harmonics under the probability
    uniform measure on `S^{d-1}` — Atkinson-Han Thm 2.9. -/
axiom mercerEigenfun_addition_theorem
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (ℓ : ℕ) (u : Sphere d) :
    ∑' j : ℕ, (if mercerDegAt d β α hDim hβ hα j = ℓ then
        (mercerEigenfun d β α hDim hβ hα j u) ^ 2 else 0)
      = (sphericalHarmonicDim d ℓ : ℝ)

/-- Diagonal Mercer constraint: total angular mass per degree-block
    sums to `1` (trace of the angular Mercer integral operator under
    the probability uniform measure). -/
axiom mercerDegreeMass_total_eq_one
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ∑' ℓ : ℕ,
      (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
          mercerEigenval d β α hDim hβ hα j else 0) = 1

/-- P-uniform λ-weighted per-fibre Cauchy-Schwarz bound on mode
    projections — packaged consequence of Atkinson-Han Thm 2.9 +
    Cauchy-Schwarz on integrals + `|radialFeature k| ≤ 1`. -/
axiom mercer_modeProjSqSum_per_degree_le_mass
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ k : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        mercerEigenval d β α hDim hβ hα j *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0)
      ≤ ∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
          mercerEigenval d β α hDim hβ hα j else 0

end WristbandLossProofs
