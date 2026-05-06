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
- Dai, F.; Xu, Y. (2013). *Approximation Theory and Harmonic Analysis
  on Spheres and Balls*, Chapter 1, Theorem 2.6, Corollary 2.7,
  Theorem 2.9. Springer.
- Dutordoir, V.; Durrande, N.; Hensman, J. (2020). "Sparse Gaussian
  Processes with Spherical Harmonic Features." *PMLR* 119, Theorem 1
  and supplement Theorems 3--5.
- Gneiting, T. (2013). "Strictly and non-strictly positive definite
  functions on spheres." *Bernoulli* 19(4), Theorem 1.
- Mercer, J. (1909). "Functions of positive and negative type."
  *Phil. Trans. R. Soc. Lond. A* 209, 415–446.
- Schoenberg, I.J. (1942). "Positive definite functions on spheres."
  *Duke Math. J.* 9(1), 96–108.
- Steinwart, I.; Christmann, A. (2008). *Support Vector Machines.*
  Springer (Theorem 4.49).
-/

/-! ## Axioms -/

/-- Source-close zonal spherical-harmonic expansion of `kernelAngChordal`
    for `d ≥ 3`.

    Primary harmonic-analysis source:
    Dai-Xu, Chapter 1, Theorem 2.6, Corollary 2.7, Theorem 2.9.

    Secondary ML/kernel source:
    Dutordoir-Durrande-Hensman (2020), Theorem 1 and supplement
    Theorems 3--5.

    Positivity source:
    Gneiting (2013), Theorem 1, summarizing Schoenberg's characterization
    of positive definite zonal kernels by nonnegative Gegenbauer
    coefficients.

    Generic Mercer source used only for the pointwise Mercer expansion
    mechanism:
    Steinwart-Christmann, Theorem 4.49.

    Specialization:
    `kernelAngChordal β α u v = s (⟪u, v⟫)` with
    `s(t) = exp (2 * β * α^2 * (t - 1))`.

    Fragility:
    the standard Gegenbauer normalization uses `(d - 2) / 2` and is
    singular at `d = 2`. This imported fact is intentionally stated only
    for `3 ≤ d`; the circle case should be handled separately by a Fourier
    expansion or left explicitly isolated. -/
axiom kernelAngChordal_zonalHarmonicExpansion_ge3
    (d : ℕ) (β α : ℝ) (hDim : 3 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ∃ (Y : (ℓ : ℕ) → Fin (sphericalHarmonicDim d ℓ) → Sphere d → ℝ)
      (γ : ℕ → ℝ),
      (∀ ℓ : ℕ, 0 ≤ γ ℓ) ∧
      (∀ ℓ : ℕ, ∀ r : Fin (sphericalHarmonicDim d ℓ), Continuous (Y ℓ r)) ∧
      (∀ ℓ : ℕ, ∀ r : Fin (sphericalHarmonicDim d ℓ),
        ∀ ℓ' : ℕ, ∀ r' : Fin (sphericalHarmonicDim d ℓ'),
          ∫ u, Y ℓ r u * Y ℓ' r' u
            ∂(sphereUniform d (by omega) : Measure (Sphere d)) =
              if h : ℓ = ℓ' then
                if h ▸ r = r' then 1 else 0
              else 0) ∧
      (∀ u : Sphere d,
        Y 0
            ⟨0, by
              have hDim2 : 2 ≤ d := by omega
              simpa [sphericalHarmonicDim_zero d hDim2]⟩
            u = 1) ∧
      (∀ u v : Sphere d,
        kernelAngChordal β α u v =
          ∑' ℓ : ℕ,
            γ ℓ *
              ∑ r : Fin (sphericalHarmonicDim d ℓ), Y ℓ r u * Y ℓ r v)

/-- FRAGILE FLAT WRAPPER.

    This is a flat-`ℕ` enumeration wrapper around the source-close
    degree-block spherical-harmonic expansion. The natural source index is
    `Σ ℓ, Fin (sphericalHarmonicDim d ℓ)`, not a bare `ℕ`.

    For `d ≥ 3`, the source-close imported fact is
    `kernelAngChordal_zonalHarmonicExpansion_ge3`.

    For `d = 2`, the standard Gegenbauer formula degenerates at
    `(d - 2) / 2 = 0`; this case requires a separate Fourier / circle
    expansion.

    Generic Mercer theorems justify the existence of a continuous kernel
    eigen-expansion, but not by themselves the degree accessor, per-degree
    multiplicities, or constancy of eigenvalues inside each spherical
    harmonic degree block. Those are packaged here as a temporary flattened
    interface for downstream spectral files. -/
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
