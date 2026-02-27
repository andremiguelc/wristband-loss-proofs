import WristbandLossProofs.Spectral.SpectralPrimitives
import WristbandLossProofs.KernelImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Spectral Imported Facts

This file contains externally imported spectral facts:
- Mercer decomposition of the angular kernel,
- witness extractions used across the spectral branch,
- closure-bridge assumptions used to discharge the unconditional
  spectral/kernel identity.

Every other fact used in the spectral branch is either already proved
elsewhere (`cosine_mode_integral_uniform01` in `KernelFoundations`),
in Mathlib (`integral_tsum`, `tsum_comm'`, `tsum_mul_left`, `integral_prod_mul`),
or imported below as an explicit closure bridge.

### Reused from existing files (no changes needed)

| Axiom | File | Used for |
|-------|------|----------|
| `kernelRadNeumann_hasCosineExpansion` | `KernelImportedFacts` | radial `a0` and `a k` witnesses |
| `kernelAngChordal_posSemiDef` | `KernelImportedFacts` | justifies `λv j ≥ 0` |
| `kernelEnergy_minimizer_unique` | `KernelMinimization` | uniqueness conclusion |
| `wristbandEquivalence` | `Equivalence` | Gaussian ↔ uniform bridge |
-/

/-! ### Mercer decomposition of the angular kernel -/

/-- **Mercer decomposition of `kernelAngChordal`.**

    For any `d ≥ 2`, `β > 0`, `α > 0`, there exist angular eigenfunctions
    `φ : ℕ → Sphere d → ℝ` and eigenvalues `λv : ℕ → ℝ` satisfying:

    1. **(Nonnegativity)** `λv j ≥ 0` for all `j`.
    2. **(Orthonormality)** `{φ j}` is orthonormal in `L²(sphereUniform d)`:
       `∫ φ_j(u) · φ_j'(u) dσ(u) = δ_{jj'}`.
    3. **(Kernel expansion)** `k_ang(u, v) = Σ' j, λv j · φ_j(u) · φ_j(v)`
       (as a `tsum` equality pointwise on `Sphere d × Sphere d`).
    4. **(Constant-mode identification)** `φ 0 = fun _ => 1`:
       the zeroth eigenfunction is the constant function equal to 1
       (valid since `sphereUniform d` is a probability measure).

    **Source**: Mercer (1909); Steinwart–Christmann (2008), Theorem 4.49.
    The chain of reasoning is:
    - *Compactness of `T_K`:* `kernelAngChordal β α` is continuous on the compact
      space `Sphere d`, so `K ∈ L²(σ ⊗ σ)` and `T_K` is Hilbert–Schmidt, hence compact.
    - *Self-adjointness of `T_K`:* the kernel is symmetric (`K(u,v) = K(v,u)`).
    - *Nonnegativity of eigenvalues:* the kernel is PSD (`kernelAngChordal_posSemiDef`),
      so `⟨T_K f, f⟩ ≥ 0`, giving `λv j ≥ 0` (clause 1).
    These three properties are standard functional analysis; they yield the countable
    orthonormal eigenbasis. **Mercer's theorem** is the separate, stronger statement
    that the eigenexpansion in clause (3) converges *pointwise* (not merely in `L²`),
    which holds for continuous PSD kernels on compact metric spaces.

    **Mathlib status**: Mathlib has spectral theory for compact operators
    (`Analysis.InnerProductSpace.Spectrum`) but not the Mercer pointwise
    convergence form for integral operators. The `tsum` equality in clause (3)
    is the minimal statement needed for downstream proofs; uniform convergence
    is not asserted.

    References:
    - Mercer, J. (1909). "Functions of positive and negative type."
      *Phil. Trans. R. Soc. Lond. A*, 209, 415–446.
    - Steinwart, I. & Christmann, A. (2008). *Support Vector Machines*,
      Theorem 4.49. Springer.
    - Schoenberg, I.J. (1942). "Positive definite functions on spheres."
      *Duke Math. J.*, 9(1), 96–108. -/
axiom kernelAngChordal_mercerExpansion
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ∃ (φ : ℕ → Sphere d → ℝ) (lambdaV : ℕ → ℝ),
      -- (1) Nonnegativity of eigenvalues
      (∀ j : ℕ, 0 ≤ lambdaV j) ∧
      -- (2) Orthonormality in L²(sphereUniform d)
      (∀ j j' : ℕ,
        ∫ u, φ j u * φ j' u ∂(sphereUniform d : Measure (Sphere d)) =
          if j = j' then 1 else 0) ∧
      -- (3) Pointwise kernel expansion as a tsum
      (∀ u v : Sphere d,
        kernelAngChordal β α u v =
          ∑' j : ℕ, lambdaV j * φ j u * φ j v) ∧
      -- (4) Constant-mode identification
      (∀ u : Sphere d, φ 0 u = 1)

/-! ### Witness extraction from imported expansion axioms -/

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

/-- Constant-mode radial coefficient (`a0`) extracted from the Neumann cosine axiom. -/
noncomputable def neumannConstantCoeff (β : ℝ) (hβ : 0 < β) : ℝ :=
  (kernelRadNeumann_hasCosineExpansion β hβ).choose

/-- Cosine-mode radial coefficients (`a k`) extracted from the Neumann cosine axiom. -/
noncomputable def neumannCosineCoeff (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  (kernelRadNeumann_hasCosineExpansion β hβ).choose_spec.choose

/-- Shorthand: full extended radial coefficient sequence
`radialCoeff (neumannConstantCoeff β hβ) (neumannCosineCoeff β hβ)`. -/
noncomputable def neumannRadialCoeff (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  radialCoeff (neumannConstantCoeff β hβ) (neumannCosineCoeff β hβ)

/-! ### Imported closure bridges for the spectral/kernel identity -/

/-- Imported summability of the Neumann cosine witness sequence.

For the heat kernel on a bounded interval with Neumann boundary conditions,
the cosine-mode coefficients have Gaussian-type decay `exp(-c n^2)` for `c > 0`,
hence absolute summability.

References:
- Evans, L.C. (2010). *Partial Differential Equations* (2nd ed.), AMS,
  §2.3 (heat equation eigenfunction expansions on bounded domains).
- Strauss, W.A. (2007). *Partial Differential Equations: An Introduction*
  (2nd ed.), Wiley (heat equation via Fourier cosine series / Neumann BC). -/
axiom summable_neumannCosineCoeff_imported
    (β : ℝ) (hβ : 0 < β) :
    Summable (neumannCosineCoeff β hβ)

/-- Imported factorized `L¹` bridge on raw mode features
`w ↦ φ_j(w.1) * radialFeature k w.2`, specialized in
`SpectralFoundations` to `modeTerm` using `φ = mercerEigenfun`.

This is a project-level packaged consequence of:
1. Mercer expansion/orthonormality for the angular kernel on compact sphere,
2. boundedness/integrability consequences for Mercer modes,
3. Tonelli/Fubini and Cauchy-Schwarz bounds used to build `L¹` majorants.

References:
- Mercer, J. (1909). *Phil. Trans. R. Soc. Lond. A* 209, 415–446.
- Steinwart, I.; Christmann, A. (2008). *Support Vector Machines*,
  Theorem 4.49 (Mercer form on compact spaces).
- Folland, G.B. (1999). *Real Analysis* (2nd ed.), Wiley
  (Tonelli/Fubini for nonnegative series/integrals). -/
axiom spectral_modeL1_factorized_bridge_imported
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    ∃ M : ℕ → ℝ,
      (∀ j, 0 ≤ M j) ∧
      (∀ j k,
        Integrable
          (fun w : Wristband d =>
            mercerEigenfun d β α hDim hβ hα j w.1 * radialFeature k w.2)
          (P : Measure (Wristband d))) ∧
      (∀ j k,
        ∫ w,
          ‖mercerEigenfun d β α hDim hβ hα j w.1 * radialFeature k w.2‖
          ∂(P : Measure (Wristband d)) ≤ M j) ∧
      Summable
        (fun j : ℕ => ‖mercerEigenval d β α hDim hβ hα j‖ * (M j) ^ 2)

end WristbandLossProofs
