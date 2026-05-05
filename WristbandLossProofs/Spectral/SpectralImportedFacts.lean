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
    `φ : ℕ → Sphere d → ℝ`, eigenvalues `λv : ℕ → ℝ`, and a degree-accessor
    `degAt : ℕ → ℕ` (mapping each flat eigenmode to its angular degree)
    satisfying:

    1. **(Nonnegativity)** `λv j ≥ 0` for all `j`.
    2. **(Orthonormality)** `{φ j}` is orthonormal in `L²(sphereUniform d)`:
       `∫ φ_j(u) · φ_j'(u) dσ(u) = δ_{jj'}`.
    3. **(Kernel expansion)** `k_ang(u, v) = Σ' j, λv j · φ_j(u) · φ_j(v)`
       (as a `tsum` equality pointwise on `Sphere d × Sphere d`).
    4. **(Constant-mode identification)** `φ 0 = fun _ => 1`:
       the zeroth eigenfunction is the constant function equal to 1
       (valid since `sphereUniform d` is a probability measure).
    5. **(Block multiplicity)** Each angular degree `ℓ` has exactly
       `sphericalHarmonicDim d ℓ` flat eigenmodes mapped to it
       (equal to the dimension of degree-`ℓ` spherical harmonics on `S^{d-1}`).
    6. **(Constancy on fibres)** `λv` is constant on each `degAt`-fibre:
       all eigenmodes of the same angular degree share the same eigenvalue.

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
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (hDim1 : 1 ≤ d := by omega) :
    ∃ (φ : ℕ → Sphere d → ℝ) (lambdaV : ℕ → ℝ) (degAt : ℕ → ℕ),
      -- (1) Nonnegativity of eigenvalues
      (∀ j : ℕ, 0 ≤ lambdaV j) ∧
      -- (2) Orthonormality in L²(sphereUniform d)
      (∀ j j' : ℕ,
        ∫ u, φ j u * φ j' u ∂(sphereUniform d hDim1 : Measure (Sphere d)) =
          if j = j' then 1 else 0) ∧
      -- (3) Pointwise kernel expansion as a tsum
      (∀ u v : Sphere d,
        kernelAngChordal β α u v =
          ∑' j : ℕ, lambdaV j * φ j u * φ j v) ∧
      -- (4) Constant-mode identification
      (∀ u : Sphere d, φ 0 u = 1) ∧
      -- (5) Block multiplicity: each angular degree `ℓ` has exactly
      -- `sphericalHarmonicDim d ℓ` flat eigenmodes mapped to it.
      (∀ ℓ : ℕ,
        Set.ncard {j : ℕ | degAt j = ℓ} = sphericalHarmonicDim d ℓ) ∧
      -- (6) `lambdaV` is constant on each `degAt`-fibre: all flat eigenmodes
      -- of the same angular degree share the same eigenvalue `λ_ℓ`.
      (∀ j j' : ℕ, degAt j = degAt j' → lambdaV j = lambdaV j')

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

/-- Degree accessor extracted from the Mercer axiom: `mercerDegAt … j` is the
angular degree `ℓ` of the `j`-th flat eigenmode.  Together with
`mercerDegAt_card_fiber` and `mercerEigenval_const_on_degree_fiber`, this
exposes the block structure used by the closed-form angular tail bound. -/
noncomputable def mercerDegAt
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ℕ → ℕ :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.choose

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

/-- Explicit Gaussian upper bound on Neumann cosine coefficients.

The cosine-mode weight on `cos((k+1)π t)·cos((k+1)π t')` in the
`kernelRadNeumann β` expansion satisfies the closed-form bound
`ã_{k+1} ≤ 2√(π/β) · exp(−π²(k+1)²/(4β))`.  Indexing matches
`kernelRadNeumann_hasCosineExpansion` (Lean `k` ↔ math `m = k + 1`).

This is strictly more informative than `summable_neumannCosineCoeff_imported`
(which only asserts summability) — it gives the explicit Gaussian rate used
in the closed-form radial-tail bound.

References:
- Teplyaev, A. (1995). *Spectral Analysis of Heat Kernels on Compact
  Manifolds*; *Heat kernels on the unit circle and on intervals*,
  Eq. (0.6)–(0.7) — direct interval-Neumann formula.
- Stein, E.M. & Weiss, G. (1971). *Introduction to Fourier Analysis on
  Euclidean Spaces*, Ch. VII §2 (Poisson summation). -/
axiom neumannCosineCoeff_le_gaussianBound
    (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    neumannCosineCoeff β hβ k ≤
      2 * Real.sqrt (Real.pi / β) *
        Real.exp (-(Real.pi ^ 2) * ((k : ℝ) + 1) ^ 2 / (4 * β))

/-- **Addition theorem** for spherical harmonics under probability normalization.

For each angular degree `ℓ ≥ 0` and each unit vector `u`, the sum of squares
of all `mercerEigenfun`s of degree `ℓ` equals the multiplicity `N(d, ℓ)`:
`Σ_{j : degAt j = ℓ} φ_j(u)² = N(d, ℓ)`.

The constant `N(d, ℓ) = sphericalHarmonicDim d ℓ` (no `|S^{d-1}|` factor)
because `sphereUniform` is the **probability** uniform measure under which
the harmonics are orthonormal.  The flat-index `tsum`-with-indicator form
matches the Mercer expansion's flat indexing.

This is one of the two pillars of the closed-form angular tail bound:
combined with the diagonal Mercer constraint
`k_ang(u, u) = Σ_j λv j · φ_j(u)² = 1`, it gives `Σ_ℓ λ_ℓ · N(d, ℓ) = 1`
(derived without an additional axiom).

Reference: Atkinson, K. & Han, W. (2012). *Spherical Harmonics and
Approximations on the Unit Sphere*, Theorem 2.9. Springer. -/
axiom mercerEigenfun_addition_theorem
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (ℓ : ℕ) (u : Sphere d) :
    ∑' j : ℕ, (if mercerDegAt d β α hDim hβ hα j = ℓ then
        (mercerEigenfun d β α hDim hβ hα j u) ^ 2 else 0)
      = (sphericalHarmonicDim d ℓ : ℝ)

/-- **Diagonal Mercer constraint** under our normalization.

The total angular mass per degree-block equals `1`:
`Σ_ℓ Σ_{j : degAt j = ℓ} λv j = Σ_ℓ λ_ℓ · N(d, ℓ) = 1`.

Equivalently, this is the L²(σ)-trace of the angular Mercer integral
operator: `tr(T_K) = ∫ k_ang(u, u) dσ(u) = ∫ 1 dσ = 1` (where `σ` is
the **probability** uniform measure on `S^{d-1}`), combined with the
spectral identity `tr(T_K) = Σ_j λv j`.

**Derivable from** `kernelAngChordal_mercerExpansion` (clauses 2 + 3 + 6) +
`mercerEigenfun_addition_theorem` (regrouping of `Σ_j λv j · φ_j(u)² = 1`
into degree fibres) using a Fubini-style sigma swap on nonneg `tsum`s.
The Lean derivation is deferred to a future cleanup pass; the statement
is included here as an axiom so the closed-form angular tail bound
can be stated with the elegant complementary form `T_ang(L) + S_ang(L) = 1`.

References (for the math derivation): Mercer (1909); Atkinson-Han Thm 2.9. -/
axiom mercerDegreeMass_total_eq_one
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ∑' ℓ : ℕ,
      (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
          mercerEigenval d β α hDim hβ hα j else 0) = 1

/-- **P-uniform λ-weighted per-fibre bound on mode projections.**

For each angular degree `ℓ` and radial mode `k`, the **λ-weighted** sum of
squared mode projections over the `degAt`-fibre of degree `ℓ` is bounded by
the per-degree mass `Σ_{j : degAt j = ℓ} λv j` (= `λ_ℓ · N(d, ℓ)` by
constancy + multiplicity), uniformly in the distribution `P`:

  `Σ_{j : degAt j = ℓ} λ_j · (E_P[φ_j(U) · f_k(T)])²
     ≤ Σ_{j : degAt j = ℓ} λ_j`.

This is the closed-form-ready version of the per-fibre Cauchy-Schwarz bound:
the angular-strip energy is bounded by the per-degree mass (which sums to
`1` by `mercerDegreeMass_total_eq_one`).

**Derivable from** `mercerEigenfun_addition_theorem` + λv non-negativity +
λv-on-fibre constancy (clauses of `kernelAngChordal_mercerExpansion`) +
Cauchy-Schwarz on integrals + |radialFeature k| ≤ 1:
- C-S per `j` (with `λ_j ≥ 0`): `λ_j · (E_P[X_j])² ≤ λ_j · E_P[X_j²]`.
- Sum over fibre, linearity:
  `Σ_j λ_j · (E_P[X_j])² ≤ E_P[(Σ_j λ_j · φ_j(U)²) · f_k(T)²]`.
- λ-constancy + addition theorem: `Σ_{j : degAt = ℓ} λ_j · φ_j(u)²
  = λ_ℓ · Σ_{j : degAt = ℓ} φ_j(u)² = λ_ℓ · N(d, ℓ)`.
- `λ_ℓ · N(d, ℓ) = Σ_{j : degAt = ℓ} λ_j` (constancy + cardinality).
- `|f_k| ≤ 1` and `E_P[c] = c` for probability `P`.

The Lean derivation involves measure-theoretic Cauchy-Schwarz, Fubini-style
swap, and a tsum-cardinality identity for the fibre; deferred to a future
cleanup pass.

Reference: Atkinson-Han Thm 2.9 (addition theorem); standard C-S identity. -/
axiom mercer_modeProjSqSum_per_degree_le_mass
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ k : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        mercerEigenval d β α hDim hβ hα j *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0)
      ≤ ∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
          mercerEigenval d β α hDim hβ hα j else 0

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
