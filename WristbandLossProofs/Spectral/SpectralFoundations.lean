import WristbandLossProofs.Spectral.SpectralImportedFacts
import WristbandLossProofs.KernelFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Spectral Foundations

Local lemmas for the spectral energy branch.  All non-trivial proofs are
`sorry`-scaffolded for a future proof round.

### Proof obligations summary

| Lemma | Route | Mathlib / Source |
|-------|-------|-----------------|
| `angularEigenfun_integral_zero` | B1: from orthonormality (A1_bundle clause 2+4) | local 3-liner |
| `sphereMean_zero` | B3: antipodal symmetry of `sphereUniform` | `integral_map` + axiom |
| `modeProj_zero_zero_eq_one` | A1 clause 4: `φ 0 = 1`, `radialFeature 0 = 1` | trivial |
| `modeProj_vanishes_at_uniform` | B1 (j > 0, k = 0) + B2 (k ≥ 1) via Fubini | local |
| `spectralEnergy_eq_kernelEnergy` | 7-step algebra: A1 + radial expansion + Fubini | C1, C2, C3, D1 |
| `spectralEnergy_nonneg_excess` | all terms non-negative; (0,0) term constant | order lemmas |
-/

/-! ### Witness extraction from axioms -/

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

/-- Shorthand: the full radial coefficient sequence `radialCoeff a0 a` for
    the Neumann kernel, combining the constant and cosine witnesses. -/
noncomputable def neumannRadialCoeff (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  radialCoeff (neumannConstantCoeff β hβ) (neumannCosineCoeff β hβ)

/-! ### Properties of witnesses (from the axiom spec) -/

lemma mercerEigenval_nonneg
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (j : ℕ) :
    0 ≤ mercerEigenval d β α hDim hβ hα j :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.1 j

lemma mercerEigenfun_orthonormal
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j j' : ℕ) :
    ∫ u, mercerEigenfun d β α hDim hβ hα j u *
           mercerEigenfun d β α hDim hβ hα j' u
        ∂(sphereUniform d : Measure (Sphere d)) =
      if j = j' then 1 else 0 :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.2.1 j j'

lemma mercerEigenfun_zero_eq_one
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (u : Sphere d) :
    mercerEigenfun d β α hDim hβ hα 0 u = 1 :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.2.2.2 u

lemma neumannConstantCoeff_nonneg (β : ℝ) (hβ : 0 < β) :
    0 ≤ neumannConstantCoeff β hβ :=
  (kernelRadNeumann_hasCosineExpansion β hβ).choose_spec.choose_spec.1

lemma neumannCosineCoeff_nonneg (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    0 ≤ neumannCosineCoeff β hβ k :=
  (kernelRadNeumann_hasCosineExpansion β hβ).choose_spec.choose_spec.2.1 k

/-- All radial coefficients are non-negative. -/
lemma neumannRadialCoeff_nonneg (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    0 ≤ neumannRadialCoeff β hβ k := by
  cases k with
  | zero => exact neumannConstantCoeff_nonneg β hβ
  | succ k => exact neumannCosineCoeff_nonneg β hβ k

/-! ### Group B — Integrals vanish at μ₀ -/

/-- **B1**: Non-constant angular eigenfunctions integrate to zero under `sphereUniform`.

    Proof sketch: orthonormality (A1_bundle clause 2) gives
    `∫ φ_j · φ_0 dσ = 0` for `j ≠ 0`.  Since `φ_0 = 1` (clause 4),
    this is `∫ φ_j dσ = 0`.

    Mathlib route: `MeasureTheory.integral_eq_zero_iff` or direct from
    the inner-product calculation `⟨φ_j, 1⟩_{L²} = 0`. -/
lemma angularEigenfun_integral_zero
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j : ℕ) (hj : 0 < j) :
    ∫ u, mercerEigenfun d β α hDim hβ hα j u
        ∂(sphereUniform d : Measure (Sphere d)) = 0 := by
  -- Strategy: use orthonormality with j' = 0:
  --   ∫ φ_j · φ_0 dσ = 0  (since j ≠ 0)
  -- Then substitute φ_0 = 1.
  have hOrtho := mercerEigenfun_orthonormal d β α hDim hβ hα j 0
  simp [Nat.ne_of_gt hj] at hOrtho
  -- hOrtho : ∫ u, φ_j(u) * φ_0(u) dσ = 0
  -- Substitute φ_0(u) = 1:
  have hPhi0 : ∀ u : Sphere d, mercerEigenfun d β α hDim hβ hα 0 u = 1 :=
    mercerEigenfun_zero_eq_one d β α hDim hβ hα
  simpa [hPhi0] using hOrtho

/-- **B2 (reuse)**: Cosine features integrate to zero under `uniform01`.

    Already proved: `cosine_mode_integral_uniform01` in `KernelFoundations.lean`.
    The statement there covers `cos((k+1)·π·t)` for all `k : ℕ`.
    In our indexing: `∫ radialFeature (k+1) t dt = 0` for all `k : ℕ`.

    Note: `∫ radialFeature 0 t dt = ∫ 1 dt = 1` (constant mode, not zero). -/
lemma radialFeature_cosine_integral_zero (k : ℕ) :
    ∫ t : UnitInterval,
      radialFeature (k + 1) t
    ∂(uniform01 : Measure UnitInterval) = 0 := by
  -- Direct application of `cosine_mode_integral_uniform01` from KernelFoundations.
  simpa [radialFeature] using
    (cosine_mode_integral_uniform01 (k + 1) (Nat.succ_pos k))

/-- **Constant radial feature integrates to 1** under `uniform01`.
    `∫ 1 dt = 1` since `uniform01` is a probability measure. -/
lemma radialFeature_constant_integral_one :
    ∫ t : UnitInterval,
      radialFeature 0 t
    ∂(uniform01 : Measure UnitInterval) = 1 := by
  simp [radialFeature]

/-! ### Mode projections at uniform measure -/

/-- The (0, 0) mode projection equals 1 for any distribution.

    Since `φ 0 = 1` and `radialFeature 0 = 1`, the integrand is identically 1,
    and any probability measure integrates 1 to 1. -/
lemma modeProj_zero_zero_eq_one
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    modeProj (mercerEigenfun d β α hDim hβ hα) 0 0 P = 1 := by
  -- φ 0 w.1 = 1 and radialFeature 0 w.2 = 1, so integrand = 1 * 1 = 1.
  -- ∫ 1 dP = 1 since P is a probability measure.
  simp [modeProj, radialFeature, mercerEigenfun_zero_eq_one d β α hDim hβ hα]

/-- **All non-(0,0) mode projections vanish at `wristbandUniform d`**.

    Cases:
    - `k = 0, j > 0`: `modeProj φ j 0 μ₀ = (∫ φ_j dσ) · (∫ 1 dt) = 0 · 1 = 0` (B1).
    - `k ≥ 1, any j`: `modeProj φ j k μ₀ = (∫ φ_j dσ) · (∫ cos(k·π·t) dt) = (?) · 0 = 0`
      because the cosine integral is 0 (B2) and factoring is valid by Fubini (D1).

    Proof route: use `MeasureTheory.integral_prod_mul` (D1) to factor the
    wristband integral into angular × radial, then apply B1 or B2. -/
lemma modeProj_vanishes_at_uniform
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j k : ℕ) (hjk : j ≠ 0 ∨ k ≠ 0) :
    modeProj (mercerEigenfun d β α hDim hβ hα) j k (wristbandUniform d) = 0 := by
  -- Unfold modeProj and wristbandUniform = productLaw sphereUniform uniform01.
  -- Apply D1 (integral_prod_mul) to factor into angular × radial integrals.
  -- For k = 0 and j > 0: angular factor = ∫ φ_j dσ = 0 (B1 above).
  -- For k ≥ 1: radial factor = ∫ radialFeature k dt = 0 (B2 above).
  cases k with
  | zero =>
      have hj : j ≠ 0 := by
        cases hjk with
        | inl hj' => exact hj'
        | inr hk0 => cases hk0 rfl
      have hjPos : 0 < j := Nat.pos_of_ne_zero hj
      have hFactor :
          modeProj (mercerEigenfun d β α hDim hβ hα) j 0 (wristbandUniform d) =
            (∫ u, mercerEigenfun d β α hDim hβ hα j u
              ∂(sphereUniform d : Measure (Sphere d))) *
            (∫ t : UnitInterval, radialFeature 0 t
              ∂(uniform01 : Measure UnitInterval)) := by
        unfold modeProj wristbandUniform productLaw
        simpa using
          (integral_prod_mul
            (μ := (sphereUniform d : Measure (Sphere d)))
            (ν := (uniform01 : Measure UnitInterval))
            (f := fun u : Sphere d => mercerEigenfun d β α hDim hβ hα j u)
            (g := fun t : UnitInterval => radialFeature 0 t))
      have hAng :
          ∫ u, mercerEigenfun d β α hDim hβ hα j u
            ∂(sphereUniform d : Measure (Sphere d)) = 0 :=
        angularEigenfun_integral_zero β α hDim hβ hα j hjPos
      calc
        modeProj (mercerEigenfun d β α hDim hβ hα) j 0 (wristbandUniform d)
            =
          (∫ u, mercerEigenfun d β α hDim hβ hα j u
            ∂(sphereUniform d : Measure (Sphere d))) *
          (∫ t : UnitInterval, radialFeature 0 t
            ∂(uniform01 : Measure UnitInterval)) := hFactor
        _ = 0 := by simp [hAng, radialFeature_constant_integral_one]
  | succ k =>
      have hFactor :
          modeProj (mercerEigenfun d β α hDim hβ hα) j (k + 1) (wristbandUniform d) =
            (∫ u, mercerEigenfun d β α hDim hβ hα j u
              ∂(sphereUniform d : Measure (Sphere d))) *
            (∫ t : UnitInterval, radialFeature (k + 1) t
              ∂(uniform01 : Measure UnitInterval)) := by
        unfold modeProj wristbandUniform productLaw
        simpa using
          (integral_prod_mul
            (μ := (sphereUniform d : Measure (Sphere d)))
            (ν := (uniform01 : Measure UnitInterval))
            (f := fun u : Sphere d => mercerEigenfun d β α hDim hβ hα j u)
            (g := fun t : UnitInterval => radialFeature (k + 1) t))
      have hRad :
          ∫ t : UnitInterval, radialFeature (k + 1) t
            ∂(uniform01 : Measure UnitInterval) = 0 :=
        radialFeature_cosine_integral_zero k
      calc
        modeProj (mercerEigenfun d β α hDim hβ hα) j (k + 1) (wristbandUniform d)
            =
          (∫ u, mercerEigenfun d β α hDim hβ hα j u
            ∂(sphereUniform d : Measure (Sphere d))) *
          (∫ t : UnitInterval, radialFeature (k + 1) t
            ∂(uniform01 : Measure UnitInterval)) := hFactor
        _ = 0 := by simp [hRad]

/-! ### Interchange helper for double `tsum` -/

/-- Commute a double `tsum` with an integral under explicit summability assumptions.

This is the core technical pattern needed in S4 (the `∫∫ Σ = Σ ∫∫` step), factored
as a reusable lemma so S4 can focus on instantiating hypotheses for the specific
spectral kernel term family. -/
lemma integral_tsum_tsum_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (F : ℕ → ℕ → α → ℝ)
    (hInt : ∀ j k, Integrable (F j k) μ)
    (hRowNorm : ∀ j, Summable (fun k => ∫ a, ‖F j k a‖ ∂μ))
    (hOuterInt : ∀ j, Integrable (fun a => ∑' k, F j k a) μ)
    (hOuterNorm : Summable (fun j => ∫ a, ‖∑' k, F j k a‖ ∂μ)) :
    ∫ a, ∑' j, ∑' k, F j k a ∂μ = ∑' j, ∑' k, ∫ a, F j k a ∂μ := by
  have hRowEq :
      ∀ j, ∫ a, ∑' k, F j k a ∂μ = ∑' k, ∫ a, F j k a ∂μ := by
    intro j
    symm
    exact integral_tsum_of_summable_integral_norm (hInt j) (hRowNorm j)
  have hOuterEq :
      ∫ a, ∑' j, ∑' k, F j k a ∂μ = ∑' j, ∫ a, ∑' k, F j k a ∂μ := by
    symm
    exact integral_tsum_of_summable_integral_norm hOuterInt hOuterNorm
  calc
    ∫ a, ∑' j, ∑' k, F j k a ∂μ
        = ∑' j, ∫ a, ∑' k, F j k a ∂μ := hOuterEq
    _ = ∑' j, ∑' k, ∫ a, F j k a ∂μ := by
      refine tsum_congr ?_
      intro j
      exact hRowEq j

/-! ### The main spectral energy identity -/

/-- **Spectral energy equals kernel energy**.

    `spectralEnergy φ λv a0 a P = kernelEnergy (wristbandKernelNeumann β α) P`

    7-step proof sketch:
    1. Unfold `kernelEnergy` and `wristbandKernelNeumann` as a product of factors.
    2. Substitute the Mercer expansion (A1_bundle clause 3) for the angular factor:
       `k_ang(u,v) = Σ'_j λv_j · φ_j(u) · φ_j(v)`.
    3. Substitute the radial expansion (`kernelRadNeumann_hasCosineExpansion`) for
       the radial factor: `k_rad(t,t') = Σ'_k radialCoeff a0 a k · f_k(t) · f_k(t')`.
    4. Interchange `∫∫` and `Σ'_j Σ'_k` using C1 (`MeasureTheory.integral_tsum`)
       with a dominated convergence / non-negativity argument.
    5. Swap the two `tsum`s using C2 (`ENNReal.tsum_comm`) for non-negative terms.
    6. Factor `Σ_i f(i) · Σ_j f(j) = (Σ f)²` using C3 (`tsum_mul_left/right`).
    7. Apply D1 (`MeasureTheory.integral_prod_mul`) to factor the joint integrals
       into the product form defining `modeProj φ j k P`. -/
lemma spectralEnergy_eq_kernelEnergy
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P =
      kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  sorry

/-! ### Non-negative excess energy -/

/-- **Spectral energy at uniform is the minimum**.

    `spectralEnergy φ λv a0 a (wristbandUniform d) ≤ spectralEnergy φ λv a0 a P`

    Proof sketch:
    - At `wristbandUniform d`: the (0,0) term contributes `λv 0 · a0 · 1²` and
      all other terms contribute 0 (by `modeProj_vanishes_at_uniform`).
      So `spectralEnergy μ₀ = λv 0 · a0`.
    - For any P: the (0,0) term still contributes `λv 0 · a0 · 1²` (by
      `modeProj_zero_zero_eq_one`), plus non-negative extra terms.
    - The difference `spectralEnergy P - spectralEnergy μ₀` is a sum
      `Σ_{(j,k)≠(0,0)} λv j · radialCoeff a0 a k · (modeProj j k P)² ≥ 0`.

    Mathlib route: `tsum_nonneg` + pointwise non-negativity of each term. -/
lemma spectralEnergy_nonneg_excess
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        (wristbandUniform d) ≤
      spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P := by
  sorry

end WristbandLossProofs
