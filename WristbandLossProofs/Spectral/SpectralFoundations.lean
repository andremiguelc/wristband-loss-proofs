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
| `angularEigenfun_integral_zero` | from orthonormality (A1_bundle clause 2+4) | local 3-liner |
| `sphereMean_zero` | antipodal symmetry of `sphereUniform` | `integral_map` + axiom |
| `modeProj_zero_zero_eq_one` | A1 clause 4: `φ 0 = 1`, `radialFeature 0 = 1` | trivial |
| `modeProj_vanishes_at_uniform` | angular/radial zero-mean factors via Fubini | local |
| `spectralEnergy_eq_kernelEnergy` | 7-step algebra: A1 + radial expansion + Fubini | `integral_tsum`, `tsum` algebra, `integral_prod_mul` |
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

/-! ### Kernel Expansion Wrappers -/

/-- Angular expansion rewritten in extracted witness notation. -/
lemma kernelAngChordal_mercerExpansion_witness
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (u v : Sphere d) :
    kernelAngChordal β α u v =
      ∑' j : ℕ,
        mercerEigenval d β α hDim hβ hα j *
          mercerEigenfun d β α hDim hβ hα j u *
          mercerEigenfun d β α hDim hβ hα j v :=
  (kernelAngChordal_mercerExpansion d β α hDim hβ hα).choose_spec.choose_spec.2.2.1 u v

/-- Radial cosine expansion rewritten in extracted witness notation. -/
lemma kernelRadNeumann_cosineExpansion_witness
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    kernelRadNeumann β t t' =
      neumannConstantCoeff β hβ +
        ∑' k : ℕ,
          neumannCosineCoeff β hβ k *
            Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t : ℝ)) *
            Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t' : ℝ)) :=
  (kernelRadNeumann_hasCosineExpansion β hβ).choose_spec.choose_spec.2.2 t t'

/-- Extended-index radial expansion, under an explicit summability hypothesis. -/
lemma kernelRadNeumann_spectralExpansion_extended_of_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval)
    (hSumm :
      Summable
        (fun k : ℕ =>
          neumannRadialCoeff β hβ k * radialFeature k t * radialFeature k t')) :
    kernelRadNeumann β t t' =
      ∑' k : ℕ,
        neumannRadialCoeff β hβ k * radialFeature k t * radialFeature k t' := by
  let term : ℕ → ℝ := fun k =>
    neumannRadialCoeff β hβ k * radialFeature k t * radialFeature k t'
  have hRaw := kernelRadNeumann_cosineExpansion_witness β hβ t t'
  have hZeroAdd : (∑' k : ℕ, term k) = term 0 + ∑' k : ℕ, term (k + 1) :=
    hSumm.tsum_eq_zero_add
  calc
    kernelRadNeumann β t t'
        = neumannConstantCoeff β hβ +
            ∑' k : ℕ,
              neumannCosineCoeff β hβ k *
                Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t : ℝ)) *
                Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t' : ℝ)) := hRaw
    _ = term 0 + ∑' k : ℕ, term (k + 1) := by
      simp [term, neumannRadialCoeff, radialCoeff, radialFeature]
    _ = ∑' k : ℕ, term k := hZeroAdd.symm
    _ = ∑' k : ℕ,
          neumannRadialCoeff β hβ k * radialFeature k t * radialFeature k t' := by
      rfl

/- TODO(kernelRadNeumann_extended_index, pinned):
To remove the explicit `Summable` hypothesis in
`kernelRadNeumann_spectralExpansion_extended_of_summable`, we need one of:

1. Imported strengthening:
   extend the radial imported fact to also provide summability of the cosine
   witness sequence (equivalently, of the extended-index sequence) at each
   `(t, t')`.
2. Local derivation:
   prove summability of the extended-index sequence from existing imported data,
   then build an unconditional wrapper lemma.

Until that is discharged, downstream helper lemmas can thread this summability
assumption explicitly. -/

/-! ### Integrals Vanishing At Uniform Measure -/

/-- Non-constant angular eigenfunctions integrate to zero under `sphereUniform`.

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

/-- Cosine features integrate to zero under `uniform01`.

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
    - `k = 0, j > 0`: `modeProj φ j 0 μ₀ = (∫ φ_j dσ) · (∫ 1 dt) = 0 · 1 = 0`.
    - `k ≥ 1, any j`: `modeProj φ j k μ₀ = (∫ φ_j dσ) · (∫ cos(k·π·t) dt) = (?) · 0 = 0`
      because the cosine integral is 0 and factoring is valid by Fubini.

    Proof route: use `MeasureTheory.integral_prod_mul` to factor the
    wristband integral into angular × radial, then apply the angular/radial
    zero-mean lemmas. -/
lemma modeProj_vanishes_at_uniform
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j k : ℕ) (hjk : j ≠ 0 ∨ k ≠ 0) :
    modeProj (mercerEigenfun d β α hDim hβ hα) j k (wristbandUniform d) = 0 := by
  -- Unfold modeProj and wristbandUniform = productLaw sphereUniform uniform01.
  -- Apply integral_prod_mul to factor into angular × radial integrals.
  -- For k = 0 and j > 0: angular factor = ∫ φ_j dσ = 0.
  -- For k ≥ 1: radial factor = ∫ radialFeature k dt = 0.
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

/-- Mode feature on wristband space for spectral index `(j, k)`. -/
noncomputable def modeTerm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j k : ℕ) (w : Wristband d) : ℝ :=
  mercerEigenfun d β α hDim hβ hα j w.1 * radialFeature k w.2

/-- Weighted rank-one kernel term for fixed spectral index `(j, k)`. -/
noncomputable def spectralKernelTerm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (j k : ℕ) (w w' : Wristband d) : ℝ :=
  mercerEigenval d β α hDim hβ hα j *
    neumannRadialCoeff β hβ k *
    modeTerm β α hDim hβ hα j k w *
    modeTerm β α hDim hβ hα j k w'

/-- Pointwise kernel expansion as a double `tsum`, under explicit
summability assumptions for the angular and radial mode families at `(w, w')`. -/
lemma wristbandKernelNeumann_eq_double_tsum_modeTerm_of_summable
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (w w' : Wristband d)
    (hSummAng :
      Summable
        (fun j : ℕ =>
          mercerEigenval d β α hDim hβ hα j *
            mercerEigenfun d β α hDim hβ hα j w.1 *
            mercerEigenfun d β α hDim hβ hα j w'.1))
    (hSummRad :
      Summable
        (fun k : ℕ =>
          neumannRadialCoeff β hβ k * radialFeature k w.2 * radialFeature k w'.2)) :
    wristbandKernelNeumann (d := d) β α w w' =
      ∑' j : ℕ, ∑' k : ℕ,
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          modeTerm β α hDim hβ hα j k w *
          modeTerm β α hDim hβ hα j k w' := by
  let A : ℕ → ℝ := fun j =>
    mercerEigenval d β α hDim hβ hα j *
      mercerEigenfun d β α hDim hβ hα j w.1 *
      mercerEigenfun d β α hDim hβ hα j w'.1
  let B : ℕ → ℝ := fun k =>
    neumannRadialCoeff β hβ k * radialFeature k w.2 * radialFeature k w'.2
  have hAng : kernelAngChordal β α w.1 w'.1 = ∑' j : ℕ, A j := by
    simpa [A] using kernelAngChordal_mercerExpansion_witness β α hDim hβ hα w.1 w'.1
  have hRad : kernelRadNeumann β w.2 w'.2 = ∑' k : ℕ, B k := by
    simpa [B] using
      kernelRadNeumann_spectralExpansion_extended_of_summable β hβ w.2 w'.2 hSummRad
  calc
    wristbandKernelNeumann (d := d) β α w w' = (∑' j : ℕ, A j) * (∑' k : ℕ, B k) := by
      simpa [wristbandKernelNeumann, hAng, hRad]
    _ = ∑' j : ℕ, A j * (∑' k : ℕ, B k) := by
      symm
      simpa using (Summable.tsum_mul_right (a := ∑' k : ℕ, B k) hSummAng)
    _ = ∑' j : ℕ, ∑' k : ℕ, A j * B k := by
      refine tsum_congr ?_
      intro j
      symm
      simpa using (Summable.tsum_mul_left (a := A j) hSummRad)
    _ = ∑' j : ℕ, ∑' k : ℕ,
          mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ k *
            modeTerm β α hDim hβ hα j k w *
            modeTerm β α hDim hβ hα j k w' := by
      refine tsum_congr ?_
      intro j
      refine tsum_congr ?_
      intro k
      simp [A, B, modeTerm]
      ring

/-- Commute a double `tsum` with an integral under explicit summability assumptions.

This is the core technical pattern for the kernel-energy identity
(the `∫∫ Σ = Σ ∫∫` step), factored as a reusable lemma so later proofs can
focus on instantiating hypotheses for the specific spectral kernel term family. -/
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

/-- Outer-swap lemma: commute the outer integral with the double `tsum`
for the spectral kernel term family, under explicit summability assumptions. -/
lemma kernelEnergy_outer_tsum_tsum_interchange_of_summable_integral_norm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hInt : ∀ j k,
      Integrable
        (fun w : Wristband d =>
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hRowNorm : ∀ j,
      Summable
        (fun k =>
          ∫ w,
            ‖∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d))))
    (hOuterInt : ∀ j,
      Integrable
        (fun w : Wristband d =>
          ∑' k,
            ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hOuterNorm :
      Summable
        (fun j =>
          ∫ w,
            ‖∑' k,
                ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                    ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d)))) :
    (∫ w,
      ∑' j, ∑' k,
        (∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d)))
      ∂(P : Measure (Wristband d)))
      =
    ∑' j, ∑' k,
      ∫ w,
        ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d))
      ∂(P : Measure (Wristband d)) := by
  simpa using
    (integral_tsum_tsum_of_summable_integral_norm
      (μ := (P : Measure (Wristband d)))
      (F := fun j k (w : Wristband d) =>
        ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d)))
      hInt hRowNorm hOuterInt hOuterNorm)

/-- Fixed-mode double integral factors into the square of `modeProj`. -/
lemma modeTerm_double_integral_eq_modeProj_sq
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (j k : ℕ) :
    (∫ w, ∫ w',
      modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
    =
    (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
  let I : ℝ :=
    ∫ w, modeTerm β α hDim hβ hα j k w ∂(P : Measure (Wristband d))
  calc
    (∫ w, ∫ w',
      modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
        = ∫ w, modeTerm β α hDim hβ hα j k w * I ∂(P : Measure (Wristband d)) := by
            refine integral_congr_ae ?_
            filter_upwards with w
            simpa [I] using
              (integral_const_mul
                (μ := (P : Measure (Wristband d)))
                (modeTerm β α hDim hβ hα j k w)
                (fun w' : Wristband d => modeTerm β α hDim hβ hα j k w'))
    _ = I * I := by
          simpa [I] using
            (integral_mul_const
              I
              (fun w : Wristband d => modeTerm β α hDim hβ hα j k w))
    _ = (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
          simp [I, modeProj, modeTerm, pow_two]

/-- Pull fixed spectral coefficients out of the double integral. -/
lemma coeff_mul_modeTerm_double_integral
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (j k : ℕ) :
    (∫ w, ∫ w',
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        modeTerm β α hDim hβ hα j k w *
        modeTerm β α hDim hβ hα j k w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
    =
    mercerEigenval d β α hDim hβ hα j *
      neumannRadialCoeff β hβ k *
      (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
  let c : ℝ := mercerEigenval d β α hDim hβ hα j * neumannRadialCoeff β hβ k
  calc
    (∫ w, ∫ w',
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        modeTerm β α hDim hβ hα j k w *
        modeTerm β α hDim hβ hα j k w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
        =
      (∫ w, ∫ w', c *
          (modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w')
        ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d))) := by
          refine integral_congr_ae ?_
          filter_upwards with w
          refine integral_congr_ae ?_
          filter_upwards with w'
          ring
    _ =
      (∫ w, c *
          (∫ w',
            modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'
            ∂(P : Measure (Wristband d)))
        ∂(P : Measure (Wristband d))) := by
          refine integral_congr_ae ?_
          filter_upwards with w
          simpa using
            (integral_const_mul
              (μ := (P : Measure (Wristband d)))
              c
              (fun w' : Wristband d =>
                modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'))
    _ =
      c *
        (∫ w, ∫ w',
          modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'
          ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d))) := by
            simpa using
              (integral_const_mul
                (μ := (P : Measure (Wristband d)))
                c
                (fun w : Wristband d =>
                  ∫ w',
                    modeTerm β α hDim hβ hα j k w * modeTerm β α hDim hβ hα j k w'
                    ∂(P : Measure (Wristband d))))
    _ = c * (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
          rw [modeTerm_double_integral_eq_modeProj_sq β α hDim hβ hα P j k]
    _ = mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
          simp [c]

/-- Full `∫∫` with double `tsum` interchange, under explicit inner and
outer summability/integrability assumptions. -/
lemma kernelEnergy_double_tsum_interchange_of_summable_integral_norm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hInnerInt : ∀ w j k,
      Integrable
        (fun w' : Wristband d => spectralKernelTerm β α hDim hβ hα j k w w')
        (P : Measure (Wristband d)))
    (hInnerRowNorm : ∀ w j,
      Summable
        (fun k =>
          ∫ w',
            ‖spectralKernelTerm β α hDim hβ hα j k w w'‖
          ∂(P : Measure (Wristband d))))
    (hInnerOuterInt : ∀ w j,
      Integrable
        (fun w' : Wristband d =>
          ∑' k, spectralKernelTerm β α hDim hβ hα j k w w')
        (P : Measure (Wristband d)))
    (hInnerOuterNorm : ∀ w,
      Summable
        (fun j =>
          ∫ w',
            ‖∑' k, spectralKernelTerm β α hDim hβ hα j k w w'‖
          ∂(P : Measure (Wristband d))))
    (hOuterInt : ∀ j k,
      Integrable
        (fun w : Wristband d =>
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hOuterRowNorm : ∀ j,
      Summable
        (fun k =>
          ∫ w,
            ‖∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d))))
    (hOuterOuterInt : ∀ j,
      Integrable
        (fun w : Wristband d =>
          ∑' k,
            ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hOuterOuterNorm :
      Summable
        (fun j =>
          ∫ w,
            ‖∑' k,
                ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                    ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d)))) :
    (∫ w, ∫ w',
      ∑' j, ∑' k, spectralKernelTerm β α hDim hβ hα j k w w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
      =
    ∑' j, ∑' k,
      ∫ w,
        ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d))
      ∂(P : Measure (Wristband d)) := by
  have hInnerSwap :
      (∫ w, ∫ w',
        ∑' j, ∑' k, spectralKernelTerm β α hDim hβ hα j k w w'
        ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
        =
      (∫ w,
        ∑' j, ∑' k,
          (∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d)))
        ∂(P : Measure (Wristband d))) := by
    refine integral_congr_ae ?_
    filter_upwards with w
    simpa using
      (integral_tsum_tsum_of_summable_integral_norm
        (μ := (P : Measure (Wristband d)))
        (F := fun j k (w' : Wristband d) => spectralKernelTerm β α hDim hβ hα j k w w')
        (hInt := hInnerInt w)
        (hRowNorm := hInnerRowNorm w)
        (hOuterInt := hInnerOuterInt w)
        (hOuterNorm := hInnerOuterNorm w))
  have hOuterSwap :=
    kernelEnergy_outer_tsum_tsum_interchange_of_summable_integral_norm
      β α hDim hβ hα P hOuterInt hOuterRowNorm hOuterOuterInt hOuterOuterNorm
  exact hInnerSwap.trans hOuterSwap

/-- Conditional assembly: rewrite `kernelEnergy` as the spectral double sum,
assuming pointwise kernel expansion and justified interchange. -/
lemma kernelEnergy_eq_spectralEnergy_sum_of_expansion_and_interchange
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPointwise : ∀ w w',
      wristbandKernelNeumann (d := d) β α w w' =
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w')
    (hInterchange :
      (∫ w, ∫ w',
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w'
        ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
        =
      ∑' j : ℕ, ∑' k : ℕ,
        ∫ w,
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d))
        ∂(P : Measure (Wristband d))) :
    kernelEnergy (wristbandKernelNeumann (d := d) β α) P =
      ∑' j : ℕ, ∑' k : ℕ,
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
  calc
    kernelEnergy (wristbandKernelNeumann (d := d) β α) P
        =
      (∫ w, ∫ w',
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w'
        ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d))) := by
          unfold kernelEnergy
          refine integral_congr_ae ?_
          filter_upwards with w
          refine integral_congr_ae ?_
          filter_upwards with w'
          exact hPointwise w w'
    _ =
      ∑' j : ℕ, ∑' k : ℕ,
        ∫ w,
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d))
        ∂(P : Measure (Wristband d)) := hInterchange
    _ =
      ∑' j : ℕ, ∑' k : ℕ,
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
          refine tsum_congr ?_
          intro j
          refine tsum_congr ?_
          intro k
          simpa [spectralKernelTerm] using
            (coeff_mul_modeTerm_double_integral β α hDim hβ hα P j k)

/-! ### Kernel-Energy Bridge Lemmas (Conditional Assembly) -/

/-- Conditional bridge: once pointwise expansion and `∫∫`/`Σ` interchange are
available, `spectralEnergy` and `kernelEnergy` are equal. -/
lemma spectralEnergy_eq_kernelEnergy_of_expansion_and_interchange
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPointwise : ∀ w w',
      wristbandKernelNeumann (d := d) β α w w' =
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w')
    (hInterchange :
      (∫ w, ∫ w',
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w'
        ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
        =
      ∑' j : ℕ, ∑' k : ℕ,
        ∫ w,
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d))
        ∂(P : Measure (Wristband d))) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P =
      kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  have hMain :=
    kernelEnergy_eq_spectralEnergy_sum_of_expansion_and_interchange
      β α hDim hβ hα P hPointwise hInterchange
  calc
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P
        =
      ∑' j : ℕ, ∑' k : ℕ,
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
            rfl
    _ = kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
          simpa using hMain.symm

/-- Technical assumption package for the spectral kernel-energy identity:
pointwise summability (for expansion) plus integrability/norm-summability
for the double-`tsum` interchange. -/
structure KernelExpansionInterchangeAssumptions
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) : Prop where
  hPointwiseAng : ∀ (w w' : Wristband d),
    Summable
      (fun j : ℕ =>
        mercerEigenval d β α hDim hβ hα j *
          mercerEigenfun d β α hDim hβ hα j w.1 *
          mercerEigenfun d β α hDim hβ hα j w'.1)
  hPointwiseRad : ∀ (w w' : Wristband d),
    Summable
      (fun k : ℕ =>
        neumannRadialCoeff β hβ k * radialFeature k w.2 * radialFeature k w'.2)
  hInnerInt : ∀ w j k,
    Integrable
      (fun w' : Wristband d => spectralKernelTerm β α hDim hβ hα j k w w')
      (P : Measure (Wristband d))
  hInnerRowNorm : ∀ w j,
    Summable
      (fun k =>
        ∫ w',
          ‖spectralKernelTerm β α hDim hβ hα j k w w'‖
        ∂(P : Measure (Wristband d)))
  hInnerOuterInt : ∀ w j,
    Integrable
      (fun w' : Wristband d =>
        ∑' k, spectralKernelTerm β α hDim hβ hα j k w w')
      (P : Measure (Wristband d))
  hInnerOuterNorm : ∀ w,
    Summable
      (fun j =>
        ∫ w',
          ‖∑' k, spectralKernelTerm β α hDim hβ hα j k w w'‖
        ∂(P : Measure (Wristband d)))
  hOuterInt : ∀ j k,
    Integrable
      (fun w : Wristband d =>
        ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d)))
      (P : Measure (Wristband d))
  hOuterRowNorm : ∀ j,
    Summable
      (fun k =>
        ∫ w,
          ‖∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d))‖
          ∂(P : Measure (Wristband d)))
  hOuterOuterInt : ∀ j,
    Integrable
      (fun w : Wristband d =>
        ∑' k,
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d)))
      (P : Measure (Wristband d))
  hOuterOuterNorm :
    Summable
      (fun j =>
        ∫ w,
          ‖∑' k,
              ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                  ∂(P : Measure (Wristband d))‖
          ∂(P : Measure (Wristband d)))

/-- Build the pointwise `spectralKernelTerm` expansion from
the summability fields in `KernelExpansionInterchangeAssumptions`. -/
lemma wristbandKernelNeumann_eq_double_tsum_spectralKernelTerm_of_package
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPkg : KernelExpansionInterchangeAssumptions β α hDim hβ hα P) :
    ∀ w w',
      wristbandKernelNeumann (d := d) β α w w' =
        ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w' := by
  intro w w'
  simpa [spectralKernelTerm] using
    (wristbandKernelNeumann_eq_double_tsum_modeTerm_of_summable
      β α hDim hβ hα w w' (hPkg.hPointwiseAng w w') (hPkg.hPointwiseRad w w'))

/-- Build the full `∫∫`/double-`tsum` interchange from
the integrability and norm-summability fields in the package. -/
lemma kernelEnergy_double_tsum_interchange_of_package
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPkg : KernelExpansionInterchangeAssumptions β α hDim hβ hα P) :
    (∫ w, ∫ w',
      ∑' j : ℕ, ∑' k : ℕ, spectralKernelTerm β α hDim hβ hα j k w w'
      ∂(P : Measure (Wristband d)) ∂(P : Measure (Wristband d)))
      =
    ∑' j : ℕ, ∑' k : ℕ,
      ∫ w,
        ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
            ∂(P : Measure (Wristband d))
      ∂(P : Measure (Wristband d)) := by
  exact
    kernelEnergy_double_tsum_interchange_of_summable_integral_norm
      β α hDim hβ hα P
      hPkg.hInnerInt hPkg.hInnerRowNorm hPkg.hInnerOuterInt hPkg.hInnerOuterNorm
      hPkg.hOuterInt hPkg.hOuterRowNorm hPkg.hOuterOuterInt hPkg.hOuterOuterNorm

/-- Conditional identity in final shape, parameterized by a single technical package.
This is the current endpoint pending unconditional wrappers. -/
lemma spectralEnergy_eq_kernelEnergy_of_package
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPkg : KernelExpansionInterchangeAssumptions β α hDim hβ hα P) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P =
      kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  exact
    spectralEnergy_eq_kernelEnergy_of_expansion_and_interchange
      β α hDim hβ hα P
      (wristbandKernelNeumann_eq_double_tsum_spectralKernelTerm_of_package
        β α hDim hβ hα P hPkg)
      (kernelEnergy_double_tsum_interchange_of_package β α hDim hβ hα P hPkg)

/-- Conditional end-to-end wrapper: instantiate pointwise expansion and
integral/sum interchange assumptions directly. -/
lemma spectralEnergy_eq_kernelEnergy_of_summable_integral_norm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hPointwiseAng : ∀ (w w' : Wristband d),
      Summable
        (fun j : ℕ =>
          mercerEigenval d β α hDim hβ hα j *
            mercerEigenfun d β α hDim hβ hα j w.1 *
            mercerEigenfun d β α hDim hβ hα j w'.1))
    (hPointwiseRad : ∀ (w w' : Wristband d),
      Summable
        (fun k : ℕ =>
          neumannRadialCoeff β hβ k * radialFeature k w.2 * radialFeature k w'.2))
    (hInnerInt : ∀ w j k,
      Integrable
        (fun w' : Wristband d => spectralKernelTerm β α hDim hβ hα j k w w')
        (P : Measure (Wristband d)))
    (hInnerRowNorm : ∀ w j,
      Summable
        (fun k =>
          ∫ w',
            ‖spectralKernelTerm β α hDim hβ hα j k w w'‖
          ∂(P : Measure (Wristband d))))
    (hInnerOuterInt : ∀ w j,
      Integrable
        (fun w' : Wristband d =>
          ∑' k, spectralKernelTerm β α hDim hβ hα j k w w')
        (P : Measure (Wristband d)))
    (hInnerOuterNorm : ∀ w,
      Summable
        (fun j =>
          ∫ w',
            ‖∑' k, spectralKernelTerm β α hDim hβ hα j k w w'‖
          ∂(P : Measure (Wristband d))))
    (hOuterInt : ∀ j k,
      Integrable
        (fun w : Wristband d =>
          ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
              ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hOuterRowNorm : ∀ j,
      Summable
        (fun k =>
          ∫ w,
            ‖∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d))))
    (hOuterOuterInt : ∀ j,
      Integrable
        (fun w : Wristband d =>
          ∑' k,
            ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                ∂(P : Measure (Wristband d)))
        (P : Measure (Wristband d)))
    (hOuterOuterNorm :
      Summable
        (fun j =>
          ∫ w,
            ‖∑' k,
                ∫ w', spectralKernelTerm β α hDim hβ hα j k w w'
                    ∂(P : Measure (Wristband d))‖
            ∂(P : Measure (Wristband d)))) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P =
      kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  let hPkg : KernelExpansionInterchangeAssumptions β α hDim hβ hα P :=
    { hPointwiseAng := hPointwiseAng
      hPointwiseRad := hPointwiseRad
      hInnerInt := hInnerInt
      hInnerRowNorm := hInnerRowNorm
      hInnerOuterInt := hInnerOuterInt
      hInnerOuterNorm := hInnerOuterNorm
      hOuterInt := hOuterInt
      hOuterRowNorm := hOuterRowNorm
      hOuterOuterInt := hOuterOuterInt
      hOuterOuterNorm := hOuterOuterNorm }
  exact spectralEnergy_eq_kernelEnergy_of_package β α hDim hβ hα P hPkg

/- TODO(spectralEnergy_eq_kernelEnergy, pinned):
To replace the `sorry` in `spectralEnergy_eq_kernelEnergy`, we need to discharge
the hypotheses currently made explicit in
`spectralEnergy_eq_kernelEnergy_of_summable_integral_norm`.

Concretely, we still need packaged assumptions/lemmas for:
1. Pointwise summability of the angular series at every `(w, w')`.
2. Pointwise summability of the extended radial series at every `(w, w')`
   (this is linked to TODO(kernelRadNeumann_extended_index)).
3. The inner/outer integrability + norm-summability side conditions required by
   `kernelEnergy_double_tsum_interchange_of_summable_integral_norm`.

Likely completion path:
- either strengthen imported facts so these are available in witness form, or
- add local wrappers that derive them from existing imported assumptions. -/

/-! ### The main spectral energy identity -/

/-- **Spectral energy equals kernel energy**.

    `spectralEnergy φ λv a0 a P = kernelEnergy (wristbandKernelNeumann β α) P`

    7-step proof sketch:
    1. Unfold `kernelEnergy` and `wristbandKernelNeumann` as a product of factors.
    2. Substitute the Mercer expansion (A1_bundle clause 3) for the angular factor:
       `k_ang(u,v) = Σ'_j λv_j · φ_j(u) · φ_j(v)`.
    3. Substitute the radial expansion (`kernelRadNeumann_hasCosineExpansion`) for
       the radial factor: `k_rad(t,t') = Σ'_k radialCoeff a0 a k · f_k(t) · f_k(t')`.
    4. Interchange `∫∫` and `Σ'_j Σ'_k` using `MeasureTheory.integral_tsum`
       with a dominated convergence / non-negativity argument.
    5. Swap the two `tsum`s using `ENNReal.tsum_comm` for non-negative terms.
    6. Factor `Σ_i f(i) · Σ_j f(j) = (Σ f)²` using `tsum_mul_left/right`.
    7. Apply `MeasureTheory.integral_prod_mul` to factor the joint integrals
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

/-- Non-negativity of each spectral summand. -/
lemma spectralEnergy_term_nonneg
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (j k : ℕ) :
    0 ≤
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
  exact mul_nonneg
    (mul_nonneg
      (mercerEigenval_nonneg d β α hDim hβ hα j)
      (neumannRadialCoeff_nonneg β hβ k))
    (sq_nonneg _)

/-- Spectral energy at `wristbandUniform` equals the `(0,0)` mode contribution. -/
lemma spectralEnergy_uniform_eq_mode00
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        (wristbandUniform d)
      =
    mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 := by
  let termU : ℕ → ℕ → ℝ :=
    fun j k =>
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k (wristbandUniform d)) ^ 2
  have hUniformInner :
      ∀ j : ℕ,
        (∑' k : ℕ, termU j k) =
          if j = 0 then
            mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0
          else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      have hZeroTail : ∀ k : ℕ, k ≠ 0 → termU 0 k = 0 := by
        intro k hk
        have hMode :
            modeProj (mercerEigenfun d β α hDim hβ hα) 0 k (wristbandUniform d) = 0 :=
          modeProj_vanishes_at_uniform β α hDim hβ hα 0 k (Or.inr hk)
        simp [termU, hMode]
      calc
        (∑' k : ℕ, termU 0 k)
            = termU 0 0 := tsum_eq_single 0 hZeroTail
        _ = mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 := by
              simp [termU, modeProj_zero_zero_eq_one β α hDim hβ hα (wristbandUniform d)]
    · have hAllZero : ∀ k : ℕ, termU j k = 0 := by
        intro k
        have hMode :
            modeProj (mercerEigenfun d β α hDim hβ hα) j k (wristbandUniform d) = 0 :=
          modeProj_vanishes_at_uniform β α hDim hβ hα j k (Or.inl hj)
        simp [termU, hMode]
      have hZeroTail : ∀ k : ℕ, k ≠ 0 → termU j k = 0 := by
        intro k hk
        exact hAllZero k
      calc
        (∑' k : ℕ, termU j k)
            = termU j 0 := tsum_eq_single 0 hZeroTail
        _ = 0 := hAllZero 0
        _ = if j = 0 then mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 else 0 := by
              simp [hj]
  calc
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        (wristbandUniform d)
        = ∑' j : ℕ, ∑' k : ℕ, termU j k := by
              rfl
    _ = ∑' j : ℕ,
          (if j = 0 then
            mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0
           else 0) := by
          refine tsum_congr ?_
          intro j
          exact hUniformInner j
    _ = mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 := by
          simpa using
            (tsum_ite_eq 0
              (fun _ : ℕ =>
                mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0))

/-- Under explicit summability of spectral mode series, the `(0,0)` mode
contribution is a lower bound for spectral energy at `P`. -/
lemma spectralEnergy_mode00_le_of_summable
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hSummInner : ∀ j : ℕ,
      Summable
        (fun k : ℕ =>
          mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ k *
            (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2))
    (hSummOuter :
      Summable
        (fun j : ℕ =>
          ∑' k : ℕ,
            mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ k *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2)) :
    mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0
      ≤
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P := by
  let termP : ℕ → ℕ → ℝ :=
    fun j k =>
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2
  have hTermPNonneg : ∀ j k : ℕ, 0 ≤ termP j k := by
    intro j k
    exact spectralEnergy_term_nonneg β α hDim hβ hα P j k
  have hP00Eq :
      termP 0 0 =
        mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 := by
    simp [termP, modeProj_zero_zero_eq_one β α hDim hβ hα P]
  have hInner0Le :
      termP 0 0 ≤ ∑' k : ℕ, termP 0 k := by
    simpa using
      (hSummInner 0).sum_le_tsum
        (s := ({0} : Finset ℕ))
        (by
          intro k hk
          exact hTermPNonneg 0 k)
  have hOuterNonneg : ∀ j : ℕ, 0 ≤ ∑' k : ℕ, termP j k := by
    intro j
    exact tsum_nonneg (hTermPNonneg j)
  have hOuterLe :
      (∑' k : ℕ, termP 0 k) ≤
        ∑' j : ℕ, ∑' k : ℕ, termP j k := by
    simpa using
      hSummOuter.sum_le_tsum
        (s := ({0} : Finset ℕ))
        (by
          intro j hj
          exact hOuterNonneg j)
  calc
    mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0
        = termP 0 0 := hP00Eq.symm
    _ ≤ ∑' k : ℕ, termP 0 k := hInner0Le
    _ ≤ ∑' j : ℕ, ∑' k : ℕ, termP j k := hOuterLe
    _ =
        spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          P := by
          rfl

/-- Conditional non-negative excess inequality under explicit summability
assumptions for the spectral mode series at `P`. -/
lemma spectralEnergy_nonneg_excess_of_summable
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hSummInner : ∀ j : ℕ,
      Summable
        (fun k : ℕ =>
          mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ k *
            (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2))
    (hSummOuter :
      Summable
        (fun j : ℕ =>
          ∑' k : ℕ,
            mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ k *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2)) :
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
  calc
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        (wristbandUniform d)
        = mercerEigenval d β α hDim hβ hα 0 * neumannRadialCoeff β hβ 0 :=
          spectralEnergy_uniform_eq_mode00 β α hDim hβ hα
    _ ≤
      spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P :=
          spectralEnergy_mode00_le_of_summable β α hDim hβ hα P hSummInner hSummOuter

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
