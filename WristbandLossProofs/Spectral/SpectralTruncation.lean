import WristbandLossProofs.Spectral.SpectralFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory Filter
open scoped BigOperators

/-! ## Spectral Truncation — joint (L, K) bounds

Theorems about `spectralEnergyTruncated` (the joint angular-and-radial truncation
of `spectralEnergy`, defined in `SpectralPrimitives.lean`).

**Naming convention.** Throughout this file, `K` is "highest mode index kept"
in the Lean sense, so `Finset.range (K + 1) = {0, 1, …, K}` indexes `K + 1`
modes. The Python implementation (`python/spectral/kernel.py`) and the math
docs (`docs/working/_spectral_what_and_why.md`) use the convention "number of
modes kept", so Python's `k_modes = 6, ell ≤ 1` corresponds here to
`K = 5, L = 1`.

**No new axioms.** All proofs use only the existing imported facts:
`spectral_modeL1_factorized_bridge_imported` (with its k-uniform majorant),
`summable_neumannCosineCoeff_imported`, plus `kernelAngChordal_mercerExpansion`
indirectly via the witness-extraction defs in `SpectralImportedFacts`.

### Phase 2: containment

  - `spectralEnergyTruncated_nonneg`            : `0 ≤ E_{L,K}(P)`
  - `spectralEnergyTruncated_le_spectralEnergy` : `E_{L,K}(P) ≤ spectralEnergy P`

### Phase 3: error bound (in progress)

The error `|spectralEnergy − spectralEnergyTruncated L K|` decomposes as
`angularTailMass · radialTotalMass + angularPrefixMass · radialTailMass`,
where the four mass quantities are defined below.
-/

/-! ### Phase 3: mass definitions -/

/-- Total radial mass: `∑' k, neumannRadialCoeff k`.  Finite because the
cosine coefficients are summable (and so is the extended `radialCoeff`). -/
noncomputable def radialTotalMass (β : ℝ) (hβ : 0 < β) : ℝ :=
  ∑' k : ℕ, neumannRadialCoeff β hβ k

/-- Radial tail mass beyond mode `K`: `∑' n, neumannRadialCoeff (n + K + 1)`,
i.e. the truncation overspill from dropping radial modes `> K`. -/
noncomputable def radialTailMass (β : ℝ) (hβ : 0 < β) (K : ℕ) : ℝ :=
  ∑' n : ℕ, neumannRadialCoeff β hβ (n + (K + 1))

/-- Angular prefix mass: finite sum over the kept Mercer modes
`j ∈ {0, …, L}` of `‖λv j‖ · (M j)²`, where `M` is the bridge axiom's
per-`j` L¹ majorant.  Inlined as `.choose` so the equality with a local
`M` from `obtain` is `rfl`. -/
noncomputable def angularPrefixMass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1),
    ‖mercerEigenval d β α hDim hβ hα j‖ *
      ((spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P).choose j) ^ 2

/-- Angular tail mass: `∑' i, ‖λv (i+L+1)‖ · (M (i+L+1))²` over Mercer modes
`j > L`.  Finite because the bridge gives the unshifted outer summability and
shifted summability follows from `summable_nat_add_iff`.  Inlined as `.choose`
so the equality with a local `M` from `obtain` is `rfl`. -/
noncomputable def angularTailMass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L : ℕ) : ℝ :=
  ∑' i : ℕ,
    ‖mercerEigenval d β α hDim hβ hα (i + (L + 1))‖ *
      ((spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P).choose
        (i + (L + 1))) ^ 2

/-- The joint-truncated spectral energy is non-negative.  Direct consequence of
the term-wise nonnegativity `spectralEnergy_term_nonneg`. -/
theorem spectralEnergyTruncated_nonneg
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    0 ≤
      spectralEnergyTruncated
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P := by
  unfold spectralEnergyTruncated
  refine Finset.sum_nonneg ?_
  intro j _
  refine Finset.sum_nonneg ?_
  intro k _
  exact spectralEnergy_term_nonneg β α hDim hβ hα P j k

/-- The joint-truncated spectral energy is bounded above by the full spectral
energy.

Proof outline.  Using the bridge axiom's k-uniform L¹ majorant `M : ℕ → ℝ`:
  1. Jensen on the bridge L¹ bound gives `(modeProj j k P)² ≤ (M j)²`.
  2. Pointwise: each summand `λv j · radialCoeff k · (modeProj j k P)²`
     is bounded by `λv j · (M j)² · radialCoeff k`.
  3. The radial-coefficient sequence is summable, so the inner radial tsum
     is summable per `j`.
  4. The bridge's outer summability `∑' j, ‖λv j‖·(M j)² < ∞` lifts to
     summability of `j ↦ ∑' k, f j k`.
  5. Apply `Summable.sum_le_tsum` once on each axis, finite outer over
     `Finset.range (L+1)` and finite inner over `Finset.range (K+1)`. -/
theorem spectralEnergyTruncated_le_spectralEnergy
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    spectralEnergyTruncated
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P
      ≤
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P := by
  let Φ := mercerEigenfun d β α hDim hβ hα
  let lamV := mercerEigenval d β α hDim hβ hα
  let f : ℕ → ℕ → ℝ := fun j k =>
    lamV j * neumannRadialCoeff β hβ k * (modeProj Φ j k P) ^ 2
  have hf_nonneg : ∀ j k, 0 ≤ f j k := fun j k =>
    spectralEnergy_term_nonneg β α hDim hβ hα P j k
  obtain ⟨M, hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ :=
    spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  have hLamNonneg : ∀ j, 0 ≤ lamV j := mercerEigenval_nonneg d β α hDim hβ hα
  have hRadNonneg : ∀ k, 0 ≤ neumannRadialCoeff β hβ k :=
    neumannRadialCoeff_nonneg β hβ
  -- Jensen: |modeProj j k P| ≤ M j (uniform in k).
  have hModeProjAbs : ∀ j k, |modeProj Φ j k P| ≤ M j := by
    intro j k
    have h₁ :
        ‖∫ w, Φ j w.1 * radialFeature k w.2 ∂(P : Measure (Wristband d))‖ ≤
          ∫ w, ‖Φ j w.1 * radialFeature k w.2‖ ∂(P : Measure (Wristband d)) :=
      norm_integral_le_integral_norm _
    have h₂ := h₁.trans (hModeL1Bound j k)
    simpa [modeProj, Real.norm_eq_abs] using h₂
  have hModeProjSq : ∀ j k, (modeProj Φ j k P) ^ 2 ≤ (M j) ^ 2 := by
    intro j k
    have h := hModeProjAbs j k
    have habs_sq : |modeProj Φ j k P| ^ 2 ≤ (M j) ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg _) h
      simpa [pow_two] using this
    simpa [sq_abs] using habs_sq
  -- Pointwise majorant: f j k ≤ lamV j * (M j)² * neumannRadialCoeff k.
  have hf_le : ∀ j k,
      f j k ≤ lamV j * (M j) ^ 2 * neumannRadialCoeff β hβ k := by
    intro j k
    have h2 : (modeProj Φ j k P) ^ 2 ≤ (M j) ^ 2 := hModeProjSq j k
    have hCommon : 0 ≤ lamV j * neumannRadialCoeff β hβ k :=
      mul_nonneg (hLamNonneg j) (hRadNonneg k)
    have hStep :
        lamV j * neumannRadialCoeff β hβ k * (modeProj Φ j k P) ^ 2
          ≤ lamV j * neumannRadialCoeff β hβ k * (M j) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hCommon
    have hReorder :
        lamV j * neumannRadialCoeff β hβ k * (M j) ^ 2
          = lamV j * (M j) ^ 2 * neumannRadialCoeff β hβ k := by ring
    exact hStep.trans_eq hReorder
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  have hInnerSumm : ∀ j, Summable (fun k => f j k) := by
    intro j
    have hMajorSumm :
        Summable (fun k => lamV j * (M j) ^ 2 * neumannRadialCoeff β hβ k) :=
      hRadSumm.mul_left (lamV j * (M j) ^ 2)
    exact Summable.of_nonneg_of_le (fun k => hf_nonneg j k) (hf_le j) hMajorSumm
  have hInnerLe : ∀ j,
      ∑ k ∈ Finset.range (K + 1), f j k ≤ ∑' k, f j k := by
    intro j
    exact (hInnerSumm j).sum_le_tsum (Finset.range (K + 1))
      (fun k _ => hf_nonneg j k)
  have hOuterPerJ : ∀ j,
      (∑' k, f j k) ≤ lamV j * (M j) ^ 2 * (∑' k, neumannRadialCoeff β hβ k) := by
    intro j
    have hRHS_summable :
        Summable (fun k => lamV j * (M j) ^ 2 * neumannRadialCoeff β hβ k) :=
      hRadSumm.mul_left _
    have h := Summable.tsum_le_tsum (hf_le j) (hInnerSumm j) hRHS_summable
    have hpull :
        (∑' k, lamV j * (M j) ^ 2 * neumannRadialCoeff β hβ k) =
          lamV j * (M j) ^ 2 * ∑' k, neumannRadialCoeff β hβ k :=
      tsum_mul_left
    exact h.trans_eq hpull
  -- Bridge axiom outer summability is in `‖λv j‖` form; rewrite to `λv j`
  -- using nonnegativity.
  have hAngMajor_no_norm :
      Summable (fun j => lamV j * (M j) ^ 2) := by
    have hcongr : ∀ j, ‖lamV j‖ * (M j) ^ 2 = lamV j * (M j) ^ 2 := by
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
    refine hAngMajor.congr ?_
    intro j
    exact hcongr j
  have hOuterMaj :
      Summable (fun j =>
        lamV j * (M j) ^ 2 * (∑' k, neumannRadialCoeff β hβ k)) :=
    hAngMajor_no_norm.mul_right _
  have hOuterSumm : Summable (fun j => ∑' k, f j k) := by
    refine Summable.of_nonneg_of_le ?_ hOuterPerJ hOuterMaj
    intro j
    exact tsum_nonneg (fun k => hf_nonneg j k)
  have hOuterLe :
      ∑ j ∈ Finset.range (L + 1), (∑' k, f j k) ≤ ∑' j, ∑' k, f j k :=
    hOuterSumm.sum_le_tsum (Finset.range (L + 1))
      (fun j _ => tsum_nonneg (fun k => hf_nonneg j k))
  show ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k
        ≤ ∑' j : ℕ, ∑' k : ℕ, f j k
  calc
    ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k
        ≤ ∑ j ∈ Finset.range (L + 1), ∑' k, f j k :=
          Finset.sum_le_sum (fun j _ => hInnerLe j)
    _ ≤ ∑' j : ℕ, ∑' k : ℕ, f j k := hOuterLe

/-! ### Phase 3: joint truncation error bound -/

set_option maxHeartbeats 400000 in
/-- Joint-(L, K) truncation error bound, qualitative form (no closed-form
decay rates).

The error decomposes naturally into an **angular tail** (modes `j > L`, all `k`)
plus a **radial tail at the kept angular range** (modes `j ≤ L`, `k > K`).

Both pieces use the bridge axiom's `k`-uniform `L¹` majorant `M`.  The
qualitative bound holds for any choice of `(L, K)`; combined with
`spectralEnergyTruncated_tendsto_full` (Phase 4), this certifies the
truncated energy converges to the full spectral energy as `(L, K) → ∞`.

No new axioms needed beyond the existing `kernelAngChordal_mercerExpansion`,
`summable_neumannCosineCoeff_imported`, and
`spectral_modeL1_factorized_bridge_imported`. -/
theorem spectralEnergyTruncated_error_le
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    |spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ) P
      - spectralEnergyTruncated
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P|
      ≤
        angularTailMass β α hDim hβ hα P L * radialTotalMass β hβ
      + angularPrefixMass β α hDim hβ hα P L * radialTailMass β hβ K := by
  -- Open bridge axiom via .choose / .choose_spec so M is definitionally
  -- equal to the witness used in the mass definitions.
  set bridge := spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  let M : ℕ → ℝ := bridge.choose
  have hSpec := bridge.choose_spec
  obtain ⟨hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ := hSpec
  let Φ := mercerEigenfun d β α hDim hβ hα
  let lamV := mercerEigenval d β α hDim hβ hα
  let f : ℕ → ℕ → ℝ := fun j k =>
    lamV j * neumannRadialCoeff β hβ k * (modeProj Φ j k P) ^ 2
  let majAng : ℕ → ℝ := fun j => ‖lamV j‖ * (M j) ^ 2
  have hf_nonneg : ∀ j k, 0 ≤ f j k := fun j k =>
    spectralEnergy_term_nonneg β α hDim hβ hα P j k
  have hLamNonneg : ∀ j, 0 ≤ lamV j := mercerEigenval_nonneg d β α hDim hβ hα
  have hRadNonneg : ∀ k, 0 ≤ neumannRadialCoeff β hβ k :=
    neumannRadialCoeff_nonneg β hβ
  have hLamNorm : ∀ j, ‖lamV j‖ = lamV j := fun j => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
  -- Jensen on bridge L¹ bound: |modeProj j k P| ≤ M j (k-uniform).
  have hModeProjAbs : ∀ j k, |modeProj Φ j k P| ≤ M j := by
    intro j k
    have h₁ :
        ‖∫ w, Φ j w.1 * radialFeature k w.2 ∂(P : Measure (Wristband d))‖ ≤
          ∫ w, ‖Φ j w.1 * radialFeature k w.2‖ ∂(P : Measure (Wristband d)) :=
      norm_integral_le_integral_norm _
    have h₂ := h₁.trans (hModeL1Bound j k)
    simpa [modeProj, Real.norm_eq_abs] using h₂
  have hModeProjSq : ∀ j k, (modeProj Φ j k P) ^ 2 ≤ (M j) ^ 2 := by
    intro j k
    have habs_sq : |modeProj Φ j k P| ^ 2 ≤ (M j) ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg _) (hModeProjAbs j k)
      simpa [pow_two] using this
    simpa [sq_abs] using habs_sq
  -- Pointwise majorant: f j k ≤ majAng j * neumannRadialCoeff k.
  have hf_le : ∀ j k, f j k ≤ majAng j * neumannRadialCoeff β hβ k := by
    intro j k
    have h2 : (modeProj Φ j k P) ^ 2 ≤ (M j) ^ 2 := hModeProjSq j k
    have hCommon : 0 ≤ lamV j * neumannRadialCoeff β hβ k :=
      mul_nonneg (hLamNonneg j) (hRadNonneg k)
    have hStep :
        lamV j * neumannRadialCoeff β hβ k * (modeProj Φ j k P) ^ 2
          ≤ lamV j * neumannRadialCoeff β hβ k * (M j) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hCommon
    have hReorder :
        lamV j * neumannRadialCoeff β hβ k * (M j) ^ 2
          = majAng j * neumannRadialCoeff β hβ k := by
      show _ = ‖lamV j‖ * (M j) ^ 2 * _
      rw [hLamNorm]; ring
    exact hStep.trans_eq hReorder
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  have hRadShiftSumm : ∀ N, Summable (fun n => neumannRadialCoeff β hβ (n + N)) :=
    fun N => (summable_nat_add_iff N).2 hRadSumm
  have hInnerSumm : ∀ j, Summable (fun k => f j k) := by
    intro j
    have hMajorSumm :
        Summable (fun k => majAng j * neumannRadialCoeff β hβ k) :=
      hRadSumm.mul_left _
    exact Summable.of_nonneg_of_le (fun k => hf_nonneg j k) (hf_le j) hMajorSumm
  have hInnerShiftSumm : ∀ j N, Summable (fun n => f j (n + N)) :=
    fun j N => (summable_nat_add_iff N).2 (hInnerSumm j)
  -- Per-j inner full bound: ∑' k, f j k ≤ majAng j * radialTotalMass.
  have hInnerTotal : ∀ j,
      (∑' k, f j k) ≤ majAng j * radialTotalMass β hβ := by
    intro j
    have hRHS : Summable (fun k => majAng j * neumannRadialCoeff β hβ k) :=
      hRadSumm.mul_left _
    have h := Summable.tsum_le_tsum (hf_le j) (hInnerSumm j) hRHS
    have hpull :
        (∑' k, majAng j * neumannRadialCoeff β hβ k) =
          majAng j * ∑' k, neumannRadialCoeff β hβ k :=
      tsum_mul_left
    show _ ≤ majAng j * (∑' k, neumannRadialCoeff β hβ k)
    exact h.trans_eq hpull
  -- Per-j inner-tail bound: ∑' n, f j (n+K+1) ≤ majAng j * radialTailMass K.
  have hInnerTail : ∀ j,
      (∑' n, f j (n + (K + 1))) ≤ majAng j * radialTailMass β hβ K := by
    intro j
    have hShiftLe : ∀ n,
        f j (n + (K + 1)) ≤ majAng j * neumannRadialCoeff β hβ (n + (K + 1)) :=
      fun n => hf_le j (n + (K + 1))
    have hRHSShiftSumm :
        Summable (fun n => majAng j * neumannRadialCoeff β hβ (n + (K + 1))) :=
      (hRadShiftSumm (K + 1)).mul_left _
    have h :=
      Summable.tsum_le_tsum hShiftLe (hInnerShiftSumm j (K + 1)) hRHSShiftSumm
    have hpull :
        (∑' n, majAng j * neumannRadialCoeff β hβ (n + (K + 1))) =
          majAng j * ∑' n, neumannRadialCoeff β hβ (n + (K + 1)) :=
      tsum_mul_left
    show _ ≤ majAng j * (∑' n, neumannRadialCoeff β hβ (n + (K + 1)))
    exact h.trans_eq hpull
  -- Outer summability and shifted version.
  have hMajAngSumm : Summable majAng := hAngMajor
  have hMajAngShiftSumm : Summable (fun i => majAng (i + (L + 1))) :=
    (summable_nat_add_iff (L + 1)).2 hMajAngSumm
  have hOuterMaj :
      Summable (fun j => majAng j * radialTotalMass β hβ) :=
    hMajAngSumm.mul_right _
  have hOuterSumm : Summable (fun j => ∑' k, f j k) := by
    refine Summable.of_nonneg_of_le ?_ hInnerTotal hOuterMaj
    intro j
    exact tsum_nonneg (fun k => hf_nonneg j k)
  have hOuterShiftSumm :
      Summable (fun i => ∑' k, f (i + (L + 1)) k) :=
    (summable_nat_add_iff (L + 1)).2 hOuterSumm
  -- Decomposition identities (outer + inner via sum_add_tsum_nat_add).
  have hOuterDecomp :
      (∑' j, ∑' k, f j k) =
        (∑ j ∈ Finset.range (L + 1), ∑' k, f j k) +
        (∑' i, ∑' k, f (i + (L + 1)) k) :=
    (hOuterSumm.sum_add_tsum_nat_add (L + 1)).symm
  have hInnerDecomp : ∀ j,
      (∑' k, f j k) =
        (∑ k ∈ Finset.range (K + 1), f j k) +
        (∑' n, f j (n + (K + 1))) :=
    fun j => ((hInnerSumm j).sum_add_tsum_nat_add (K + 1)).symm
  -- Combined: spectralEnergy = spectralEnergyTruncated + radialTail + angularTail.
  have hCombined :
      (∑' j, ∑' k, f j k) =
        (∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k)
        + (∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1)))
        + (∑' i, ∑' k, f (i + (L + 1)) k) := by
    rw [hOuterDecomp]
    have hSumDecomp :
        ∑ j ∈ Finset.range (L + 1), ∑' k, f j k =
        ∑ j ∈ Finset.range (L + 1),
          ((∑ k ∈ Finset.range (K + 1), f j k) + ∑' n, f j (n + (K + 1))) :=
      Finset.sum_congr rfl (fun j _ => hInnerDecomp j)
    rw [hSumDecomp, Finset.sum_add_distrib]
  have hDiffEq :
      (∑' j, ∑' k, f j k)
        - (∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k)
        = (∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1)))
          + (∑' i, ∑' k, f (i + (L + 1)) k) := by
    linarith [hCombined]
  have hPiece1Nonneg :
      0 ≤ ∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1)) := by
    apply Finset.sum_nonneg
    intro j _
    exact tsum_nonneg (fun n => hf_nonneg j (n + (K + 1)))
  have hPiece2Nonneg :
      0 ≤ ∑' i, ∑' k, f (i + (L + 1)) k := by
    apply tsum_nonneg
    intro i
    exact tsum_nonneg (fun k => hf_nonneg (i + (L + 1)) k)
  have hDiffNonneg :
      0 ≤ (∑' j, ∑' k, f j k)
            - (∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k) := by
    rw [hDiffEq]
    linarith [hPiece1Nonneg, hPiece2Nonneg]
  have hAbsEq :
      |(∑' j, ∑' k, f j k)
          - (∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k)|
        = (∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1)))
          + (∑' i, ∑' k, f (i + (L + 1)) k) := by
    rw [abs_of_nonneg hDiffNonneg, hDiffEq]
  -- Bound the radial-tail-at-L piece.
  have hRadialTailAtLBound :
      (∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1)))
        ≤ angularPrefixMass β α hDim hβ hα P L * radialTailMass β hβ K := by
    have hStep :
        ∑ j ∈ Finset.range (L + 1), ∑' n, f j (n + (K + 1))
          ≤ ∑ j ∈ Finset.range (L + 1), majAng j * radialTailMass β hβ K :=
      Finset.sum_le_sum (fun j _ => hInnerTail j)
    have hFactor :
        ∑ j ∈ Finset.range (L + 1), majAng j * radialTailMass β hβ K
          = (∑ j ∈ Finset.range (L + 1), majAng j) * radialTailMass β hβ K := by
      rw [← Finset.sum_mul]
    have hPrefix :
        (∑ j ∈ Finset.range (L + 1), majAng j)
          = angularPrefixMass β α hDim hβ hα P L := rfl
    show _ ≤ angularPrefixMass β α hDim hβ hα P L * radialTailMass β hβ K
    rw [← hPrefix, ← hFactor]
    exact hStep
  -- Bound the angular-tail piece.
  have hAngularTailBound :
      (∑' i, ∑' k, f (i + (L + 1)) k)
        ≤ angularTailMass β α hDim hβ hα P L * radialTotalMass β hβ := by
    have hShiftedInnerTotal : ∀ i,
        (∑' k, f (i + (L + 1)) k) ≤ majAng (i + (L + 1)) * radialTotalMass β hβ :=
      fun i => hInnerTotal (i + (L + 1))
    have hRHSshiftSumm :
        Summable (fun i => majAng (i + (L + 1)) * radialTotalMass β hβ) :=
      hMajAngShiftSumm.mul_right _
    have h :=
      Summable.tsum_le_tsum hShiftedInnerTotal hOuterShiftSumm hRHSshiftSumm
    have hpull :
        (∑' i, majAng (i + (L + 1)) * radialTotalMass β hβ) =
          (∑' i, majAng (i + (L + 1))) * radialTotalMass β hβ :=
      tsum_mul_right
    show _ ≤ angularTailMass β α hDim hβ hα P L * radialTotalMass β hβ
    have hTail :
        (∑' i, majAng (i + (L + 1))) = angularTailMass β α hDim hβ hα P L := rfl
    rw [← hTail]
    exact h.trans_eq hpull
  -- Combine.
  show |(∑' j, ∑' k, f j k)
        - (∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), f j k)|
       ≤ angularTailMass β α hDim hβ hα P L * radialTotalMass β hβ
       + angularPrefixMass β α hDim hβ hα P L * radialTailMass β hβ K
  rw [hAbsEq]
  linarith [hRadialTailAtLBound, hAngularTailBound]

/-! ### Phase 3: kernel-side corollaries -/

/-- Joint-truncated spectral energy is bounded by the underlying kernel
energy.  Direct corollary of `spectralEnergyTruncated_le_spectralEnergy` plus
`spectralEnergy_eq_kernelEnergy`. -/
theorem spectralEnergyTruncated_le_kernelEnergy
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    spectralEnergyTruncated
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P
      ≤ kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  have h₁ := spectralEnergyTruncated_le_spectralEnergy β α hDim hβ hα P L K
  have h₂ := spectralEnergy_eq_kernelEnergy (d := d) β α hDim hβ hα P
  linarith [h₁, h₂]

/-- Kernel-energy form of the joint truncation error bound.  The kernel-energy
formulation is what the kernel branch uses; this corollary lets downstream
results phrase the truncation error in terms of `kernelEnergy
(wristbandKernelNeumann β α)`. -/
theorem kernelEnergy_truncation_error_le
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    |kernelEnergy (wristbandKernelNeumann (d := d) β α) P
      - spectralEnergyTruncated
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P|
      ≤
        angularTailMass β α hDim hβ hα P L * radialTotalMass β hβ
      + angularPrefixMass β α hDim hβ hα P L * radialTailMass β hβ K := by
  have hEq := spectralEnergy_eq_kernelEnergy (d := d) β α hDim hβ hα P
  rw [← hEq]
  exact spectralEnergyTruncated_error_le β α hDim hβ hα P L K

/-- Combined containment: `0 ≤ E_{L,K}(P) ≤ spectralEnergy P`. -/
theorem spectralEnergyTruncated_mem_Icc
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    0 ≤
        spectralEnergyTruncated
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          L K P
      ∧
      spectralEnergyTruncated
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          L K P
        ≤
      spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          P :=
  ⟨spectralEnergyTruncated_nonneg β α hDim hβ hα P L K,
   spectralEnergyTruncated_le_spectralEnergy β α hDim hβ hα P L K⟩

end WristbandLossProofs
