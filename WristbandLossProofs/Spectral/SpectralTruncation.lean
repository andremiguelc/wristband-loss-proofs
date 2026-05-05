import WristbandLossProofs.Spectral.SpectralFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory Filter
open scoped BigOperators Topology

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

/-! ### Phase 4: degree-indexed truncation (user-facing closed-form API)

The flat-indexed `spectralEnergyTruncated` above is a stepping stone:
the qualitative bound is stated against it, but the user-facing closed-form
bound (`Step 5`) targets `spectralEnergyTruncatedByDegree` from
`SpectralPrimitives`, where the angular cutoff `L` means "highest angular
degree kept" (not "highest flat eigenmode index"). -/

/-- The degree-indexed truncated spectral energy is non-negative. -/
theorem spectralEnergyTruncatedByDegree_nonneg
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    0 ≤
      spectralEnergyTruncatedByDegree
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (mercerDegAt d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P := by
  unfold spectralEnergyTruncatedByDegree
  refine tsum_nonneg ?_
  intro j
  by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
  · simp only [if_pos h]
    refine Finset.sum_nonneg ?_
    intro k _
    exact spectralEnergy_term_nonneg β α hDim hβ hα P j k
  · simp only [if_neg h]
    exact le_refl 0

/-! ### Phase 6: closed-form radial tail bound

Upgrades the opaque `radialTailMass β hβ K` (`∑' n, neumannRadialCoeff β hβ
(n + K + 1)`) to an explicit, closed-form upper bound in `(β, K)` using
axiom `neumannCosineCoeff_le_gaussianBound` from `SpectralImportedFacts`.

The shape is the *simple geometric* majorant of `Σ_{m=K+1}^∞ ã_m` with
`ã_m = 2√(π/β)·exp(−π²m²/(4β))`:
`(n+K+1)² ≥ (K+1)² + (K+1)·n` ⟹ Gaussian-times-geometric tail
⟹ `radialTailMass β hβ K ≤ 2√(π/β)·exp(−a(K+1)²)/(1 − exp(−a(K+1)))`
with `a = π²/(4β)`. -/

/-- Closed-form upper bound for the radial tail mass.

Simple geometric majorant: with `a = π²/(4β)`,
`radialTailMass_closedForm β K = 2√(π/β) · exp(−a(K+1)²) / (1 − exp(−a(K+1)))`. -/
noncomputable def radialTailMass_closedForm (β : ℝ) (K : ℕ) : ℝ :=
  2 * Real.sqrt (Real.pi / β) *
    Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) ^ 2 / (4 * β)) /
      (1 - Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) / (4 * β)))

/-- The radial tail mass is bounded by the closed form.

Proof outline (`a := π²/(4β)`, `r := exp(−a(K+1))`, `C := 2√(π/β)·exp(−a(K+1)²)`):
1. `radialTailMass β hβ K = ∑' n, neumannCosineCoeff β hβ (n + K)` (def. unfolding).
2. Pointwise: axiom (R) gives `neumannCosineCoeff β hβ (n + K) ≤
   2√(π/β)·exp(−π²(n+K+1)²/(4β))`.
3. Square inequality: `(n+(K+1))² ≥ (K+1)² + (K+1)·n` (since the
   missing term `n² + (K+1)n` is nonneg).
4. exp monotonicity + factoring: `exp(−a(n+(K+1))²) ≤ exp(−a(K+1)²) · r^n`.
5. Sum: `∑' n, C · r^n = C / (1 − r)` via `tsum_geometric_of_lt_one`. -/
theorem radialTailMass_le_closedForm (β : ℝ) (hβ : 0 < β) (K : ℕ) :
    radialTailMass β hβ K ≤ radialTailMass_closedForm β K := by
  -- Constants
  set a : ℝ := Real.pi ^ 2 / (4 * β) with ha_def
  have ha_pos : 0 < a := by
    refine div_pos ?_ (by linarith)
    positivity
  have hKp1_pos : (0 : ℝ) < (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    linarith
  set r : ℝ := Real.exp (-(a * ((K : ℝ) + 1))) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    refine Real.exp_lt_one_iff.mpr ?_
    have := mul_pos ha_pos hKp1_pos
    linarith
  set C : ℝ := 2 * Real.sqrt (Real.pi / β) * Real.exp (-(a * ((K : ℝ) + 1) ^ 2))
    with hC_def
  have hSqrt_nonneg : 0 ≤ Real.sqrt (Real.pi / β) := Real.sqrt_nonneg _
  -- Pointwise bound on each tail term
  have hPointBound : ∀ n : ℕ,
      neumannCosineCoeff β hβ (n + K) ≤ C * r ^ n := by
    intro n
    have hAx := neumannCosineCoeff_le_gaussianBound β hβ (n + K)
    -- Reindex the cast
    have hCastK : ((n + K : ℕ) : ℝ) + 1 = (n : ℝ) + ((K : ℝ) + 1) := by push_cast; ring
    rw [hCastK] at hAx
    -- Rewrite the exponent argument as -(a * (...))
    have hAxExp_form : -(Real.pi ^ 2) * ((n : ℝ) + ((K : ℝ) + 1)) ^ 2 / (4 * β) =
        -(a * ((n : ℝ) + ((K : ℝ) + 1)) ^ 2) := by
      rw [ha_def]; field_simp
    rw [hAxExp_form] at hAx
    -- Square inequality: (K+1)² + (K+1)·n ≤ (n + (K+1))²
    have hSq : ((K : ℝ) + 1) ^ 2 + ((K : ℝ) + 1) * (n : ℝ) ≤
        ((n : ℝ) + ((K : ℝ) + 1)) ^ 2 := by
      have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := hKp1_pos.le
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg ((n : ℝ)), mul_nonneg hK hn]
    -- exp monotonicity gives exp(−a · big) ≤ exp(−a · small)
    have hExpMono : Real.exp (-(a * ((n : ℝ) + ((K : ℝ) + 1)) ^ 2)) ≤
        Real.exp (-(a * (((K : ℝ) + 1) ^ 2 + ((K : ℝ) + 1) * (n : ℝ)))) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hSq ha_pos.le
      linarith
    -- exp split: exp(−a(α + β·n)) = exp(−a·α) · r^n
    have hExpSplit : Real.exp (-(a * (((K : ℝ) + 1) ^ 2 + ((K : ℝ) + 1) * (n : ℝ)))) =
        Real.exp (-(a * ((K : ℝ) + 1) ^ 2)) * r ^ n := by
      rw [hr_def,
          show -(a * (((K : ℝ) + 1) ^ 2 + ((K : ℝ) + 1) * (n : ℝ))) =
              -(a * ((K : ℝ) + 1) ^ 2) + (n : ℝ) * (-(a * ((K : ℝ) + 1))) by ring,
          Real.exp_add, Real.exp_nat_mul]
    -- Combine: chain hAx → hExpMono → hExpSplit and re-associate to C * r^n
    have hChain :
        neumannCosineCoeff β hβ (n + K) ≤
          2 * Real.sqrt (Real.pi / β) *
            (Real.exp (-(a * ((K : ℝ) + 1) ^ 2)) * r ^ n) := by
      calc neumannCosineCoeff β hβ (n + K)
          ≤ 2 * Real.sqrt (Real.pi / β) *
              Real.exp (-(a * ((n : ℝ) + ((K : ℝ) + 1)) ^ 2)) := hAx
        _ ≤ 2 * Real.sqrt (Real.pi / β) *
              Real.exp (-(a * (((K : ℝ) + 1) ^ 2 + ((K : ℝ) + 1) * (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left hExpMono ?_
            exact mul_nonneg (by norm_num) hSqrt_nonneg
        _ = 2 * Real.sqrt (Real.pi / β) *
              (Real.exp (-(a * ((K : ℝ) + 1) ^ 2)) * r ^ n) := by rw [hExpSplit]
    have hReassoc :
        2 * Real.sqrt (Real.pi / β) *
            (Real.exp (-(a * ((K : ℝ) + 1) ^ 2)) * r ^ n) = C * r ^ n := by
      rw [hC_def]; ring
    exact hReassoc ▸ hChain
  -- Summability of the geometric majorant and the cosine tail
  have hSummableGeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr_pos.le hr_lt_one
  have hMajSumm : Summable (fun n : ℕ => C * r ^ n) := hSummableGeom.mul_left C
  have hOrigSumm : Summable (fun n : ℕ => neumannCosineCoeff β hβ (n + K)) :=
    (summable_nat_add_iff K).mpr (summable_neumannCosineCoeff_imported β hβ)
  -- Rewrite radialTailMass via neumannCosineCoeff
  have hRewrite :
      radialTailMass β hβ K = ∑' n : ℕ, neumannCosineCoeff β hβ (n + K) := by
    unfold radialTailMass
    refine tsum_congr ?_
    intro n
    show neumannRadialCoeff β hβ (n + (K + 1)) = neumannCosineCoeff β hβ (n + K)
    rfl
  -- Bundle the pointwise bound into a tsum bound
  have hStep1 :
      ∑' n : ℕ, neumannCosineCoeff β hβ (n + K) ≤ ∑' n : ℕ, C * r ^ n :=
    hOrigSumm.tsum_le_tsum hPointBound hMajSumm
  -- Compute the geometric tsum
  have hGeom : ∑' n : ℕ, C * r ^ n = C / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt_one, div_eq_mul_inv]
  -- Show C / (1 − r) = radialTailMass_closedForm β K
  have hUnfold : C / (1 - r) = radialTailMass_closedForm β K := by
    have hπ2β_sq : -(a * ((K : ℝ) + 1) ^ 2) =
        -(Real.pi ^ 2) * ((K : ℝ) + 1) ^ 2 / (4 * β) := by
      rw [ha_def]; field_simp
    have hπ2β_lin : -(a * ((K : ℝ) + 1)) =
        -(Real.pi ^ 2) * ((K : ℝ) + 1) / (4 * β) := by
      rw [ha_def]; field_simp
    unfold radialTailMass_closedForm
    rw [hC_def, hr_def, hπ2β_sq, hπ2β_lin]
  -- Combine
  rw [hRewrite]
  calc ∑' n : ℕ, neumannCosineCoeff β hβ (n + K)
      ≤ ∑' n : ℕ, C * r ^ n := hStep1
    _ = C / (1 - r) := hGeom
    _ = radialTailMass_closedForm β K := hUnfold

/-- The closed-form radial tail bound goes to zero as `K → ∞`.

Combines:
- numerator `2√(π/β) · exp(−π²(K+1)²/(4β)) → 0` (super-exp Gaussian decay),
- denominator `1 − exp(−π²(K+1)/(4β)) → 1` (exp(...) → 0 in the linear case),
via `Tendsto.div`. -/
theorem tendsto_radialTailMass_closedForm (β : ℝ) (hβ : 0 < β) :
    Tendsto (radialTailMass_closedForm β) atTop (𝓝 0) := by
  -- Helper: (K : ℝ) + 1 → atTop
  have hKpO : Tendsto (fun K : ℕ => ((K : ℝ) + 1)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro K; exact le_of_lt (lt_add_one _)
  -- (K+1)² → atTop (squeeze: (K+1)² ≥ K+1 when K+1 ≥ 1)
  have hSq : Tendsto (fun K : ℕ => ((K : ℝ) + 1) ^ 2) atTop atTop := by
    apply tendsto_atTop_mono _ hKpO
    intro K
    have h1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
      linarith
    nlinarith
  -- Positivity of π²/(4β)
  have ha : (0 : ℝ) < Real.pi ^ 2 / (4 * β) := div_pos (by positivity) (by linarith)
  -- exp(−π²(K+1)²/(4β)) → 0
  have hExpSq : Tendsto (fun K : ℕ =>
      Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) ^ 2 / (4 * β))) atTop (𝓝 0) := by
    have hMul : Tendsto (fun K : ℕ =>
        (Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1) ^ 2) atTop atTop :=
      Filter.Tendsto.const_mul_atTop ha hSq
    have hNeg : Tendsto (fun K : ℕ =>
        -((Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1) ^ 2)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hMul
    have hExp := Real.tendsto_exp_atBot.comp hNeg
    have hForm : ∀ K : ℕ,
        -(Real.pi ^ 2) * ((K : ℝ) + 1) ^ 2 / (4 * β) =
          -((Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1) ^ 2) := by
      intro K; field_simp
    simp_rw [hForm]
    exact hExp
  -- exp(−π²(K+1)/(4β)) → 0
  have hExpLin : Tendsto (fun K : ℕ =>
      Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) / (4 * β))) atTop (𝓝 0) := by
    have hMul : Tendsto (fun K : ℕ =>
        (Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop ha hKpO
    have hNeg : Tendsto (fun K : ℕ =>
        -((Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1))) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hMul
    have hExp := Real.tendsto_exp_atBot.comp hNeg
    have hForm : ∀ K : ℕ,
        -(Real.pi ^ 2) * ((K : ℝ) + 1) / (4 * β) =
          -((Real.pi ^ 2 / (4 * β)) * ((K : ℝ) + 1)) := by
      intro K; field_simp
    simp_rw [hForm]
    exact hExp
  -- Numerator: 2√(π/β) · exp(...) → 0
  have hNumer : Tendsto (fun K : ℕ =>
      2 * Real.sqrt (Real.pi / β) *
        Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) ^ 2 / (4 * β))) atTop (𝓝 0) := by
    have h := hExpSq.const_mul (2 * Real.sqrt (Real.pi / β))
    rwa [mul_zero] at h
  -- Denominator: 1 − exp(...) → 1
  have hDenom : Tendsto (fun K : ℕ =>
      1 - Real.exp (-(Real.pi ^ 2) * ((K : ℝ) + 1) / (4 * β))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hExpLin
    rwa [sub_zero] at h
  -- Quotient → 0/1 = 0; the 0/1 simplification + def-unfold finishes the goal
  have hDiv := hNumer.div hDenom one_ne_zero
  rw [zero_div] at hDiv
  exact hDiv

/-! ### Phase 7: closed-form angular tail bound

Upgrades the bridge-axiom-based `angularTailMass(P, L)` to a P-uniform
closed-form bound via the Mercer per-degree weights `λ_ℓ · N(d, ℓ)`.

Key ingredients:
- `mercerDegreeMass ℓ = Σ_{j : degAt j = ℓ} λv j` (= `λ_ℓ · N(d, ℓ)`).
- Diagonal-Mercer constraint: `Σ_ℓ mercerDegreeMass ℓ = 1` (axiom).
- Addition theorem: `Σ_{j : degAt j = ℓ} φ_j(u)² = N(d, ℓ)` (axiom).
- λv constancy on `degAt`-fibres (clause of augmented Mercer axiom).

The closed-form bound is `Σ_{n} mercerDegreeMass (n + L + 1)`
= `Σ_{ℓ > L} λ_ℓ · N(d, ℓ)`, equivalent to `1 − Σ_{ℓ ≤ L} λ_ℓ · N(d, ℓ)`
via diagonal-Mercer. -/

/-- Per-degree mass: sum of `λv j` over the `mercerDegAt`-fibre of degree `ℓ`.

Mathematically equals `λ_ℓ · N(d, ℓ)`, where `λ_ℓ` is the common eigenvalue
shared by all degree-`ℓ` eigenmodes (`mercerEigenval_const_on_degree_fiber`)
and `N(d, ℓ) = sphericalHarmonicDim d ℓ` is the multiplicity. -/
noncomputable def mercerDegreeMass
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (ℓ : ℕ) : ℝ :=
  ∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ
    then mercerEigenval d β α hDim hβ hα j else 0

/-- Closed-form angular tail mass: `Σ_{ℓ > L} λ_ℓ · N(d, ℓ)`, expressed via
the nat-shift form `Σ' n, mercerDegreeMass (n + L + 1)`.

P-uniform — does not depend on `P`. Equals `1 − angularPrefixMass_closedForm L`
by the diagonal-Mercer axiom. -/
noncomputable def angularTailMass_closedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (L : ℕ) : ℝ :=
  ∑' n : ℕ, mercerDegreeMass d β α hDim hβ hα (n + (L + 1))

/-- Closed-form angular prefix mass: `Σ_{ℓ ≤ L} λ_ℓ · N(d, ℓ)`. Finite sum. -/
noncomputable def angularPrefixMass_closedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (L : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range (L + 1), mercerDegreeMass d β α hDim hβ hα ℓ

/-- Each per-degree mass is non-negative (since `λv j ≥ 0`). -/
lemma mercerDegreeMass_nonneg
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (ℓ : ℕ) :
    0 ≤ mercerDegreeMass d β α hDim hβ hα ℓ := by
  unfold mercerDegreeMass
  refine tsum_nonneg ?_
  intro j
  split_ifs with h
  · exact mercerEigenval_nonneg d β α hDim hβ hα j
  · exact le_refl 0

/-- The per-degree masses are summable (their tsum equals 1). -/
lemma mercerDegreeMass_summable
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    Summable (mercerDegreeMass d β α hDim hβ hα) := by
  by_contra h
  have htsum : (∑' ℓ : ℕ, mercerDegreeMass d β α hDim hβ hα ℓ) = 0 :=
    tsum_eq_zero_of_not_summable h
  have hone := mercerDegreeMass_total_eq_one d β α hDim hβ hα
  -- Axiom unfolds to ∑' ℓ, mercerDegreeMass ℓ = 1 by `rfl` on the def.
  have heq : (∑' ℓ : ℕ,
        ∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
            mercerEigenval d β α hDim hβ hα j else 0) =
      (∑' ℓ : ℕ, mercerDegreeMass d β α hDim hβ hα ℓ) := rfl
  rw [heq, htsum] at hone
  exact zero_ne_one hone

/-- The diagonal-Mercer total in terms of `mercerDegreeMass`. -/
lemma tsum_mercerDegreeMass_eq_one
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    (∑' ℓ : ℕ, mercerDegreeMass d β α hDim hβ hα ℓ) = 1 :=
  mercerDegreeMass_total_eq_one d β α hDim hβ hα

/-- `prefix + tail = 1`: closed-form complement identity, via the diagonal
Mercer axiom + the standard `Σ + tail = total` decomposition. -/
lemma angularPrefixMass_add_tailMass_closedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (L : ℕ) :
    angularPrefixMass_closedForm d β α hDim hβ hα L
      + angularTailMass_closedForm d β α hDim hβ hα L = 1 := by
  have hSumm := mercerDegreeMass_summable d β α hDim hβ hα
  have hTotal := tsum_mercerDegreeMass_eq_one d β α hDim hβ hα
  -- Σ_{ℓ < L+1} f ℓ + Σ' n, f(n + L + 1) = Σ' ℓ, f ℓ = 1
  have hSumAdd := Summable.sum_add_tsum_nat_add (L + 1) hSumm
  unfold angularPrefixMass_closedForm angularTailMass_closedForm
  rw [hSumAdd, hTotal]

/-- Closed-form tail tends to zero as `L → ∞`. Direct from
`tendsto_sum_nat_add` (the partial-tail tsum tends to 0 as the shift grows). -/
theorem tendsto_angularTailMass_closedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    Tendsto (angularTailMass_closedForm d β α hDim hβ hα) atTop (𝓝 0) := by
  -- `tendsto_sum_nat_add f : Tendsto (fun i ↦ ∑' k, f (k + i)) atTop (𝓝 0)`
  -- (no summability needed; if not summable, all such tails are 0).
  -- Compose with `i = L + 1` (which is atTop in L).
  have h := tendsto_sum_nat_add (mercerDegreeMass d β α hDim hβ hα)
  -- h : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)
  have hShift : Tendsto (fun L : ℕ => L + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun _ => Nat.le_succ _) ?_
    exact tendsto_id
  exact h.comp hShift

end WristbandLossProofs
