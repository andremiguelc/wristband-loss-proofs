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

### Containment

  - `spectralEnergyTruncated_nonneg`            : `0 ≤ E_{L,K}(P)`
  - `spectralEnergyTruncated_le_spectralEnergy` : `E_{L,K}(P) ≤ spectralEnergy P`

### Error bound

The error `|spectralEnergy − spectralEnergyTruncated L K|` decomposes as
`angularTailMass · radialTotalMass + angularPrefixMass · radialTailMass`,
where the four mass quantities are defined below.
-/

/-! ### Mass definitions (flat-indexed, bridge-axiom witness) -/

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

/-! ### Qualitative joint truncation error bound (bridge-axiom witness) -/

set_option maxHeartbeats 400000 in
/-- Joint-(L, K) truncation error bound, qualitative form (no closed-form
decay rates).

The error decomposes naturally into an **angular tail** (modes `j > L`, all `k`)
plus a **radial tail at the kept angular range** (modes `j ≤ L`, `k > K`).

Both pieces use the bridge axiom's `k`-uniform `L¹` majorant `M`.  The
qualitative bound holds for any choice of `(L, K)` and certifies that
the truncated energy converges to the full spectral energy as `(L, K) → ∞`.

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

/-! ### Kernel-side corollaries of the qualitative bound -/

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

/-! ### Degree-indexed truncation (user-facing closed-form API)

The flat-indexed `spectralEnergyTruncated` above is an internal stepping stone:
the qualitative bound is stated against it, but the closed-form
bound targets `spectralEnergyTruncatedByDegree` from `SpectralPrimitives`,
where the angular cutoff `L` means "highest angular degree kept" (not
"highest flat eigenmode index"). -/

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

/-! ### Closed-form radial tail bound

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

/-! ### Closed-form angular tail bound (P-uniform)

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

/-! ### Angular strip bounds via the per-fibre Cauchy–Schwarz axiom

Two bounds on the truncation deviation, both P-uniform:

- **Angular tail** (`Σ_{j: degAt j > L} Σ' k, term j k`):
  contribution from angular modes outside the kept degree range.
- **Radial tail at the kept angular range**
  (`Σ_{j: degAt j ≤ L} Σ' n, term j (n+K+1)`):
  contribution from radial modes beyond `K` at kept angular degrees.

Closed-form bounds:
- Angular tail ≤ `angularTailMass_closedForm L · radialTotalMass`
- Radial tail at prefix ≤ `angularPrefixMass_closedForm L · radialTailMass K`

Both bounds are derived from the per-fibre weighted Cauchy-Schwarz axiom
(`mercer_modeProjSqSum_per_degree_le_mass`) applied per radial mode `k`,
combined with bridge-axiom-derived summabilities for the Fubini-style
swaps. -/

/-- **Per-fibre weighted bound** (axiom 7 wrapper, naming via
`mercerDegreeMass`).  The λ-weighted sum of squared mode projections over
the `degAt`-fibre of degree `ℓ` is bounded by `mercerDegreeMass ℓ`. -/
lemma weightedFibreSum_le_mercerDegreeMass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ k : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        mercerEigenval d β α hDim hβ hα j *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0)
      ≤ mercerDegreeMass d β α hDim hβ hα ℓ :=
  mercer_modeProjSqSum_per_degree_le_mass d β α hDim hβ hα P ℓ k

/-- **Per-`(ℓ, k)` weighted bound**: factoring out the radial coefficient
`c_k` from the per-fibre weighted bound. -/
lemma fibreSumWeighted_le
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ k : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0)
      ≤ neumannRadialCoeff β hβ k * mercerDegreeMass d β α hDim hβ hα ℓ := by
  have hcNonneg : 0 ≤ neumannRadialCoeff β hβ k := neumannRadialCoeff_nonneg β hβ k
  have hRewrite : ∀ j,
      (if mercerDegAt d β α hDim hβ hα j = ℓ then
          mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ k *
            (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0)
        = neumannRadialCoeff β hβ k *
          (if mercerDegAt d β α hDim hβ hα j = ℓ then
              mercerEigenval d β α hDim hβ hα j *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0) := by
    intro j
    by_cases h : mercerDegAt d β α hDim hβ hα j = ℓ
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  rw [tsum_congr hRewrite, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (weightedFibreSum_le_mercerDegreeMass β α hDim hβ hα P ℓ k) hcNonneg

/-- Bridge-derived `M`-uniform bound on `(modeProj j k P)^2`, used as the
pair-summability majorant for the Fubini swap on the angular strips. -/
private lemma modeProj_sq_le_M_sq
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (M : ℕ → ℝ)
    (hModeL1Bound : ∀ j k,
        ∫ w, ‖mercerEigenfun d β α hDim hβ hα j w.1 *
          radialFeature k w.2‖ ∂(P : Measure (Wristband d)) ≤ M j)
    (j k : ℕ) :
    (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 ≤ (M j) ^ 2 := by
  have h₁ :
      ‖∫ w, mercerEigenfun d β α hDim hβ hα j w.1 * radialFeature k w.2
          ∂(P : Measure (Wristband d))‖ ≤
        ∫ w, ‖mercerEigenfun d β α hDim hβ hα j w.1 * radialFeature k w.2‖
          ∂(P : Measure (Wristband d)) :=
    norm_integral_le_integral_norm _
  have h₂ : |modeProj (mercerEigenfun d β α hDim hβ hα) j k P| ≤ M j := by
    have h₃ := h₁.trans (hModeL1Bound j k)
    simpa [modeProj, Real.norm_eq_abs] using h₃
  have habs_sq : |modeProj (mercerEigenfun d β α hDim hβ hα) j k P| ^ 2 ≤ (M j) ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg _) h₂
    simpa [pow_two] using this
  simpa [sq_abs] using habs_sq

-- The closed-form per-degree bounds need a `maxHeartbeats` bump because the
-- bridge-axiom unpacking + Fubini-style swap + per-n bound chain elaborates
-- through several non-trivial `Summable` instances.
set_option maxHeartbeats 600000 in
/-- **Per-degree weighted-radial-sum bound** (generic shape).

For any radial reindexing `h : ℕ → ℕ` whose pulled-back coefficients are
summable, the weighted sum at angular degree `ℓ` is bounded by
`mercerDegreeMass ℓ` times the shifted radial mass `Σ' n, c (h n)`.

Specializes to the radial-tail (`h = · + (K + 1)`) and full-radial-sum
(`h = id`) bounds used in the closed-form truncation theorems. -/
lemma fibreShiftedRadialSum_le_mercerDegreeMass_mass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ : ℕ) (h : ℕ → ℕ)
    (hRadShiftSumm : Summable (fun n => neumannRadialCoeff β hβ (h n))) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        ∑' n : ℕ,
          mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ (h n) *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j (h n) P) ^ 2
        else 0)
      ≤ mercerDegreeMass d β α hDim hβ hα ℓ *
          ∑' n : ℕ, neumannRadialCoeff β hβ (h n) := by
  obtain ⟨M, _hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ :=
    spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  have hLamNonneg : ∀ j, 0 ≤ mercerEigenval d β α hDim hβ hα j :=
    mercerEigenval_nonneg d β α hDim hβ hα
  -- Indicator-weighted (j, n)-pair function.
  set F : ℕ × ℕ → ℝ := fun p =>
    if mercerDegAt d β α hDim hβ hα p.1 = ℓ then
      mercerEigenval d β α hDim hβ hα p.1 *
        neumannRadialCoeff β hβ (h p.2) *
        (modeProj (mercerEigenfun d β α hDim hβ hα) p.1 (h p.2) P) ^ 2
    else 0
  -- Pair-summable majorant: A j = lamV j * M_j², G(j, n) = A j * c_{h n}.
  set A : ℕ → ℝ := fun j => mercerEigenval d β α hDim hβ hα j * (M j) ^ 2
  set G : ℕ × ℕ → ℝ := fun p => A p.1 * neumannRadialCoeff β hβ (h p.2)
  have hA_nonneg : ∀ j, 0 ≤ A j := fun j =>
    mul_nonneg (hLamNonneg j) (sq_nonneg _)
  have hCNonneg : ∀ n, 0 ≤ neumannRadialCoeff β hβ (h n) :=
    fun n => neumannRadialCoeff_nonneg β hβ (h n)
  have hF_nonneg : ∀ p, 0 ≤ F p := by
    intro p
    by_cases hp : mercerDegAt d β α hDim hβ hα p.1 = ℓ
    · simp only [F, if_pos hp]
      exact spectralEnergy_term_nonneg β α hDim hβ hα P p.1 (h p.2)
    · simp only [F, if_neg hp]; exact le_refl _
  have hF_le_G : ∀ p, F p ≤ G p := by
    intro p
    by_cases hp : mercerDegAt d β α hDim hβ hα p.1 = ℓ
    · simp only [F, G, A, if_pos hp]
      have hCommon : 0 ≤ mercerEigenval d β α hDim hβ hα p.1 *
          neumannRadialCoeff β hβ (h p.2) :=
        mul_nonneg (hLamNonneg _) (hCNonneg _)
      have hModeSq := modeProj_sq_le_M_sq β α hDim hβ hα P M hModeL1Bound p.1 (h p.2)
      calc mercerEigenval d β α hDim hβ hα p.1 *
              neumannRadialCoeff β hβ (h p.2) *
              (modeProj (mercerEigenfun d β α hDim hβ hα) p.1 (h p.2) P) ^ 2
          ≤ mercerEigenval d β α hDim hβ hα p.1 *
              neumannRadialCoeff β hβ (h p.2) * (M p.1) ^ 2 :=
            mul_le_mul_of_nonneg_left hModeSq hCommon
        _ = mercerEigenval d β α hDim hβ hα p.1 * (M p.1) ^ 2 *
              neumannRadialCoeff β hβ (h p.2) := by ring
    · simp only [F, if_neg hp]
      exact mul_nonneg (hA_nonneg p.1) (hCNonneg _)
  -- A is summable (from hAngMajor, after stripping ‖·‖).
  have hA_summable : Summable A := by
    refine hAngMajor.congr ?_
    intro j
    show ‖mercerEigenval d β α hDim hβ hα j‖ * (M j) ^ 2 = A j
    simp only [A, Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
  -- Pair-summability of G, then F by domination.
  have hG_summable : Summable G :=
    Summable.mul_of_nonneg hA_summable hRadShiftSumm hA_nonneg hCNonneg
  have hF_summable : Summable F :=
    Summable.of_nonneg_of_le hF_nonneg hF_le_G hG_summable
  -- Fubini swap.
  have hSwap :
      (∑' j : ℕ, ∑' n : ℕ, F (j, n)) = ∑' n : ℕ, ∑' j : ℕ, F (j, n) := by
    have h2 := Summable.tsum_comm (f := fun j n => F (j, n)) hF_summable
    exact h2.symm
  -- Per-n bound via fibreSumWeighted_le.
  have hPer_n : ∀ n,
      (∑' j : ℕ, F (j, n)) ≤
        neumannRadialCoeff β hβ (h n) * mercerDegreeMass d β α hDim hβ hα ℓ := by
    intro n
    show (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
            mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ (h n) *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j (h n) P) ^ 2 else 0) ≤ _
    exact fibreSumWeighted_le β α hDim hβ hα P ℓ (h n)
  have hColSumm : Summable (fun n : ℕ => ∑' j : ℕ, F (j, n)) :=
    (hF_summable.prod_symm).prod
  have hRHS_summable :
      Summable (fun n : ℕ => neumannRadialCoeff β hβ (h n) *
                              mercerDegreeMass d β α hDim hβ hα ℓ) :=
    hRadShiftSumm.mul_right _
  have hMono := Summable.tsum_le_tsum hPer_n hColSumm hRHS_summable
  have hRadEval :
      (∑' n : ℕ, neumannRadialCoeff β hβ (h n) *
                  mercerDegreeMass d β α hDim hβ hα ℓ) =
        mercerDegreeMass d β α hDim hβ hα ℓ *
          ∑' n : ℕ, neumannRadialCoeff β hβ (h n) := by
    rw [tsum_mul_right, mul_comm]
  have hPushIf : ∀ j,
      (if mercerDegAt d β α hDim hβ hα j = ℓ then
          ∑' n : ℕ,
            mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ (h n) *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j (h n) P) ^ 2
          else 0) = ∑' n : ℕ, F (j, n) := by
    intro j
    by_cases hp : mercerDegAt d β α hDim hβ hα j = ℓ
    · simp only [F, if_pos hp]
    · simp only [F, if_neg hp, tsum_zero]
  rw [tsum_congr hPushIf, hSwap]
  exact hMono.trans_eq hRadEval

/-- **Per-degree radial-tail bound** at angular degree `ℓ` (specialization of
`fibreShiftedRadialSum_le_mercerDegreeMass_mass` to `h = · + (K + 1)`). -/
lemma fibreRadialTailSum_le_mercerDegreeMass_radialTailMass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ K : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        ∑' n : ℕ,
          mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ (n + (K + 1)) *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
        else 0)
      ≤ mercerDegreeMass d β α hDim hβ hα ℓ * radialTailMass β hβ K := by
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  have hRadShiftSumm : Summable (fun n : ℕ => neumannRadialCoeff β hβ (n + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).mpr hRadSumm
  exact fibreShiftedRadialSum_le_mercerDegreeMass_mass β α hDim hβ hα P ℓ
    (fun n => n + (K + 1)) hRadShiftSumm

/-- **Per-degree full-radial-sum bound** at angular degree `ℓ`: the full
radial-sum energy at angular degree `ℓ` is bounded by `mercerDegreeMass ℓ ·
radialTotalMass`.

Specialization of `fibreShiftedRadialSum_le_mercerDegreeMass_mass` to `h = id`. -/
lemma fibreRadialFullSum_le_mercerDegreeMass_radialTotalMass
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (ℓ : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j = ℓ then
        ∑' k : ℕ,
          mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2
        else 0)
      ≤ mercerDegreeMass d β α hDim hβ hα ℓ * radialTotalMass β hβ := by
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  have hRadIdSumm : Summable (fun n : ℕ => neumannRadialCoeff β hβ (id n)) := by
    simpa using hRadSumm
  exact fibreShiftedRadialSum_le_mercerDegreeMass_mass β α hDim hβ hα P ℓ id hRadIdSumm

/-- The radial total mass is non-negative. -/
lemma radialTotalMass_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ radialTotalMass β hβ :=
  tsum_nonneg (neumannRadialCoeff_nonneg β hβ)

/-- The radial tail mass is non-negative. -/
lemma radialTailMass_nonneg (β : ℝ) (hβ : 0 < β) (K : ℕ) :
    0 ≤ radialTailMass β hβ K :=
  tsum_nonneg (fun n => neumannRadialCoeff_nonneg β hβ (n + (K + 1)))

set_option maxHeartbeats 800000 in
/-- **Closed-form bound on the radial tail at the kept angular range**: the
radial-tail energy at angular degrees `ℓ ≤ L` is bounded by
`angularPrefixMass_closedForm L · radialTailMass K`.

Decomposition pattern:
- Pointwise identity at each `j`: `(if degAt j ≤ L then F j else 0) =
  Σ_{ℓ ∈ range (L+1)} (if degAt j = ℓ then F j else 0)`.
- Swap the finite Σ with the outer ∑' (using `Summable.tsum_finsetSum` after
  proving per-ℓ summability via the bridge majorant `lamV j · M_j²`).
- Apply the per-degree radial-tail bound summed over ℓ. -/
lemma spectralRadialTailAtPrefix_le_closedForm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j ≤ L then
        ∑' n : ℕ,
          mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ (n + (K + 1)) *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
        else 0)
      ≤ angularPrefixMass_closedForm d β α hDim hβ hα L * radialTailMass β hβ K := by
  obtain ⟨M, _hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ :=
    spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  have hLamNonneg : ∀ j, 0 ≤ mercerEigenval d β α hDim hβ hα j :=
    mercerEigenval_nonneg d β α hDim hβ hα
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  have hRadShiftSumm : Summable (fun n : ℕ => neumannRadialCoeff β hβ (n + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).mpr hRadSumm
  -- Bridge majorant.
  set A : ℕ → ℝ := fun j => mercerEigenval d β α hDim hβ hα j * (M j) ^ 2
  have hA_nonneg : ∀ j, 0 ≤ A j := fun j => mul_nonneg (hLamNonneg j) (sq_nonneg _)
  have hA_summable : Summable A := by
    refine hAngMajor.congr ?_
    intro j
    show ‖mercerEigenval d β α hDim hβ hα j‖ * (M j) ^ 2 = A j
    simp only [A, Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
  -- Per-j inner non-negativity.
  have hInner_nonneg : ∀ j n,
      0 ≤ mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ (n + (K + 1)) *
            (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2 :=
    fun j n => spectralEnergy_term_nonneg β α hDim hβ hα P j (n + (K + 1))
  -- Per-(j, n) bridge bound.
  have hInner_le : ∀ j n,
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ (n + (K + 1)) *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2 ≤
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ (n + (K + 1)) * (M j) ^ 2 := by
    intro j n
    apply mul_le_mul_of_nonneg_left
    · exact modeProj_sq_le_M_sq β α hDim hβ hα P M hModeL1Bound j (n + (K + 1))
    · exact mul_nonneg (hLamNonneg _) (neumannRadialCoeff_nonneg β hβ _)
  -- Per-j: F j ≤ A j * radialTailMass K, where F j = ∑' n, term j (n+K+1).
  have hF_le : ∀ j,
      (∑' n, mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ (n + (K + 1)) *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2)
        ≤ A j * radialTailMass β hβ K := by
    intro j
    have hRHSSumm : Summable (fun n =>
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ (n + (K + 1)) * (M j) ^ 2) := by
      have h1 := hRadShiftSumm.mul_left (mercerEigenval d β α hDim hβ hα j)
      exact h1.mul_right ((M j) ^ 2)
    have hLHSSumm : Summable (fun n =>
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ (n + (K + 1)) *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2) :=
      Summable.of_nonneg_of_le (hInner_nonneg j) (hInner_le j) hRHSSumm
    have hMono := hLHSSumm.tsum_le_tsum (hInner_le j) hRHSSumm
    have hRHS_eval : (∑' n, mercerEigenval d β α hDim hβ hα j *
                      neumannRadialCoeff β hβ (n + (K + 1)) * (M j) ^ 2) =
        A j * radialTailMass β hβ K := by
      have hRew : (fun n => mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ (n + (K + 1)) * (M j) ^ 2) =
                (fun n => A j * neumannRadialCoeff β hβ (n + (K + 1))) := by
        funext n; simp only [A]; ring
      rw [hRew, tsum_mul_left]
      rfl
    exact hMono.trans_eq hRHS_eval
  -- Per-ℓ summability of the if-fibre version.
  have hG_summable : ∀ ℓ : ℕ,
      Summable (fun j => if mercerDegAt d β α hDim hβ hα j = ℓ then
          ∑' n, mercerEigenval d β α hDim hβ hα j *
                neumannRadialCoeff β hβ (n + (K + 1)) *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
          else 0) := by
    intro ℓ
    refine Summable.of_nonneg_of_le ?_ ?_ (hA_summable.mul_right (radialTailMass β hβ K))
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j = ℓ
      · simp only [if_pos h]; exact tsum_nonneg (hInner_nonneg j)
      · simp only [if_neg h]; exact le_refl _
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j = ℓ
      · simp only [if_pos h]; exact hF_le j
      · simp only [if_neg h]
        exact mul_nonneg (hA_nonneg j) (radialTailMass_nonneg β hβ K)
  -- Pointwise identity at each j.
  have hPointwise : ∀ j,
      (if mercerDegAt d β α hDim hβ hα j ≤ L then
          ∑' n, mercerEigenval d β α hDim hβ hα j *
                neumannRadialCoeff β hβ (n + (K + 1)) *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
          else 0) =
        ∑ ℓ ∈ Finset.range (L + 1),
          (if mercerDegAt d β α hDim hβ hα j = ℓ then
              ∑' n, mercerEigenval d β α hDim hβ hα j *
                    neumannRadialCoeff β hβ (n + (K + 1)) *
                    (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
            else 0) := by
    intro j
    by_cases hLe : mercerDegAt d β α hDim hβ hα j ≤ L
    · rw [if_pos hLe]
      rw [Finset.sum_eq_single (mercerDegAt d β α hDim hβ hα j)]
      · rw [if_pos rfl]
      · intro ℓ' _ hne
        rw [if_neg (fun h => hne h.symm)]
      · intro hNotMem
        exfalso; apply hNotMem
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hLe
    · rw [if_neg hLe]
      symm
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [Finset.mem_range, Nat.lt_succ_iff] at hℓ
      rw [if_neg]
      intro h; exact hLe (h ▸ hℓ)
  -- Apply to outer tsum: ∑' j, [pointwise LHS] = ∑' j, [Σ ...].
  rw [tsum_congr hPointwise]
  -- Swap finite Σ with ∑'.
  rw [Summable.tsum_finsetSum (fun ℓ _ => hG_summable ℓ)]
  -- Per-degree radial-tail bound, summed over ℓ ∈ range (L+1).
  have hPer_ℓ : ∀ ℓ ∈ Finset.range (L + 1),
      (∑' j, if mercerDegAt d β α hDim hβ hα j = ℓ then
            ∑' n, mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ (n + (K + 1)) *
                  (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
          else 0) ≤
        mercerDegreeMass d β α hDim hβ hα ℓ * radialTailMass β hβ K :=
    fun ℓ _ => fibreRadialTailSum_le_mercerDegreeMass_radialTailMass β α hDim hβ hα P ℓ K
  calc ∑ ℓ ∈ Finset.range (L + 1),
          (∑' j, if mercerDegAt d β α hDim hβ hα j = ℓ then
                ∑' n, mercerEigenval d β α hDim hβ hα j *
                      neumannRadialCoeff β hβ (n + (K + 1)) *
                      (modeProj (mercerEigenfun d β α hDim hβ hα) j (n + (K + 1)) P) ^ 2
              else 0)
      ≤ ∑ ℓ ∈ Finset.range (L + 1),
          mercerDegreeMass d β α hDim hβ hα ℓ * radialTailMass β hβ K :=
        Finset.sum_le_sum hPer_ℓ
    _ = (∑ ℓ ∈ Finset.range (L + 1), mercerDegreeMass d β α hDim hβ hα ℓ) *
          radialTailMass β hβ K := by rw [← Finset.sum_mul]
    _ = angularPrefixMass_closedForm d β α hDim hβ hα L * radialTailMass β hβ K := rfl

set_option maxHeartbeats 1200000 in
/-- **Closed-form bound on the angular tail**: the energy at angular modes `j`
with `degAt j > L` (over all radial `k`) is bounded by
`angularTailMass_closedForm L · radialTotalMass`.

Decomposition pattern:
- Pointwise identity at each `j`: `(if degAt j ≤ L then 0 else F j) =
  ∑' i, (if degAt j = i + (L + 1) then F j else 0)` (at most one nonzero
  term, at `i = degAt j - (L + 1)`).
- Pair-summability of `H : ℕ × ℕ → ℝ` via `summable_prod_of_nonneg`:
  per-row `H (j, ·)` is finite-supported, sum-of-row-tsums dominated by the
  bridge majorant.
- Fubini swap `∑' j (∑' i, H) = ∑' i (∑' j, H)` then per-degree
  full-radial-sum bound. -/
lemma spectralAngularTail_le_closedForm
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L : ℕ) :
    (∑' j : ℕ, if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else
        ∑' k : ℕ,
          mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2)
      ≤ angularTailMass_closedForm d β α hDim hβ hα L * radialTotalMass β hβ := by
  obtain ⟨M, _hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ :=
    spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  have hLamNonneg : ∀ j, 0 ≤ mercerEigenval d β α hDim hβ hα j :=
    mercerEigenval_nonneg d β α hDim hβ hα
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  set A : ℕ → ℝ := fun j => mercerEigenval d β α hDim hβ hα j * (M j) ^ 2
  have hA_nonneg : ∀ j, 0 ≤ A j := fun j => mul_nonneg (hLamNonneg j) (sq_nonneg _)
  have hA_summable : Summable A := by
    refine hAngMajor.congr ?_
    intro j
    show ‖mercerEigenval d β α hDim hβ hα j‖ * (M j) ^ 2 = A j
    simp only [A, Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
  have hInner_nonneg : ∀ j k,
      0 ≤ mercerEigenval d β α hDim hβ hα j *
            neumannRadialCoeff β hβ k *
            (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 :=
    spectralEnergy_term_nonneg β α hDim hβ hα P
  have hInner_le : ∀ j k,
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k *
        (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 ≤
      mercerEigenval d β α hDim hβ hα j *
        neumannRadialCoeff β hβ k * (M j) ^ 2 := by
    intro j k
    apply mul_le_mul_of_nonneg_left
    · exact modeProj_sq_le_M_sq β α hDim hβ hα P M hModeL1Bound j k
    · exact mul_nonneg (hLamNonneg _) (neumannRadialCoeff_nonneg β hβ _)
  have hF_nonneg : ∀ j,
      0 ≤ ∑' k, mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ k *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 :=
    fun j => tsum_nonneg (hInner_nonneg j)
  have hF_le : ∀ j,
      (∑' k, mercerEigenval d β α hDim hβ hα j *
              neumannRadialCoeff β hβ k *
              (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2)
        ≤ A j * radialTotalMass β hβ := by
    intro j
    have hLHSSumm : Summable (fun k =>
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k *
          (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2) := by
      apply Summable.of_nonneg_of_le (fun k => hInner_nonneg j k) (hInner_le j)
      have h1 := hRadSumm.mul_left (mercerEigenval d β α hDim hβ hα j)
      exact h1.mul_right ((M j) ^ 2)
    have hRHSSumm : Summable (fun k =>
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k * (M j) ^ 2) := by
      have h1 := hRadSumm.mul_left (mercerEigenval d β α hDim hβ hα j)
      exact h1.mul_right ((M j) ^ 2)
    have hMono := hLHSSumm.tsum_le_tsum (hInner_le j) hRHSSumm
    have hRHS_eval : (∑' k, mercerEigenval d β α hDim hβ hα j *
                      neumannRadialCoeff β hβ k * (M j) ^ 2) =
        A j * radialTotalMass β hβ := by
      have hRew : (fun k => mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ k * (M j) ^ 2) =
                (fun k => A j * neumannRadialCoeff β hβ k) := by
        funext k; simp only [A]; ring
      rw [hRew, tsum_mul_left]
      rfl
    exact hMono.trans_eq hRHS_eval
  -- Define H : ℕ × ℕ → ℝ.
  set H : ℕ × ℕ → ℝ := fun p =>
    if mercerDegAt d β α hDim hβ hα p.1 = p.2 + (L + 1) then
      ∑' k, mercerEigenval d β α hDim hβ hα p.1 *
            neumannRadialCoeff β hβ k *
            (modeProj (mercerEigenfun d β α hDim hβ hα) p.1 k P) ^ 2
    else 0
  have hH_nonneg : ∀ p, 0 ≤ H p := by
    intro p
    by_cases h : mercerDegAt d β α hDim hβ hα p.1 = p.2 + (L + 1)
    · simp only [H, if_pos h]; exact hF_nonneg p.1
    · simp only [H, if_neg h]; exact le_refl _
  -- Per-row summability of H: support contained in {i | i + L + 1 = degAt j} ⊆ range (degAt j).
  have hH_row_summ : ∀ j, Summable (fun i => H (j, i)) := by
    intro j
    apply summable_of_ne_finset_zero
      (s := Finset.range (mercerDegAt d β α hDim hβ hα j + 1))
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [H]
    rw [if_neg]
    intro hEq
    apply hi
    omega
  -- Per-row tsum: ∑' i, H (j, i) = if degAt j ≤ L then 0 else F j.
  have hH_row_tsum : ∀ j,
      (∑' i, H (j, i)) =
        if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else
          ∑' k, mercerEigenval d β α hDim hβ hα j *
                neumannRadialCoeff β hβ k *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
    intro j
    by_cases hLe : mercerDegAt d β α hDim hβ hα j ≤ L
    · rw [if_pos hLe]
      have hAllZero : ∀ i, H (j, i) = 0 := by
        intro i
        simp only [H]
        rw [if_neg]
        intro hEq
        omega
      rw [tsum_congr hAllZero]
      exact tsum_zero
    · rw [if_neg hLe]
      have hL_lt : L + 1 ≤ mercerDegAt d β α hDim hβ hα j := by omega
      let i₀ := mercerDegAt d β α hDim hβ hα j - (L + 1)
      have hi₀_eq : mercerDegAt d β α hDim hβ hα j = i₀ + (L + 1) := by omega
      have hOnly : ∀ i', i' ≠ i₀ → H (j, i') = 0 := by
        intro i' hne
        simp only [H]
        rw [if_neg]
        intro hEq
        apply hne
        omega
      have hAt : H (j, i₀) =
          ∑' k, mercerEigenval d β α hDim hβ hα j *
                neumannRadialCoeff β hβ k *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 := by
        simp only [H]
        rw [if_pos hi₀_eq]
      rw [tsum_eq_single i₀ hOnly, hAt]
  -- Sum-of-row-tsums summability: bounded by F j ≤ A j · radTotal.
  have hRowTsum_summ : Summable (fun j => ∑' i, H (j, i)) := by
    apply Summable.of_nonneg_of_le _ _ (hA_summable.mul_right (radialTotalMass β hβ))
    · intro j
      rw [hH_row_tsum]
      by_cases hLe : mercerDegAt d β α hDim hβ hα j ≤ L
      · rw [if_pos hLe]
      · rw [if_neg hLe]; exact hF_nonneg j
    · intro j
      rw [hH_row_tsum]
      by_cases hLe : mercerDegAt d β α hDim hβ hα j ≤ L
      · rw [if_pos hLe]
        exact mul_nonneg (hA_nonneg j) (radialTotalMass_nonneg β hβ)
      · rw [if_neg hLe]; exact hF_le j
  -- Pair-summability of H.
  have hH_summable : Summable H := by
    rw [summable_prod_of_nonneg hH_nonneg]
    exact ⟨hH_row_summ, hRowTsum_summ⟩
  -- Pointwise identity: (if degAt ≤ L then 0 else F j) = ∑' i, H (j, i).
  have hPointwise : ∀ j,
      (if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else
          ∑' k, mercerEigenval d β α hDim hβ hα j *
                neumannRadialCoeff β hβ k *
                (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2) =
        ∑' i, H (j, i) := fun j => (hH_row_tsum j).symm
  -- Apply tsum_congr.
  rw [tsum_congr hPointwise]
  -- Fubini swap.
  have hSwap :
      (∑' j : ℕ, ∑' i : ℕ, H (j, i)) = ∑' i : ℕ, ∑' j : ℕ, H (j, i) := by
    have h := Summable.tsum_comm (f := fun j i => H (j, i)) hH_summable
    exact h.symm
  rw [hSwap]
  -- Per-i bound: ∑' j, H (j, i) ≤ mercerDegreeMass (i + L + 1) · radialTotalMass.
  have hPer_i : ∀ i,
      (∑' j, H (j, i)) ≤
        mercerDegreeMass d β α hDim hβ hα (i + (L + 1)) * radialTotalMass β hβ := by
    intro i
    show (∑' j, if mercerDegAt d β α hDim hβ hα j = i + (L + 1) then
            ∑' k, mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ k *
                  (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2 else 0) ≤ _
    exact fibreRadialFullSum_le_mercerDegreeMass_radialTotalMass β α hDim hβ hα P
      (i + (L + 1))
  -- Tsum monotonicity.
  have hColSumm : Summable (fun i : ℕ => ∑' j : ℕ, H (j, i)) :=
    (hH_summable.prod_symm).prod
  have hRHS_summable :
      Summable (fun i : ℕ => mercerDegreeMass d β α hDim hβ hα (i + (L + 1)) *
                              radialTotalMass β hβ) := by
    have hMass_summable := mercerDegreeMass_summable d β α hDim hβ hα
    have hShifted : Summable (fun i => mercerDegreeMass d β α hDim hβ hα (i + (L + 1))) :=
      (summable_nat_add_iff (L + 1)).mpr hMass_summable
    exact hShifted.mul_right _
  have hMono := Summable.tsum_le_tsum hPer_i hColSumm hRHS_summable
  have hRHS_eval :
      (∑' i, mercerDegreeMass d β α hDim hβ hα (i + (L + 1)) * radialTotalMass β hβ) =
        angularTailMass_closedForm d β α hDim hβ hα L * radialTotalMass β hβ := by
    rw [tsum_mul_right]
    rfl
  exact hMono.trans_eq hRHS_eval

/-! ### Combined closed-form joint truncation error bound -/

/-- The closed-form upper bound on the joint truncation deviation.

Sum of:
- angular tail piece: `angularTailMass_closedForm L · radialTotalMass`
- radial-tail-at-prefix piece: `angularPrefixMass_closedForm L · radialTailMass_closedForm K`

P-uniform; explicit in `(β, α, d, L, K)`. -/
noncomputable def spectralTruncationClosedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (L K : ℕ) : ℝ :=
  angularTailMass_closedForm d β α hDim hβ hα L * radialTotalMass β hβ +
    angularPrefixMass_closedForm d β α hDim hβ hα L * radialTailMass_closedForm β K

set_option maxHeartbeats 1600000 in
/-- **Closed-form joint truncation error bound** (degree-indexed).

The deviation between the full spectral energy and its joint angular-and-radial
truncation `spectralEnergyTruncatedByDegree` (where `L` is the highest angular
degree kept and `K` the highest radial mode kept) is bounded by an explicit
closed-form expression in `(β, α, d, L, K)`. P-uniform.

Proof outline:
- Per-j: `∑' k, term j k` decomposes (case-split on `degAt j ≤ L`) as
  `truncated_j + radial-tail-at-prefix_j + angular-tail_j`, where the three
  pieces are exactly the integrands of `spectralEnergyTruncatedByDegree`,
  the closed-form radial-tail bound, and the closed-form angular-tail bound.
- Outer linearity of tsum (with bridge-axiom-derived summabilities) gives
  `spectralEnergy = spectralEnergyTruncatedByDegree + radial-tail + angular-tail`.
- Hence the absolute deviation equals `radial-tail + angular-tail`, which is
  bounded by the closed-form expression. -/
theorem spectralEnergyTruncatedByDegree_error_le_explicit
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    |spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ) P
      - spectralEnergyTruncatedByDegree
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (mercerDegAt d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P|
      ≤ spectralTruncationClosedForm d β α hDim hβ hα L K := by
  obtain ⟨M, _hMNonneg, _hModeInt, hModeL1Bound, hAngMajor⟩ :=
    spectral_modeL1_factorized_bridge_imported β α hDim hβ hα P
  have hLamNonneg : ∀ j, 0 ≤ mercerEigenval d β α hDim hβ hα j :=
    mercerEigenval_nonneg d β α hDim hβ hα
  have hRadSumm : Summable (neumannRadialCoeff β hβ) :=
    summable_neumannRadialCoeff_of_summable_neumannCosineCoeff β hβ
      (summable_neumannCosineCoeff_imported β hβ)
  set A : ℕ → ℝ := fun j => mercerEigenval d β α hDim hβ hα j * (M j) ^ 2
  have hA_nonneg : ∀ j, 0 ≤ A j := fun j => mul_nonneg (hLamNonneg j) (sq_nonneg _)
  have hA_summable : Summable A := by
    refine hAngMajor.congr ?_
    intro j
    show ‖mercerEigenval d β α hDim hβ hα j‖ * (M j) ^ 2 = A j
    simp only [A, Real.norm_eq_abs, abs_of_nonneg (hLamNonneg j)]
  set term : ℕ → ℕ → ℝ := fun j k =>
    mercerEigenval d β α hDim hβ hα j * neumannRadialCoeff β hβ k *
      (modeProj (mercerEigenfun d β α hDim hβ hα) j k P) ^ 2
  have hterm_nonneg : ∀ j k, 0 ≤ term j k :=
    spectralEnergy_term_nonneg β α hDim hβ hα P
  have hterm_le : ∀ j k,
      term j k ≤ mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ k * (M j) ^ 2 := by
    intro j k
    apply mul_le_mul_of_nonneg_left
    · exact modeProj_sq_le_M_sq β α hDim hβ hα P M hModeL1Bound j k
    · exact mul_nonneg (hLamNonneg _) (neumannRadialCoeff_nonneg β hβ _)
  have hInner_summ : ∀ j, Summable (fun k => term j k) := by
    intro j
    apply Summable.of_nonneg_of_le (fun k => hterm_nonneg j k) (hterm_le j)
    have h1 := hRadSumm.mul_left (mercerEigenval d β α hDim hβ hα j)
    exact h1.mul_right ((M j) ^ 2)
  have hF_le : ∀ j, (∑' k, term j k) ≤ A j * radialTotalMass β hβ := by
    intro j
    have hRHSSumm : Summable (fun k =>
        mercerEigenval d β α hDim hβ hα j *
          neumannRadialCoeff β hβ k * (M j) ^ 2) := by
      have h1 := hRadSumm.mul_left (mercerEigenval d β α hDim hβ hα j)
      exact h1.mul_right ((M j) ^ 2)
    have hMono := (hInner_summ j).tsum_le_tsum (hterm_le j) hRHSSumm
    have hRHS_eval : (∑' k, mercerEigenval d β α hDim hβ hα j *
                      neumannRadialCoeff β hβ k * (M j) ^ 2) =
        A j * radialTotalMass β hβ := by
      have hRew : (fun k => mercerEigenval d β α hDim hβ hα j *
                  neumannRadialCoeff β hβ k * (M j) ^ 2) =
                (fun k => A j * neumannRadialCoeff β hβ k) := by
        funext k; simp only [A]; ring
      rw [hRew, tsum_mul_left]
      rfl
    exact hMono.trans_eq hRHS_eval
  -- Outer summability: F j = ∑' k, term j k is summable in j.
  have hOuterSumm : Summable (fun j => ∑' k, term j k) :=
    Summable.of_nonneg_of_le
      (fun j => tsum_nonneg (fun k => hterm_nonneg j k))
      hF_le (hA_summable.mul_right (radialTotalMass β hβ))
  -- Each piece (truncated, radial-tail-at-prefix, angular-tail) is summable in j.
  have hTruncSumm : Summable (fun j =>
      if mercerDegAt d β α hDim hβ hα j ≤ L then
        ∑ k ∈ Finset.range (K + 1), term j k else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hOuterSumm
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]
        exact Finset.sum_nonneg (fun k _ => hterm_nonneg j k)
      · simp only [if_neg h]; exact le_refl _
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]
        exact (hInner_summ j).sum_le_tsum (Finset.range (K + 1))
          (fun k _ => hterm_nonneg j k)
      · simp only [if_neg h]
        exact tsum_nonneg (fun k => hterm_nonneg j k)
  have hRadTailAtPrefixSumm : Summable (fun j =>
      if mercerDegAt d β α hDim hβ hα j ≤ L then
        ∑' n, term j (n + (K + 1)) else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hOuterSumm
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]
        exact tsum_nonneg (fun n => hterm_nonneg j (n + (K + 1)))
      · simp only [if_neg h]; exact le_refl _
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]
        have hShiftSumm : Summable (fun n => term j (n + (K + 1))) :=
          (summable_nat_add_iff (K + 1)).mpr (hInner_summ j)
        have hShifted_le : ∀ n, term j (n + (K + 1)) ≤ term j (n + (K + 1)) :=
          fun n => le_refl _
        have hSplit := (hInner_summ j).sum_add_tsum_nat_add (K + 1)
        have hPrefixNonneg : 0 ≤ ∑ k ∈ Finset.range (K + 1), term j k :=
          Finset.sum_nonneg (fun k _ => hterm_nonneg j k)
        linarith
      · simp only [if_neg h]
        exact tsum_nonneg (fun k => hterm_nonneg j k)
  have hAngTailSumm : Summable (fun j =>
      if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else ∑' k, term j k) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hOuterSumm
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]; exact le_refl _
      · simp only [if_neg h]; exact tsum_nonneg (fun k => hterm_nonneg j k)
    · intro j
      by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
      · simp only [if_pos h]; exact tsum_nonneg (fun k => hterm_nonneg j k)
      · simp only [if_neg h]; exact le_refl _
  -- Per-j decomposition.
  have hPerJDecomp : ∀ j,
      (∑' k, term j k) =
        (if mercerDegAt d β α hDim hβ hα j ≤ L then
            ∑ k ∈ Finset.range (K + 1), term j k else 0) +
        (if mercerDegAt d β α hDim hβ hα j ≤ L then
            ∑' n, term j (n + (K + 1)) else 0) +
        (if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else ∑' k, term j k) := by
    intro j
    by_cases hLe : mercerDegAt d β α hDim hβ hα j ≤ L
    · simp only [if_pos hLe]
      have hSplit := (hInner_summ j).sum_add_tsum_nat_add (K + 1)
      linarith
    · simp only [if_neg hLe]
      ring
  -- Outer decomposition: spectralEnergy = truncated + radTailAtPrefix + angTail.
  have hOuterDecomp :
      (∑' j, ∑' k, term j k) =
        (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
            ∑ k ∈ Finset.range (K + 1), term j k else 0) +
        (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
            ∑' n, term j (n + (K + 1)) else 0) +
        (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else ∑' k, term j k) := by
    rw [tsum_congr hPerJDecomp]
    rw [Summable.tsum_add (hTruncSumm.add hRadTailAtPrefixSumm) hAngTailSumm,
        Summable.tsum_add hTruncSumm hRadTailAtPrefixSumm]
  -- Each piece is non-negative.
  have hRadTailAtPrefixNonneg :
      0 ≤ ∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
            ∑' n, term j (n + (K + 1)) else 0 := by
    apply tsum_nonneg
    intro j
    by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
    · simp only [if_pos h]; exact tsum_nonneg (fun n => hterm_nonneg j (n + (K + 1)))
    · simp only [if_neg h]; exact le_refl _
  have hAngTailNonneg :
      0 ≤ ∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else ∑' k, term j k := by
    apply tsum_nonneg
    intro j
    by_cases h : mercerDegAt d β α hDim hβ hα j ≤ L
    · simp only [if_pos h]; exact le_refl _
    · simp only [if_neg h]; exact tsum_nonneg (fun k => hterm_nonneg j k)
  -- spectralEnergy and spectralEnergyTruncatedByDegree definitional unfolds.
  have hSpectralUnfold :
      spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ) P =
        ∑' j, ∑' k, term j k := rfl
  have hTruncUnfold :
      spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          L K P =
        ∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
          ∑ k ∈ Finset.range (K + 1), term j k else 0 := rfl
  -- spectralEnergy - truncated = radTailAtPrefix + angTail.
  have hDiffEq :
      spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ) P
        - spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          L K P
        =
      (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
          ∑' n, term j (n + (K + 1)) else 0) +
      (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then 0 else ∑' k, term j k) := by
    rw [hSpectralUnfold, hTruncUnfold, hOuterDecomp]; ring
  -- |...| = ...
  have hDiffNonneg :
      0 ≤ spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ) P
        - spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          L K P := by
    rw [hDiffEq]
    linarith
  rw [abs_of_nonneg hDiffNonneg, hDiffEq]
  -- Bound each piece via the closed-form lemmas, then chain via radialTailMass ≤ closedForm.
  have hAngTailBound :=
    spectralAngularTail_le_closedForm β α hDim hβ hα P L
  have hRadTailBound :=
    spectralRadialTailAtPrefix_le_closedForm β α hDim hβ hα P L K
  have hRadTailClosed := radialTailMass_le_closedForm β hβ K
  have hPrefixNonneg : 0 ≤ angularPrefixMass_closedForm d β α hDim hβ hα L := by
    unfold angularPrefixMass_closedForm
    exact Finset.sum_nonneg (fun ℓ _ => mercerDegreeMass_nonneg d β α hDim hβ hα ℓ)
  have hRadTailBoundClosed :
      (∑' j, if mercerDegAt d β α hDim hβ hα j ≤ L then
          ∑' n, term j (n + (K + 1)) else 0)
        ≤ angularPrefixMass_closedForm d β α hDim hβ hα L *
          radialTailMass_closedForm β K := by
    refine hRadTailBound.trans ?_
    exact mul_le_mul_of_nonneg_left hRadTailClosed hPrefixNonneg
  unfold spectralTruncationClosedForm
  linarith [hAngTailBound, hRadTailBoundClosed]

/-- Kernel-energy form of the closed-form joint truncation error bound. -/
theorem kernelEnergy_truncationByDegree_error_le_explicit
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) (L K : ℕ) :
    |kernelEnergy (wristbandKernelNeumann (d := d) β α) P
      - spectralEnergyTruncatedByDegree
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (mercerDegAt d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        L K P|
      ≤ spectralTruncationClosedForm d β α hDim hβ hα L K := by
  rw [← spectralEnergy_eq_kernelEnergy (d := d) β α hDim hβ hα P]
  exact spectralEnergyTruncatedByDegree_error_le_explicit β α hDim hβ hα P L K

/-- The closed-form angular prefix mass is at most 1 (since prefix + tail = 1
and tail ≥ 0). -/
lemma angularPrefixMass_closedForm_le_one
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) (L : ℕ) :
    angularPrefixMass_closedForm d β α hDim hβ hα L ≤ 1 := by
  have hSum := angularPrefixMass_add_tailMass_closedForm d β α hDim hβ hα L
  have hTailNonneg : 0 ≤ angularTailMass_closedForm d β α hDim hβ hα L := by
    unfold angularTailMass_closedForm
    exact tsum_nonneg (fun n => mercerDegreeMass_nonneg d β α hDim hβ hα _)
  linarith

/-- The closed-form joint truncation bound tends to `0` as `(L, K) → ∞`
jointly on `atTop ×ˢ atTop`. -/
theorem tendsto_spectralTruncationClosedForm
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    Tendsto (fun p : ℕ × ℕ =>
        spectralTruncationClosedForm d β α hDim hβ hα p.1 p.2)
      (atTop ×ˢ atTop) (𝓝 0) := by
  -- Angular-tail piece a(L) → 0 (depends only on L).
  have hAng : Tendsto (fun L : ℕ =>
      angularTailMass_closedForm d β α hDim hβ hα L * radialTotalMass β hβ)
      atTop (𝓝 0) := by
    have h := (tendsto_angularTailMass_closedForm d β α hDim hβ hα).mul_const
      (radialTotalMass β hβ)
    simpa using h
  have hAngProd : Tendsto (fun p : ℕ × ℕ =>
      angularTailMass_closedForm d β α hDim hβ hα p.1 * radialTotalMass β hβ)
      (atTop ×ˢ atTop) (𝓝 0) :=
    hAng.comp (tendsto_fst (f := atTop) (g := atTop))
  -- Radial-tail piece b(L, K) → 0: dominated by radialTailMass_closedForm K.
  have hRadProd : Tendsto (fun p : ℕ × ℕ =>
      radialTailMass_closedForm β p.2) (atTop ×ˢ atTop) (𝓝 0) :=
    (tendsto_radialTailMass_closedForm β hβ).comp
      (tendsto_snd (f := atTop) (g := atTop))
  have hPrefixBound : ∀ p : ℕ × ℕ,
      |angularPrefixMass_closedForm d β α hDim hβ hα p.1 *
        radialTailMass_closedForm β p.2| ≤
        radialTailMass_closedForm β p.2 := by
    intro p
    have hPrefixNonneg : 0 ≤ angularPrefixMass_closedForm d β α hDim hβ hα p.1 := by
      unfold angularPrefixMass_closedForm
      exact Finset.sum_nonneg
        (fun ℓ _ => mercerDegreeMass_nonneg d β α hDim hβ hα ℓ)
    have hPrefixLe : angularPrefixMass_closedForm d β α hDim hβ hα p.1 ≤ 1 :=
      angularPrefixMass_closedForm_le_one d β α hDim hβ hα p.1
    have hRadNonneg : 0 ≤ radialTailMass_closedForm β p.2 := by
      have h := radialTailMass_le_closedForm β hβ p.2
      have h2 := radialTailMass_nonneg β hβ p.2
      linarith
    rw [abs_of_nonneg (mul_nonneg hPrefixNonneg hRadNonneg)]
    calc angularPrefixMass_closedForm d β α hDim hβ hα p.1 *
            radialTailMass_closedForm β p.2
        ≤ 1 * radialTailMass_closedForm β p.2 :=
          mul_le_mul_of_nonneg_right hPrefixLe hRadNonneg
      _ = radialTailMass_closedForm β p.2 := by ring
  have hRad : Tendsto (fun p : ℕ × ℕ =>
      angularPrefixMass_closedForm d β α hDim hβ hα p.1 *
        radialTailMass_closedForm β p.2) (atTop ×ˢ atTop) (𝓝 0) := by
    refine squeeze_zero_norm hPrefixBound ?_
    simpa [Real.norm_eq_abs] using hRadProd
  -- Sum tends to 0.
  have hSum := hAngProd.add hRad
  simpa [spectralTruncationClosedForm] using hSum

/-- **Joint convergence of the truncated spectral energy** on `atTop ×ˢ atTop`.

As `(L, K) → ∞` jointly (highest angular degree and highest radial mode),
`spectralEnergyTruncatedByDegree L K P → spectralEnergy P` for any
distribution `P`.  Squeeze argument using the closed-form joint bound. -/
theorem spectralEnergyTruncatedByDegree_tendsto_full
    {d : ℕ} (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    Tendsto (fun p : ℕ × ℕ =>
        spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          p.1 p.2 P)
      (atTop ×ˢ atTop)
      (𝓝 (spectralEnergy
            (mercerEigenfun d β α hDim hβ hα)
            (mercerEigenval d β α hDim hβ hα)
            (neumannConstantCoeff β hβ)
            (neumannCosineCoeff β hβ) P)) := by
  -- Squeeze on the closed-form bound: |truncated - full| ≤ closedForm → 0.
  set Espec := spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ) P
  have hBound : ∀ p : ℕ × ℕ,
      |spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          p.1 p.2 P - Espec|
        ≤ spectralTruncationClosedForm d β α hDim hβ hα p.1 p.2 := by
    intro p
    rw [abs_sub_comm]
    exact spectralEnergyTruncatedByDegree_error_le_explicit β α hDim hβ hα P p.1 p.2
  have hClosed := tendsto_spectralTruncationClosedForm d β α hDim hβ hα
  have hDiff : Tendsto (fun p : ℕ × ℕ =>
      spectralEnergyTruncatedByDegree
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (mercerDegAt d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          p.1 p.2 P - Espec) (atTop ×ˢ atTop) (𝓝 0) := by
    refine squeeze_zero_norm hBound ?_
    simpa [Real.norm_eq_abs] using hClosed
  have := hDiff.add (tendsto_const_nhds (x := Espec) (f := atTop ×ˢ atTop))
  simpa using this

end WristbandLossProofs
