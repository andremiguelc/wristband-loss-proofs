import WristbandLossProofs.KernelFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Kernel Energy Minimization

This file proves **Hypothesis K**: the wristband kernel energy is uniquely
minimized at the uniform measure `μ₀ = σ_{d-1} ⊗ Unif[0,1]`.

The proof follows the standard MMD pathway:
1. The kernel is PSD → `MMD²(P, μ₀) ≥ 0`.
2. The potential `h(w) = E_{W'~μ₀}[K(w,W')]` is constant → energy-MMD
   identity: `E(P) - E(μ₀) = MMD²(P, μ₀)`.
3. The kernel is characteristic → `MMD² = 0 ⟹ P = μ₀`.
4. Combining: `E(P) ≥ E(μ₀)`, with equality iff `P = μ₀`.

The result is stated for the Neumann kernel (infinite reflection series),
which has exactly constant potential. A truncation bound relates this to
the 3-image kernel actually used in Python.
-/

/-! ### PSD of the joint kernel

Product of PSD kernels is PSD (Schur product theorem for kernel
functions). -/

/-- Product of two PSD kernels (on possibly different spaces) gives a
    PSD kernel on the product space.
    This is the kernel-function version of the Schur product theorem. -/
theorem productKernel_posSemiDef
    {X : Type*} {Y : Type*}
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsPosSemiDefKernel Kx)
    (hKy : IsPosSemiDefKernel Ky) :
    IsPosSemiDefKernel
      (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2) := by
  exact productKernel_posSemiDef_imported Kx Ky hKx hKy

/-- The joint Neumann wristband kernel is PSD.
    Follows from: angular is PSD + Neumann radial is PSD + product is PSD. -/
theorem wristbandKernelNeumann_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (wristbandKernelNeumann (d := d) β α) := by
  have hAng : IsPosSemiDefKernel (kernelAngChordal (d := d) β α) :=
    kernelAngChordal_posSemiDef d β α hβ hα
  have hRad : IsPosSemiDefKernel (kernelRadNeumann β) :=
    kernelRadNeumann_posSemiDef β hβ
  simpa [wristbandKernelNeumann] using
    (productKernel_posSemiDef
      (Kx := kernelAngChordal (d := d) β α)
      (Ky := kernelRadNeumann β)
      hAng hRad)

/-! ### Constant potential of the joint kernel

The potential of a product kernel under a product measure factors:
`h(u,t) = h_ang(u) · h_rad(t)`. This combines with constant-potential
facts for angular and radial factors to yield constancy of the joint
Neumann kernel.
-/

/-- Potential of a product kernel under a product measure factors
    as the product of the component potentials:
    `E_{(u',t')~μ⊗ν}[Kx(u,u')·Ky(t,t')] = E_{u'~μ}[Kx(u,u')] · E_{t'~ν}[Ky(t,t')]`.
    This is Fubini's theorem applied to the product. -/
theorem productPotential_factors
    {X : Type*} {Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (μ : Distribution X) (ν : Distribution Y)
    (w : X × Y) :
    kernelPotential
      (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)
      (productLaw μ ν) w =
    kernelPotential Kx μ w.1 * kernelPotential Ky ν w.2 := by
  unfold kernelPotential productLaw
  simpa using
    (integral_prod_mul
      (μ := (μ : Measure X))
      (ν := (ν : Measure Y))
      (f := fun x : X => Kx w.1 x)
      (g := fun y : Y => Ky w.2 y))

/-- The joint Neumann kernel has constant potential under `μ₀`.
    Combines: angular constant potential + Neumann constant potential +
    product factorization. -/
theorem wristbandKernelNeumann_constantPotential
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    ∃ c : ℝ,
      HasConstantPotential
        (wristbandKernelNeumann (d := d) β α)
        (wristbandUniform d) c := by
  rcases angularPotential_constant d hDim β α hβ hα with ⟨cAng, hAngConst⟩
  rcases neumannPotential_constant β hβ with ⟨cRad, hRadConst⟩
  refine ⟨cAng * cRad, ?_⟩
  intro w
  have hFactor :=
    productPotential_factors
      (Kx := kernelAngChordal (d := d) β α)
      (Ky := kernelRadNeumann β)
      (μ := sphereUniform d)
      (ν := uniform01)
      w
  calc
    kernelPotential
        (wristbandKernelNeumann (d := d) β α)
        (wristbandUniform d) w
      = kernelPotential
          (fun (p q : Sphere d × UnitInterval) =>
            kernelAngChordal (d := d) β α p.1 q.1 *
              kernelRadNeumann β p.2 q.2)
          (productLaw (sphereUniform d) uniform01) w := by
            rfl
    _ = kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) w.1 *
          kernelPotential (kernelRadNeumann β) uniform01 w.2 := by
            simpa [wristbandUniform] using hFactor
    _ = cAng * cRad := by
          rw [hAngConst w.1, hRadConst w.2]

/-! ### Main theorem: energy uniquely minimized at uniform

This is **Hypothesis K** from the proof plan. -/

/-- **Hypothesis K (energy minimization).**
    The kernel energy `E(P) = E_{W,W'~P}[K(W,W')]` satisfies
    `E(P) ≥ E(μ₀)` for all distributions `P` on wristband space. -/
theorem kernelEnergy_minimized_at_uniform
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    kernelEnergy (wristbandKernelNeumann β α) P ≥
      kernelEnergy (wristbandKernelNeumann β α)
        (wristbandUniform d) := by
  rcases wristbandKernelNeumann_constantPotential d hDim β α hβ hα with ⟨c, hConst⟩
  have hEq :=
    energy_eq_mmdSq_of_constantPotential
      (K := wristbandKernelNeumann (d := d) β α)
      (μ₀ := wristbandUniform d)
      (c := c)
      hConst P
  have hMMD : 0 ≤ mmdSq (wristbandKernelNeumann (d := d) β α) P (wristbandUniform d) := by
    exact mmdSq_nonneg _ (wristbandKernelNeumann_posSemiDef d β α hβ hα) _ _
  have hDiff : 0 ≤ kernelEnergy (wristbandKernelNeumann (d := d) β α) P -
      kernelEnergy (wristbandKernelNeumann (d := d) β α) (wristbandUniform d) := by
    linarith [hEq, hMMD]
  linarith [hDiff]

/-- **Hypothesis K (uniqueness).**
    If `E(P) = E(μ₀)`, then `P = μ₀`. -/
theorem kernelEnergy_minimizer_unique
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hEq : kernelEnergy (wristbandKernelNeumann β α) P =
      kernelEnergy (wristbandKernelNeumann β α)
        (wristbandUniform d)) :
    P = wristbandUniform d := by
  rcases wristbandKernelNeumann_constantPotential d hDim β α hβ hα with ⟨c, hConst⟩
  have hMmdEq : mmdSq (wristbandKernelNeumann (d := d) β α) P (wristbandUniform d) = 0 := by
    have hEnergy :=
      energy_eq_mmdSq_of_constantPotential
        (K := wristbandKernelNeumann (d := d) β α)
        (μ₀ := wristbandUniform d)
        (c := c)
        hConst P
    linarith [hEq, hEnergy]
  exact (wristbandKernelNeumann_characteristic d hDim β α hβ hα)
    P (wristbandUniform d) hMmdEq

/-! ### 3-image truncation bound

The Python code uses the 3-image kernel, not the full Neumann series.
The difference is exponentially small in `β`. The leading omitted terms
are the `n = ±1` components of `(t - t' - 2n)`, which can be as small as
distance `1`, so the leading scale is `O(exp(-β))`. -/

/-- One Neumann image term from the shifted-difference family. -/
noncomputable def neumannDiffTerm
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) : ℝ :=
  Real.exp (-β * (((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2))

/-- One Neumann image term from the reflected-sum family. -/
noncomputable def neumannSumTerm
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) : ℝ :=
  Real.exp (-β * (((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2))

/-- The Neumann summand splits as shifted-difference + reflected-sum terms. -/
lemma kernelRadNeumannSummand_eq
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) :
    kernelRadNeumannSummand β t t' n =
      neumannDiffTerm β t t' n + neumannSumTerm β t t' n := by
  rfl

/-- The 3-image radial kernel equals the selected image terms `D₀ + S₀ + S₁`. -/
lemma kernelRad3Image_eq_selected
    (β : ℝ) (t t' : UnitInterval) :
    kernelRad3Image β t t' =
      neumannDiffTerm β t t' 0 +
      neumannSumTerm β t t' 0 +
      neumannSumTerm β t t' 1 := by
  simp [kernelRad3Image, neumannDiffTerm, neumannSumTerm]

/-- Decompose a `tsum` into finite selected terms plus the complement subtype sum. -/
lemma tsum_eq_sum_add_tsum_subtype_compl
    {β : Type*} (f : β → ℝ)
    (hf : Summable f) (s : Finset β) :
    (∑' b, f b) = (∑ i ∈ s, f i) + (∑' b : {b // b ∉ s}, f b) := by
  classical
  let a : ℝ := ∑' b : {b // b ∉ s}, f b
  have hSubSummable : Summable (fun b : {b // b ∉ s} => f b) := by
    simpa using (hf.subtype (s := {b | b ∉ s}))
  have hSubHas : HasSum (fun b : {b // b ∉ s} => f b) a := by
    exact hSubSummable.hasSum
  have hFull : HasSum f (a + ∑ i ∈ s, f i) :=
    (Finset.hasSum_compl_iff (f := f) (s := s)).1 hSubHas
  have hMain : (∑' b, f b) = a + ∑ i ∈ s, f i := by
    exact hf.hasSum.unique hFull
  linarith [hMain]

lemma neumannDiffTerm_nonneg
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) :
    0 ≤ neumannDiffTerm β t t' n := by
  exact Real.exp_nonneg _

lemma neumannSumTerm_nonneg
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) :
    0 ≤ neumannSumTerm β t t' n := by
  exact Real.exp_nonneg _

lemma neumannTerms_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    Summable (fun n : ℤ => neumannDiffTerm β t t' n + neumannSumTerm β t t' n) := by
  simpa [neumannDiffTerm, neumannSumTerm] using
    kernelRadNeumann_summable β hβ t t'

lemma neumannDiffTerm_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    Summable (fun n : ℤ => neumannDiffTerm β t t' n) := by
  exact Summable.of_nonneg_of_le
    (f := fun n : ℤ => neumannDiffTerm β t t' n + neumannSumTerm β t t' n)
    (g := fun n : ℤ => neumannDiffTerm β t t' n)
    (fun n => neumannDiffTerm_nonneg β t t' n)
    (fun n => le_add_of_nonneg_right (neumannSumTerm_nonneg β t t' n))
    (neumannTerms_summable β hβ t t')

lemma neumannSumTerm_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    Summable (fun n : ℤ => neumannSumTerm β t t' n) := by
  exact Summable.of_nonneg_of_le
    (f := fun n : ℤ => neumannDiffTerm β t t' n + neumannSumTerm β t t' n)
    (g := fun n : ℤ => neumannSumTerm β t t' n)
    (fun n => neumannSumTerm_nonneg β t t' n)
    (fun n => le_add_of_nonneg_left (neumannDiffTerm_nonneg β t t' n))
    (neumannTerms_summable β hβ t t')

lemma kernelRadNeumann_eq_tsum_diff_add_tsum_sum
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    kernelRadNeumann β t t' =
      (∑' n : ℤ, neumannDiffTerm β t t' n) +
      (∑' n : ℤ, neumannSumTerm β t t' n) := by
  have hDiff := neumannDiffTerm_summable β hβ t t'
  have hSum := neumannSumTerm_summable β hβ t t'
  calc
    kernelRadNeumann β t t' =
      ∑' n : ℤ, (neumannDiffTerm β t t' n + neumannSumTerm β t t' n) := by
        simp [kernelRadNeumann, neumannDiffTerm, neumannSumTerm]
    _ =
      (∑' n : ℤ, neumannDiffTerm β t t' n) +
      (∑' n : ℤ, neumannSumTerm β t t' n) := by
        exact Summable.tsum_add hDiff hSum

lemma unitInterval_sub_bounds (t t' : UnitInterval) :
    -1 ≤ (t : ℝ) - (t' : ℝ) ∧ (t : ℝ) - (t' : ℝ) ≤ 1 := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have ht0' : 0 ≤ (t' : ℝ) := t'.2.1
  have ht1' : (t' : ℝ) ≤ 1 := t'.2.2
  constructor <;> linarith

lemma unitInterval_add_bounds (t t' : UnitInterval) :
    0 ≤ (t : ℝ) + (t' : ℝ) ∧ (t : ℝ) + (t' : ℝ) ≤ 2 := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have ht0' : 0 ≤ (t' : ℝ) := t'.2.1
  have ht1' : (t' : ℝ) ≤ 1 := t'.2.2
  constructor <;> linarith

lemma neumannDiffTerm_pos_bound
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) (n : ℕ) :
    neumannDiffTerm β t t' (Int.ofNat (n + 1)) ≤
      Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
  let a : ℝ := (t : ℝ) - (t' : ℝ)
  have haL : -1 ≤ a := (unitInterval_sub_bounds t t').1
  have haU : a ≤ 1 := (unitInterval_sub_bounds t t').2
  have hAbs : (2 * n + 1 : ℝ) ≤ |a - 2 * (n + 1 : ℝ)| := by
    have hy : a - 2 * (n + 1 : ℝ) ≤ -(2 * n + 1 : ℝ) := by
      nlinarith
    have hy0 : a - 2 * (n + 1 : ℝ) ≤ 0 := by nlinarith [hy]
    have habs : |a - 2 * (n + 1 : ℝ)| = -(a - 2 * (n + 1 : ℝ)) := abs_of_nonpos hy0
    rw [habs]
    nlinarith [hy]
  have hSq : ((2 * n + 1 : ℝ) ^ 2) ≤ (a - 2 * (n + 1 : ℝ)) ^ 2 := by
    nlinarith [hAbs]
  have hSqLin : (1 + 4 * n : ℝ) ≤ (a - 2 * (n + 1 : ℝ)) ^ 2 := by
    have hPoly : (1 + 4 * n : ℝ) ≤ (2 * n + 1 : ℝ) ^ 2 := by
      nlinarith
    exact le_trans hPoly hSq
  have hExpArg : -β * (a - 2 * (n + 1 : ℝ)) ^ 2 ≤ -β * (1 + 4 * n : ℝ) := by
    nlinarith [hSqLin, hβ]
  have hExp : Real.exp (-β * (a - 2 * (n + 1 : ℝ)) ^ 2) ≤ Real.exp (-β * (1 + 4 * n : ℝ)) :=
    (Real.exp_le_exp).2 hExpArg
  have hR : Real.exp (-β * (1 + 4 * n : ℝ)) =
      Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
    calc
      Real.exp (-β * (1 + 4 * n : ℝ))
          = Real.exp (-β + ((n : ℝ) * (-4 * β))) := by
            ring
      _ = Real.exp (-β) * Real.exp ((n : ℝ) * (-4 * β)) := by
            rw [Real.exp_add]
      _ = Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
            rw [Real.exp_nat_mul]
  simpa [neumannDiffTerm, a, Int.ofNat_eq_natCast] using hExp.trans_eq hR

lemma neumannDiffTerm_negSucc_bound
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) (n : ℕ) :
    neumannDiffTerm β t t' (Int.negSucc n) ≤
      Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
  let a : ℝ := (t : ℝ) - (t' : ℝ)
  have haL : -1 ≤ a := (unitInterval_sub_bounds t t').1
  have haU : a ≤ 1 := (unitInterval_sub_bounds t t').2
  have hAbs : (2 * n + 1 : ℝ) ≤ |a + 2 * (n + 1 : ℝ)| := by
    have hy : (2 * n + 1 : ℝ) ≤ a + 2 * (n + 1 : ℝ) := by
      nlinarith
    have hy0 : 0 ≤ a + 2 * (n + 1 : ℝ) := by nlinarith [hy]
    have habs : |a + 2 * (n + 1 : ℝ)| = a + 2 * (n + 1 : ℝ) := abs_of_nonneg hy0
    rw [habs]
    exact hy
  have hSq : ((2 * n + 1 : ℝ) ^ 2) ≤ (a + 2 * (n + 1 : ℝ)) ^ 2 := by
    nlinarith [hAbs]
  have hSqLin : (1 + 4 * n : ℝ) ≤ (a + 2 * (n + 1 : ℝ)) ^ 2 := by
    have hPoly : (1 + 4 * n : ℝ) ≤ (2 * n + 1 : ℝ) ^ 2 := by
      nlinarith
    exact le_trans hPoly hSq
  have hExpArg : -β * (a + 2 * (n + 1 : ℝ)) ^ 2 ≤ -β * (1 + 4 * n : ℝ) := by
    nlinarith [hSqLin, hβ]
  have hExp : Real.exp (-β * (a + 2 * (n + 1 : ℝ)) ^ 2) ≤ Real.exp (-β * (1 + 4 * n : ℝ)) :=
    (Real.exp_le_exp).2 hExpArg
  have hR : Real.exp (-β * (1 + 4 * n : ℝ)) =
      Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
    calc
      Real.exp (-β * (1 + 4 * n : ℝ))
          = Real.exp (-β + ((n : ℝ) * (-4 * β))) := by
            ring
      _ = Real.exp (-β) * Real.exp ((n : ℝ) * (-4 * β)) := by
            rw [Real.exp_add]
      _ = Real.exp (-β) * (Real.exp (-4 * β)) ^ n := by
            rw [Real.exp_nat_mul]
  have hCast : ((Int.negSucc n : ℤ) : ℝ) = -(n + 1 : ℝ) := by
    simpa using (Int.cast_negSucc (R := ℝ) n)
  have hInner :
      ((t : ℝ) - (t' : ℝ) - 2 * ((Int.negSucc n : ℤ) : ℝ))
        = ((t : ℝ) - (t' : ℝ) + 2 * (n + 1 : ℝ)) := by
    calc
      ((t : ℝ) - (t' : ℝ) - 2 * ((Int.negSucc n : ℤ) : ℝ))
          = ((t : ℝ) - (t' : ℝ) - 2 * (-(n + 1 : ℝ))) := by simpa [hCast]
      _ = ((t : ℝ) - (t' : ℝ) + 2 * (n + 1 : ℝ)) := by ring
  rw [neumannDiffTerm, hInner]
  exact hExp.trans_eq hR

lemma neumannSumTerm_pos_tail_bound
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) (n : ℕ) :
    neumannSumTerm β t t' (Int.ofNat (n + 2)) ≤
      Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
  let b : ℝ := (t : ℝ) + (t' : ℝ)
  have hbL : 0 ≤ b := (unitInterval_add_bounds t t').1
  have hbU : b ≤ 2 := (unitInterval_add_bounds t t').2
  have hAbs : (2 * (n + 1) : ℝ) ≤ |b - 2 * (n + 2 : ℝ)| := by
    have hy : b - 2 * (n + 2 : ℝ) ≤ -(2 * (n + 1) : ℝ) := by nlinarith
    have hy0 : b - 2 * (n + 2 : ℝ) ≤ 0 := by nlinarith [hy]
    have habs : |b - 2 * (n + 2 : ℝ)| = -(b - 2 * (n + 2 : ℝ)) := abs_of_nonpos hy0
    rw [habs]
    nlinarith [hy]
  have hSq : ((2 * (n + 1) : ℝ) ^ 2) ≤ (b - 2 * (n + 2 : ℝ)) ^ 2 := by
    nlinarith [hAbs]
  have hExpArg : -β * (b - 2 * (n + 2 : ℝ)) ^ 2 ≤ -β * (4 * (n + 1 : ℝ)) := by
    have hLin : (4 * (n + 1 : ℝ)) ≤ (b - 2 * (n + 2 : ℝ)) ^ 2 := by
      nlinarith [hSq]
    nlinarith [hLin, hβ]
  have hExp :
      Real.exp (-β * (b - 2 * (n + 2 : ℝ)) ^ 2) ≤ Real.exp (-β * (4 * (n + 1 : ℝ))) :=
    (Real.exp_le_exp).2 hExpArg
  have hR : Real.exp (-β * (4 * (n + 1 : ℝ))) =
      Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
    calc
      Real.exp (-β * (4 * (n + 1 : ℝ)))
          = Real.exp ((-4 * β) + ((n : ℝ) * (-4 * β))) := by
            ring
      _ = Real.exp (-4 * β) * Real.exp ((n : ℝ) * (-4 * β)) := by
            rw [Real.exp_add]
      _ = Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
            rw [Real.exp_nat_mul]
  simpa [neumannSumTerm, b, Int.ofNat_eq_natCast] using hExp.trans_eq hR

lemma neumannSumTerm_negSucc_tail_bound
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) (n : ℕ) :
    neumannSumTerm β t t' (Int.negSucc n) ≤
      Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
  let b : ℝ := (t : ℝ) + (t' : ℝ)
  have hbL : 0 ≤ b := (unitInterval_add_bounds t t').1
  have hbU : b ≤ 2 := (unitInterval_add_bounds t t').2
  have hAbs : (2 * (n + 1) : ℝ) ≤ |b + 2 * (n + 1 : ℝ)| := by
    have hy : (2 * (n + 1) : ℝ) ≤ b + 2 * (n + 1 : ℝ) := by nlinarith
    have hy0 : 0 ≤ b + 2 * (n + 1 : ℝ) := by nlinarith [hy]
    have habs : |b + 2 * (n + 1 : ℝ)| = b + 2 * (n + 1 : ℝ) := abs_of_nonneg hy0
    rw [habs]
    exact hy
  have hSq : ((2 * (n + 1) : ℝ) ^ 2) ≤ (b + 2 * (n + 1 : ℝ)) ^ 2 := by
    nlinarith [hAbs]
  have hExpArg : -β * (b + 2 * (n + 1 : ℝ)) ^ 2 ≤ -β * (4 * (n + 1 : ℝ)) := by
    have hLin : (4 * (n + 1 : ℝ)) ≤ (b + 2 * (n + 1 : ℝ)) ^ 2 := by
      nlinarith [hSq]
    nlinarith [hLin, hβ]
  have hExp :
      Real.exp (-β * (b + 2 * (n + 1 : ℝ)) ^ 2) ≤ Real.exp (-β * (4 * (n + 1 : ℝ))) :=
    (Real.exp_le_exp).2 hExpArg
  have hR : Real.exp (-β * (4 * (n + 1 : ℝ))) =
      Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
    calc
      Real.exp (-β * (4 * (n + 1 : ℝ)))
          = Real.exp ((-4 * β) + ((n : ℝ) * (-4 * β))) := by
            ring
      _ = Real.exp (-4 * β) * Real.exp ((n : ℝ) * (-4 * β)) := by
            rw [Real.exp_add]
      _ = Real.exp (-4 * β) * (Real.exp (-4 * β)) ^ n := by
            rw [Real.exp_nat_mul]
  have hCast : ((Int.negSucc n : ℤ) : ℝ) = -(n + 1 : ℝ) := by
    simpa using (Int.cast_negSucc (R := ℝ) n)
  have hInner :
      ((t : ℝ) + (t' : ℝ) - 2 * ((Int.negSucc n : ℤ) : ℝ))
        = ((t : ℝ) + (t' : ℝ) + 2 * (n + 1 : ℝ)) := by
    calc
      ((t : ℝ) + (t' : ℝ) - 2 * ((Int.negSucc n : ℤ) : ℝ))
          = ((t : ℝ) + (t' : ℝ) - 2 * (-(n + 1 : ℝ))) := by simpa [hCast]
      _ = ((t : ℝ) + (t' : ℝ) + 2 * (n + 1 : ℝ)) := by ring
  rw [neumannSumTerm, hInner]
  exact hExp.trans_eq hR

lemma exp_neg4_mul_pos_lt_one (β : ℝ) (hβ : 0 < β) :
    Real.exp (-4 * β) < 1 := by
  have hneg : -4 * β < 0 := by nlinarith
  simpa using (Real.exp_lt_one_iff.mpr hneg)

lemma tsum_diff_pos_pnat_le
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    (∑' n : ℕ+, neumannDiffTerm β t t' (n : ℤ))
      ≤ Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
  let r : ℝ := Real.exp (-4 * β)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using exp_neg4_mul_pos_lt_one β hβ
  have hDiffSummableInt : Summable (fun n : ℤ => neumannDiffTerm β t t' n) :=
    neumannDiffTerm_summable β hβ t t'
  have hDiffSummableNat : Summable (fun n : ℕ => neumannDiffTerm β t t' (Int.ofNat n)) := by
    exact (summable_int_iff_summable_nat_and_neg.mp hDiffSummableInt).1
  have hDiffSummableNatShift :
      Summable (fun n : ℕ => neumannDiffTerm β t t' (Int.ofNat (n + 1))) := by
    exact (summable_nat_add_iff 1).2 hDiffSummableNat
  have hMajorSummable : Summable (fun n : ℕ => Real.exp (-β) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hPointwise :
      ∀ n : ℕ, neumannDiffTerm β t t' (Int.ofNat (n + 1)) ≤ Real.exp (-β) * r ^ n := by
    intro n
    simpa [r] using neumannDiffTerm_pos_bound β hβ t t' n
  have hNat :
      (∑' n : ℕ, neumannDiffTerm β t t' (Int.ofNat (n + 1)))
        ≤ ∑' n : ℕ, Real.exp (-β) * r ^ n :=
    Summable.tsum_le_tsum hPointwise hDiffSummableNatShift hMajorSummable
  have hGeom :
      (∑' n : ℕ, Real.exp (-β) * r ^ n)
        = Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
    calc
      (∑' n : ℕ, Real.exp (-β) * r ^ n)
          = Real.exp (-β) * (∑' n : ℕ, r ^ n) := by
              simpa using
                (Summable.tsum_mul_left (Real.exp (-β))
                  (summable_geometric_of_lt_one hr0 hr1))
      _ = Real.exp (-β) * ((1 - r)⁻¹) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
            simp [r, div_eq_mul_inv]
  have hPnatEq :
      (∑' n : ℕ+, neumannDiffTerm β t t' (n : ℤ))
        = ∑' n : ℕ, neumannDiffTerm β t t' (Int.ofNat (n + 1)) := by
    simpa [Int.ofNat_eq_natCast] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => neumannDiffTerm β t t' (n : ℤ)))
  rw [hPnatEq]
  exact hNat.trans_eq hGeom

lemma tsum_diff_neg_pnat_le
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    (∑' n : ℕ+, neumannDiffTerm β t t' (-(n : ℤ)))
      ≤ Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
  let r : ℝ := Real.exp (-4 * β)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using exp_neg4_mul_pos_lt_one β hβ
  have hDiffSummableInt : Summable (fun n : ℤ => neumannDiffTerm β t t' n) :=
    neumannDiffTerm_summable β hβ t t'
  have hDiffSummableNatNeg :
      Summable (fun n : ℕ => neumannDiffTerm β t t' (-(Int.ofNat n))) := by
    exact (summable_int_iff_summable_nat_and_neg.mp hDiffSummableInt).2
  have hDiffSummableNatNegShift :
      Summable (fun n : ℕ => neumannDiffTerm β t t' (-(Int.ofNat (n + 1)))) := by
    exact (summable_nat_add_iff 1).2 hDiffSummableNatNeg
  have hMajorSummable : Summable (fun n : ℕ => Real.exp (-β) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hPointwise :
      ∀ n : ℕ, neumannDiffTerm β t t' (-(Int.ofNat (n + 1))) ≤ Real.exp (-β) * r ^ n := by
    intro n
    convert (neumannDiffTerm_negSucc_bound β hβ t t' n) using 1
  have hNat :
      (∑' n : ℕ, neumannDiffTerm β t t' (-(Int.ofNat (n + 1))))
        ≤ ∑' n : ℕ, Real.exp (-β) * r ^ n :=
    Summable.tsum_le_tsum hPointwise hDiffSummableNatNegShift hMajorSummable
  have hGeom :
      (∑' n : ℕ, Real.exp (-β) * r ^ n)
        = Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
    calc
      (∑' n : ℕ, Real.exp (-β) * r ^ n)
          = Real.exp (-β) * (∑' n : ℕ, r ^ n) := by
              simpa using
                (Summable.tsum_mul_left (Real.exp (-β))
                  (summable_geometric_of_lt_one hr0 hr1))
      _ = Real.exp (-β) * ((1 - r)⁻¹) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Real.exp (-β) / (1 - Real.exp (-4 * β)) := by
            simp [r, div_eq_mul_inv]
  have hPnatEq :
      (∑' n : ℕ+, neumannDiffTerm β t t' (-(n : ℤ)))
        = ∑' n : ℕ, neumannDiffTerm β t t' (-(Int.ofNat (n + 1))) := by
    simpa [Int.ofNat_eq_natCast] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => neumannDiffTerm β t t' (-(n : ℤ))))
  rw [hPnatEq]
  exact hNat.trans_eq hGeom

lemma tsum_sum_pos_tail_nat_le
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    (∑' n : ℕ, neumannSumTerm β t t' (Int.ofNat (n + 2)))
      ≤ Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
  let r : ℝ := Real.exp (-4 * β)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using exp_neg4_mul_pos_lt_one β hβ
  have hSumSummableInt : Summable (fun n : ℤ => neumannSumTerm β t t' n) :=
    neumannSumTerm_summable β hβ t t'
  have hSumSummableNat : Summable (fun n : ℕ => neumannSumTerm β t t' (Int.ofNat n)) := by
    exact (summable_int_iff_summable_nat_and_neg.mp hSumSummableInt).1
  have hSumSummableNatShift2 :
      Summable (fun n : ℕ => neumannSumTerm β t t' (Int.ofNat (n + 2))) := by
    exact (summable_nat_add_iff 2).2 hSumSummableNat
  have hMajorSummable : Summable (fun n : ℕ => Real.exp (-4 * β) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hPointwise :
      ∀ n : ℕ, neumannSumTerm β t t' (Int.ofNat (n + 2)) ≤ Real.exp (-4 * β) * r ^ n := by
    intro n
    simpa [r] using neumannSumTerm_pos_tail_bound β hβ t t' n
  have hNat :
      (∑' n : ℕ, neumannSumTerm β t t' (Int.ofNat (n + 2)))
        ≤ ∑' n : ℕ, Real.exp (-4 * β) * r ^ n :=
    Summable.tsum_le_tsum hPointwise hSumSummableNatShift2 hMajorSummable
  have hGeom :
      (∑' n : ℕ, Real.exp (-4 * β) * r ^ n)
        = Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
    calc
      (∑' n : ℕ, Real.exp (-4 * β) * r ^ n)
          = Real.exp (-4 * β) * (∑' n : ℕ, r ^ n) := by
              simpa using
                (Summable.tsum_mul_left (Real.exp (-4 * β))
                  (summable_geometric_of_lt_one hr0 hr1))
      _ = Real.exp (-4 * β) * ((1 - r)⁻¹) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
            simp [r, div_eq_mul_inv]
  exact hNat.trans_eq hGeom

lemma tsum_sum_neg_tail_nat_le
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    (∑' n : ℕ, neumannSumTerm β t t' (Int.negSucc n))
      ≤ Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
  let r : ℝ := Real.exp (-4 * β)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.exp_nonneg _
  have hr1 : r < 1 := by
    simpa [r] using exp_neg4_mul_pos_lt_one β hβ
  have hSumSummableInt : Summable (fun n : ℤ => neumannSumTerm β t t' n) :=
    neumannSumTerm_summable β hβ t t'
  have hSumSummableNatNeg :
      Summable (fun n : ℕ => neumannSumTerm β t t' (-(Int.ofNat n))) := by
    exact (summable_int_iff_summable_nat_and_neg.mp hSumSummableInt).2
  have hSumSummableNatNegShift :
      Summable (fun n : ℕ => neumannSumTerm β t t' (-(Int.ofNat (n + 1)))) := by
    exact (summable_nat_add_iff 1).2 hSumSummableNatNeg
  have hNegSuccSummable :
      Summable (fun n : ℕ => neumannSumTerm β t t' (Int.negSucc n)) := by
    refine hSumSummableNatNegShift.congr ?_
    intro n
    simp [Int.negSucc_eq]
  have hMajorSummable : Summable (fun n : ℕ => Real.exp (-4 * β) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hPointwise :
      ∀ n : ℕ, neumannSumTerm β t t' (Int.negSucc n) ≤ Real.exp (-4 * β) * r ^ n := by
    intro n
    simpa [r] using neumannSumTerm_negSucc_tail_bound β hβ t t' n
  have hNat :
      (∑' n : ℕ, neumannSumTerm β t t' (Int.negSucc n))
        ≤ ∑' n : ℕ, Real.exp (-4 * β) * r ^ n :=
    Summable.tsum_le_tsum hPointwise hNegSuccSummable hMajorSummable
  have hGeom :
      (∑' n : ℕ, Real.exp (-4 * β) * r ^ n)
        = Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
    calc
      (∑' n : ℕ, Real.exp (-4 * β) * r ^ n)
          = Real.exp (-4 * β) * (∑' n : ℕ, r ^ n) := by
              simpa using
                (Summable.tsum_mul_left (Real.exp (-4 * β))
                  (summable_geometric_of_lt_one hr0 hr1))
      _ = Real.exp (-4 * β) * ((1 - r)⁻¹) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
            simp [r, div_eq_mul_inv]
  exact hNat.trans_eq hGeom

/-- Uniform pointwise truncation bound between the 3-image radial kernel and
the full Neumann series.

Leading order is `exp(-β)` (not `exp(-4β)`), due to the omitted
`n = ±1` shifted-difference terms. -/
noncomputable def threeImageNeumannErrorBound (β : ℝ) : ℝ :=
  2 * (Real.exp (-β) + Real.exp (-4 * β)) / (1 - Real.exp (-4 * β))

lemma threeImageNeumannErrorBound_nonneg
    (β : ℝ) (hβ : 0 < β) :
    0 ≤ threeImageNeumannErrorBound β := by
  have hden : 0 < 1 - Real.exp (-4 * β) := by
    have hneg : -4 * β < 0 := by nlinarith
    have hexp : Real.exp (-4 * β) < 1 := by
      simpa using (Real.exp_lt_one_iff.mpr hneg)
    linarith
  have hnum : 0 ≤ 2 * (Real.exp (-β) + Real.exp (-4 * β)) := by
    positivity
  exact div_nonneg hnum (le_of_lt hden)

/-- The 3-image kernel is within `threeImageNeumannErrorBound β` of the
Neumann kernel pointwise. -/
theorem threeImage_approx_neumann
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    |kernelRad3Image β t t' - kernelRadNeumann β t t'| ≤
      threeImageNeumannErrorBound β := by
  let D : ℤ → ℝ := fun n => neumannDiffTerm β t t' n
  let S : ℤ → ℝ := fun n => neumannSumTerm β t t' n
  let Dp : ℝ := ∑' n : ℕ, D (Int.ofNat (n + 1))
  let Dn : ℝ := ∑' n : ℕ, D (-(Int.ofNat (n + 1)))
  let Sp2 : ℝ := ∑' n : ℕ, S (Int.ofNat (n + 2))
  let Sn : ℝ := ∑' n : ℕ, S (Int.negSucc n)

  have hDsum : Summable D := by
    simpa [D] using neumannDiffTerm_summable β hβ t t'
  have hSsum : Summable S := by
    simpa [S] using neumannSumTerm_summable β hβ t t'

  have hDdecomp : (∑' n : ℤ, D n) = Dp + D 0 + Dn := by
    have h :=
      tsum_of_add_one_of_neg_add_one
        (f := D)
        ((summable_nat_add_iff 1).2 ((summable_int_iff_summable_nat_and_neg.mp hDsum).1))
        ((summable_nat_add_iff 1).2 ((summable_int_iff_summable_nat_and_neg.mp hDsum).2))
    simpa [D, Dp, Dn, Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using h

  have hSdecompRaw :
      (∑' n : ℤ, S n) =
        (∑' n : ℕ, S (Int.ofNat (n + 1))) + S 0 +
          (∑' n : ℕ, S (-(Int.ofNat (n + 1)))) := by
    have h :=
      tsum_of_add_one_of_neg_add_one
        (f := S)
        ((summable_nat_add_iff 1).2 ((summable_int_iff_summable_nat_and_neg.mp hSsum).1))
        ((summable_nat_add_iff 1).2 ((summable_int_iff_summable_nat_and_neg.mp hSsum).2))
    simpa [S, Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using h

  have hSnEq : (∑' n : ℕ, S (-(Int.ofNat (n + 1)))) = Sn := by
    simpa [Sn, Int.negSucc_eq, Int.ofNat_eq_natCast]

  have hSdecomp1 : (∑' n : ℤ, S n) = (∑' n : ℕ, S (Int.ofNat (n + 1))) + S 0 + Sn := by
    calc
      (∑' n : ℤ, S n)
          = (∑' n : ℕ, S (Int.ofNat (n + 1))) + S 0 + (∑' n : ℕ, S (-(Int.ofNat (n + 1)))) :=
            hSdecompRaw
      _ = (∑' n : ℕ, S (Int.ofNat (n + 1))) + S 0 + Sn := by rw [hSnEq]

  have hSshiftSummable : Summable (fun n : ℕ => S (Int.ofNat (n + 1))) := by
    exact (summable_nat_add_iff 1).2 ((summable_int_iff_summable_nat_and_neg.mp hSsum).1)

  have hSposSplit : (∑' n : ℕ, S (Int.ofNat (n + 1))) = S 1 + Sp2 := by
    have h := Summable.tsum_eq_zero_add hSshiftSummable
    simpa [Sp2, Int.ofNat_eq_natCast, add_assoc, add_left_comm, add_comm] using h

  have hSdecomp : (∑' n : ℤ, S n) = S 0 + S 1 + Sp2 + Sn := by
    calc
      (∑' n : ℤ, S n)
          = (∑' n : ℕ, S (Int.ofNat (n + 1))) + S 0 + Sn := hSdecomp1
      _ = (S 1 + Sp2) + S 0 + Sn := by rw [hSposSplit]
      _ = S 0 + S 1 + Sp2 + Sn := by ring

  have hK3 : kernelRad3Image β t t' = D 0 + S 0 + S 1 := by
    simpa [D, S, add_assoc, add_left_comm, add_comm] using
      kernelRad3Image_eq_selected β t t'

  have hKN : kernelRadNeumann β t t' = (∑' n : ℤ, D n) + (∑' n : ℤ, S n) := by
    simpa [D, S] using kernelRadNeumann_eq_tsum_diff_add_tsum_sum β hβ t t'

  have hExpr :
      kernelRad3Image β t t' - kernelRadNeumann β t t' = -(Dp + Dn + Sp2 + Sn) := by
    calc
      kernelRad3Image β t t' - kernelRadNeumann β t t'
          = (D 0 + S 0 + S 1) - ((∑' n : ℤ, D n) + (∑' n : ℤ, S n)) := by
              rw [hK3, hKN]
      _ = (D 0 + S 0 + S 1) - ((Dp + D 0 + Dn) + (S 0 + S 1 + Sp2 + Sn)) := by
              rw [hDdecomp, hSdecomp]
      _ = -(Dp + Dn + Sp2 + Sn) := by ring

  have hDp_nonneg : 0 ≤ Dp := by
    dsimp [Dp]
    exact tsum_nonneg (fun n => by simpa [D] using neumannDiffTerm_nonneg β t t' (Int.ofNat (n + 1)))
  have hDn_nonneg : 0 ≤ Dn := by
    dsimp [Dn]
    exact tsum_nonneg (fun n => by
      have := neumannDiffTerm_nonneg β t t' (-(Int.ofNat (n + 1)))
      simpa [D] using this)
  have hSp2_nonneg : 0 ≤ Sp2 := by
    dsimp [Sp2]
    exact tsum_nonneg (fun n => by
      simpa [S] using neumannSumTerm_nonneg β t t' (Int.ofNat (n + 2)))
  have hSn_nonneg : 0 ≤ Sn := by
    dsimp [Sn]
    exact tsum_nonneg (fun n => by
      simpa [S] using neumannSumTerm_nonneg β t t' (Int.negSucc n))

  have hAbs : |kernelRad3Image β t t' - kernelRadNeumann β t t'| = Dp + Dn + Sp2 + Sn := by
    rw [hExpr, abs_neg]
    exact abs_of_nonneg (by nlinarith [hDp_nonneg, hDn_nonneg, hSp2_nonneg, hSn_nonneg])

  have hDpEq : (∑' n : ℕ+, D (n : ℤ)) = Dp := by
    simpa [Dp, Int.ofNat_eq_natCast] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => D (n : ℤ)))
  have hDnEq : (∑' n : ℕ+, D (-(n : ℤ))) = Dn := by
    simpa [Dn, Int.ofNat_eq_natCast] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => D (-(n : ℤ))))

  let Cdiff : ℝ := Real.exp (-β) / (1 - Real.exp (-4 * β))
  let Csum : ℝ := Real.exp (-4 * β) / (1 - Real.exp (-4 * β))

  have hDp_le : Dp ≤ Cdiff := by
    calc
      Dp = ∑' n : ℕ+, D (n : ℤ) := hDpEq.symm
      _ ≤ Cdiff := by
        simpa [D, Cdiff] using tsum_diff_pos_pnat_le β hβ t t'
  have hDn_le : Dn ≤ Cdiff := by
    calc
      Dn = ∑' n : ℕ+, D (-(n : ℤ)) := hDnEq.symm
      _ ≤ Cdiff := by
        simpa [D, Cdiff] using tsum_diff_neg_pnat_le β hβ t t'
  have hSp2_le : Sp2 ≤ Csum := by
    simpa [S, Sp2, Csum] using tsum_sum_pos_tail_nat_le β hβ t t'
  have hSn_le : Sn ≤ Csum := by
    simpa [S, Sn, Csum] using tsum_sum_neg_tail_nat_le β hβ t t'

  have hTail_le : Dp + Dn + Sp2 + Sn ≤ Cdiff + Cdiff + Csum + Csum := by
    nlinarith [hDp_le, hDn_le, hSp2_le, hSn_le]

  have hden_ne : (1 - Real.exp (-4 * β)) ≠ 0 := by
    have hneg : -4 * β < 0 := by nlinarith
    have hexp : Real.exp (-4 * β) < 1 := by
      simpa using (Real.exp_lt_one_iff.mpr hneg)
    linarith

  have hConst : Cdiff + Cdiff + Csum + Csum = threeImageNeumannErrorBound β := by
    dsimp [Cdiff, Csum, threeImageNeumannErrorBound]
    field_simp [hden_ne]
    ring

  rw [hAbs]
  exact hTail_le.trans_eq hConst

/-- The 3-image kernel energy is close to the Neumann kernel energy. -/
theorem threeImage_energy_approx
    {d : ℕ} (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    |kernelEnergy (wristbandKernel β α) P -
     kernelEnergy (wristbandKernelNeumann β α) P| ≤
      threeImageNeumannErrorBound β := by
  /- Roadmap:
  1. Bound pointwise kernel error by radial error using `abs_kernelAngChordal_le_one`.
  2. Lift pointwise bound through double integral (`kernelEnergy`) by
  `norm_integral_le_integral_norm` / monotonicity.
  3. Plug in the pointwise bound from `threeImage_approx_neumann`
     with the corrected `exp(-β)`-scale truncation constant. -/
  sorry

end WristbandLossProofs
