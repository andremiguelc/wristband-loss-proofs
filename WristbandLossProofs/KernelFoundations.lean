import WristbandLossProofs.KernelPrimitives
import WristbandLossProofs.KernelImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Basic Properties (scaffold — proofs deferred)

These are straightforward consequences of the definitions.
-/

/-- The angular kernel is symmetric. -/
lemma kernelAngChordal_symmetric
    {d : ℕ} (β α : ℝ) (u u' : Sphere d) :
    kernelAngChordal β α u u' = kernelAngChordal β α u' u := by
  simp [kernelAngChordal, sphereInner, real_inner_comm]

/-- The 3-image radial kernel is symmetric. -/
lemma kernelRad3Image_symmetric
    (β : ℝ) (t t' : UnitInterval) :
    kernelRad3Image β t t' = kernelRad3Image β t' t := by
  unfold kernelRad3Image
  ring_nf

/-- The angular kernel takes values in `[0, 1]` for `β·α² ≥ 0`. -/
lemma kernelAngChordal_nonneg
    {d : ℕ} (β α : ℝ) (_hβα : 0 ≤ β * α ^ 2)
    (u u' : Sphere d) :
    0 ≤ kernelAngChordal β α u u' := by
  simpa [kernelAngChordal] using
    (Real.exp_nonneg (2 * β * α ^ 2 * (sphereInner u u' - 1)))

/-- Inner product of unit sphere points is at most `1`. -/
lemma sphereInner_le_one
    {d : ℕ} (u u' : Sphere d) :
    sphereInner u u' ≤ 1 := by
  unfold sphereInner
  calc
    @inner ℝ (Vec d) _ u.1 u'.1 ≤ ‖u.1‖ * ‖u'.1‖ := by
      exact real_inner_le_norm _ _
    _ = 1 := by simp

/-- For positive parameters, angular kernel is bounded above by `1`. -/
lemma kernelAngChordal_le_one
    {d : ℕ} (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (u u' : Sphere d) :
    kernelAngChordal β α u u' ≤ 1 := by
  have hFac : 0 ≤ 2 * β * α ^ 2 := by positivity
  have hSub : sphereInner u u' - 1 ≤ 0 := sub_nonpos.mpr (sphereInner_le_one u u')
  have hExpArg : 2 * β * α ^ 2 * (sphereInner u u' - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hFac hSub
  have : Real.exp (2 * β * α ^ 2 * (sphereInner u u' - 1)) ≤ 1 :=
    (Real.exp_le_one_iff).2 hExpArg
  simpa [kernelAngChordal] using this

/-- For positive parameters, absolute angular kernel is bounded by `1`. -/
lemma abs_kernelAngChordal_le_one
    {d : ℕ} (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (u u' : Sphere d) :
    |kernelAngChordal β α u u'| ≤ 1 := by
  have hnonneg : 0 ≤ kernelAngChordal β α u u' := by
    simpa [kernelAngChordal] using
      (Real.exp_nonneg (2 * β * α ^ 2 * (sphereInner u u' - 1)))
  simpa [abs_of_nonneg hnonneg] using kernelAngChordal_le_one β α hβ hα u u'

/-- The 3-image radial kernel is nonneg (sum of exponentials). -/
lemma kernelRad3Image_nonneg
    (β : ℝ) (t t' : UnitInterval) :
    0 ≤ kernelRad3Image β t t' := by
  unfold kernelRad3Image
  positivity

/-- Measurability of the angular kernel (fixed parameters). -/
lemma measurable_kernelAngChordal
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Sphere d × Sphere d =>
      kernelAngChordal β α p.1 p.2) := by
  unfold kernelAngChordal sphereInner
  have hInner : Measurable (fun p : Sphere d × Sphere d => @inner ℝ (Vec d) _ p.1.1 p.2.1) := by
    exact (continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd) |>.measurable
  exact (Real.continuous_exp.measurable.comp
    ((measurable_const.mul measurable_const).mul (hInner.sub measurable_const)))

/-- Measurability of the 3-image radial kernel (fixed β). -/
lemma measurable_kernelRad3Image
    (β : ℝ) :
    Measurable (fun p : UnitInterval × UnitInterval =>
      kernelRad3Image β p.1 p.2) := by
  let s : UnitInterval × UnitInterval → ℝ := fun p => (p.1 : ℝ)
  let s' : UnitInterval × UnitInterval → ℝ := fun p => (p.2 : ℝ)
  have hs : Measurable s := by
    simpa [s] using (continuous_subtype_val.comp continuous_fst).measurable
  have hs' : Measurable s' := by
    simpa [s'] using (continuous_subtype_val.comp continuous_snd).measurable
  have h1 : Measurable (fun p => Real.exp (-(β * (s p - s' p) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul ((hs.sub hs').pow_const 2)).neg)
  have h2 : Measurable (fun p => Real.exp (-(β * (s p + s' p) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul ((hs.add hs').pow_const 2)).neg)
  have h3 : Measurable (fun p => Real.exp (-(β * (s p + s' p - 2) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul (((hs.add hs').sub measurable_const).pow_const 2)).neg)
  simpa [kernelRad3Image, s, s', add_assoc] using h1.add (h2.add h3)

/-- Measurability of the joint wristband kernel. -/
lemma measurable_wristbandKernel
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Wristband d × Wristband d =>
      wristbandKernel β α p.1 p.2) := by
  let gAng : Wristband d × Wristband d → Sphere d × Sphere d :=
    fun p => (p.1.1, p.2.1)
  let gRad : Wristband d × Wristband d → UnitInterval × UnitInterval :=
    fun p => (p.1.2, p.2.2)
  have hgAng : Measurable gAng := by
    exact measurable_fst.fst.prodMk measurable_snd.fst
  have hgRad : Measurable gRad := by
    exact measurable_fst.snd.prodMk measurable_snd.snd
  have hAngW : Measurable (fun p : Wristband d × Wristband d => kernelAngChordal β α p.1.1 p.2.1) := by
    simpa [gAng] using (measurable_kernelAngChordal (d := d) β α).comp hgAng
  have hRadW : Measurable (fun p : Wristband d × Wristband d => kernelRad3Image β p.1.2 p.2.2) := by
    simpa [gRad] using (measurable_kernelRad3Image β).comp hgRad
  simpa [wristbandKernel] using hAngW.mul hRadW

/-- Measurability of the Neumann wristband kernel. -/
lemma measurable_wristbandKernelNeumann
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Wristband d × Wristband d =>
      wristbandKernelNeumann β α p.1 p.2) := by
  /- Roadmap:
  1. Build `measurable_kernelRadNeumann` in the radial pair variable, likely from
     `kernelRadNeumann_eq_tsum_summand` plus measurability of each summand.
  2. Reuse the same product-map composition pattern as `measurable_wristbandKernel`.
  3. If needed, split on `0 < β` vs `β ≤ 0` to avoid summability edge cases. -/
  sorry

/-- When the potential is constant, the energy-MMD identity holds:
    `E(P) - E(μ₀) = MMD²(P, μ₀)`. -/
theorem energy_eq_mmdSq_of_constantPotential
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (μ₀ : Distribution X) (c : ℝ)
    (hConst : HasConstantPotential K μ₀ c)
    (P : Distribution X) :
    kernelEnergy K P - kernelEnergy K μ₀ = mmdSq K P μ₀ := by
  have hCross :
      (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X)) = c := by
    calc
      (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X))
          = ∫ w, kernelPotential K μ₀ w ∂(P : Measure X) := by rfl
      _ = ∫ w, c ∂(P : Measure X) := by
            refine integral_congr_ae ?_
            filter_upwards with w
            exact hConst w
      _ = c := by simp
  have hEnergyμ₀ : kernelEnergy K μ₀ = c := by
    calc
      kernelEnergy K μ₀ = ∫ w, kernelPotential K μ₀ w ∂(μ₀ : Measure X) := by rfl
      _ = ∫ w, c ∂(μ₀ : Measure X) := by
            refine integral_congr_ae ?_
            filter_upwards with w
            exact hConst w
      _ = c := by simp
  calc
    kernelEnergy K P - kernelEnergy K μ₀
        = kernelEnergy K P - c := by simp [hEnergyμ₀]
    _ = kernelEnergy K P - 2 * c + c := by ring
    _ = kernelEnergy K P -
          2 * (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X)) +
          kernelEnergy K μ₀ := by simp [hCross, hEnergyμ₀]
    _ = mmdSq K P μ₀ := by rfl

/-! ## Kernel-Theory Scaffolding -/

/-- One `n`-mode summand in the Neumann reflection series. -/
noncomputable def kernelRadNeumannSummand
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) : ℝ :=
  Real.exp (-β * (((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2)) +
  Real.exp (-β * (((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2))

/-- The Neumann radial kernel is the `ℤ`-sum of reflection summands. -/
lemma kernelRadNeumann_eq_tsum_summand
    (β : ℝ) (t t' : UnitInterval) :
    kernelRadNeumann β t t' = ∑' n : ℤ, kernelRadNeumannSummand β t t' n := by
  rfl

/-- For `β > 0`, each fixed-point Neumann summand family is summable over `ℤ`. -/
lemma kernelRadNeumannSummand_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    Summable (fun n : ℤ => kernelRadNeumannSummand β t t' n) := by
  simpa [kernelRadNeumannSummand] using kernelRadNeumann_summable β hβ t t'

/-- Each reflection summand is nonnegative. -/
lemma kernelRadNeumannSummand_nonneg
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) :
    0 ≤ kernelRadNeumannSummand β t t' n := by
  positivity

/-- Absolute value of a reflection summand simplifies by nonnegativity. -/
lemma abs_kernelRadNeumannSummand
    (β : ℝ) (t t' : UnitInterval) (n : ℤ) :
    |kernelRadNeumannSummand β t t' n| = kernelRadNeumannSummand β t t' n := by
  exact abs_of_nonneg (kernelRadNeumannSummand_nonneg β t t' n)

/-- Measurability of a fixed-index Neumann reflection summand in the second argument. -/
lemma measurable_kernelRadNeumannSummand
    (β : ℝ) (t : UnitInterval) (n : ℤ) :
    Measurable (fun t' : UnitInterval => kernelRadNeumannSummand β t t' n) := by
  let s : UnitInterval → ℝ := fun t' => (t' : ℝ)
  have hs : Measurable s := by
    simpa [s] using continuous_subtype_val.measurable
  have h1 : Measurable (fun t' : UnitInterval =>
      Real.exp (-β * (((t : ℝ) - s t' - 2 * n) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul (((measurable_const.sub hs).sub measurable_const).pow_const 2))
        : Measurable (fun t' : UnitInterval => -β * (((t : ℝ) - s t' - 2 * n) ^ 2)))
  have h2 : Measurable (fun t' : UnitInterval =>
      Real.exp (-β * (((t : ℝ) + s t' - 2 * n) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul (((measurable_const.add hs).sub measurable_const).pow_const 2))
        : Measurable (fun t' : UnitInterval => -β * (((t : ℝ) + s t' - 2 * n) ^ 2)))
  simpa [kernelRadNeumannSummand, s] using h1.add h2

/-- A fixed-index Neumann summand is a.e. strongly measurable under `uniform01`. -/
lemma aestronglyMeasurable_kernelRadNeumannSummand
    (β : ℝ) (t : UnitInterval) (n : ℤ) :
    MeasureTheory.AEStronglyMeasurable
      (fun t' : UnitInterval => kernelRadNeumannSummand β t t' n)
      (uniform01 : MeasureTheory.Measure UnitInterval) := by
  exact (measurable_kernelRadNeumannSummand β t n).aestronglyMeasurable

/-- Rank-one kernels `K(x,y) = φ(x)φ(y)` are PSD. -/
lemma rankOneKernel_posSemiDef
    {X : Type*} (φ : X → ℝ) :
    IsPosSemiDefKernel (fun x y => φ x * φ y) := by
  intro n x c
  have hsq :
      (∑ i, ∑ j, c i * c j * (φ (x i) * φ (x j)))
        = (∑ i, c i * φ (x i)) ^ 2 := by
    calc
      (∑ i, ∑ j, c i * c j * (φ (x i) * φ (x j)))
          = (∑ i, c i * φ (x i)) * (∑ j, c j * φ (x j)) := by
              simp [Finset.mul_sum, mul_left_comm, mul_comm]
      _ = (∑ i, c i * φ (x i)) ^ 2 := by ring
  rw [hsq]
  nlinarith

/-- Sum of two PSD kernels is PSD. -/
lemma IsPosSemiDefKernel_add
    {X : Type*} {K₁ K₂ : X → X → ℝ}
    (h₁ : IsPosSemiDefKernel K₁)
    (h₂ : IsPosSemiDefKernel K₂) :
    IsPosSemiDefKernel (fun x y => K₁ x y + K₂ x y) := by
  intro n x c
  have h1 := h₁ n x c
  have h2 := h₂ n x c
  calc
    (∑ i, ∑ j, c i * c j * (K₁ (x i) (x j) + K₂ (x i) (x j)))
        = (∑ i, ∑ j, c i * c j * K₁ (x i) (x j)) +
          (∑ i, ∑ j, c i * c j * K₂ (x i) (x j)) := by
            simp [mul_add, Finset.sum_add_distrib]
    _ ≥ 0 := by linarith

/-- Nonnegative scalar multiples of PSD kernels are PSD. -/
lemma IsPosSemiDefKernel_const_mul
    {X : Type*} {K : X → X → ℝ} (a : ℝ) (ha : 0 ≤ a)
    (hK : IsPosSemiDefKernel K) :
    IsPosSemiDefKernel (fun x y => a * K x y) := by
  intro n x c
  have h := hK n x c
  calc
    (∑ i, ∑ j, c i * c j * (a * K (x i) (x j)))
        = a * (∑ i, ∑ j, c i * c j * K (x i) (x j)) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ ≥ 0 := by nlinarith

/-- Imported PSD fact wrapper for the Neumann radial kernel. -/
lemma kernelRadNeumann_posSemiDef
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β) := by
  exact kernelRadNeumann_posSemiDef_imported β hβ

/-- Dominated-convergence / `integral_tsum` scaffold for Neumann potential:
swap `∫` and `∑'` for the image-series representation. -/
lemma integral_tsum_kernelRadNeumann
    (β : ℝ) (hβ : 0 < β) (t : UnitInterval) :
    (∫ t' : UnitInterval,
      kernelRadNeumann β t t' ∂(uniform01 : Measure UnitInterval))
      =
    ∑' n : ℤ,
      ∫ t' : UnitInterval,
        (Real.exp (-β * (((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2)) +
         Real.exp (-β * (((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2)))
          ∂(uniform01 : Measure UnitInterval) := by
  /- Roadmap:
  1. Rewrite LHS with `kernelRadNeumann_eq_tsum_summand`.
  2. Apply `MeasureTheory.integral_tsum`.
  3. Discharge measurability via `aestronglyMeasurable_kernelRadNeumannSummand`.
  4. Prove `hf'` by an absolute-integrability tail bound over `n`. -/
  sorry

/-- Cosine mode orthogonality on `[0,1]` under uniform law:
`k ≥ 1` mode integrates to `0`. -/
lemma cosine_mode_integral_uniform01
    (k : ℕ) (hk : 0 < k) :
    ∫ t : UnitInterval,
      Real.cos ((k : ℝ) * Real.pi * (t : ℝ))
      ∂(uniform01 : Measure UnitInterval) = 0 := by
  let f : ℝ → ℝ := fun x => Real.cos ((k : ℝ) * Real.pi * x)
  have hSubtype :
      (∫ t : UnitInterval,
        Real.cos ((k : ℝ) * Real.pi * (t : ℝ))
        ∂(uniform01 : Measure UnitInterval))
        = ∫ x in Set.Icc (0 : ℝ) 1, f x ∂(volume : Measure ℝ) := by
    simpa [uniform01, UnitInterval, f] using
      (MeasureTheory.integral_subtype
        (s := Set.Icc (0 : ℝ) 1)
        (hs := measurableSet_Icc)
        (f := f))
  have hIccToInterval :
      (∫ x in Set.Icc (0 : ℝ) 1, f x ∂(volume : Measure ℝ)) =
        ∫ x in (0 : ℝ)..1, f x := by
    have hIccIoc :
        (∫ x in Set.Icc (0 : ℝ) 1, f x ∂(volume : Measure ℝ)) =
          ∫ x in Set.Ioc (0 : ℝ) 1, f x ∂(volume : Measure ℝ) := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := (volume : Measure ℝ))
          (f := f)
          (x := (0 : ℝ))
          (y := (1 : ℝ)))
    have hIntervalIoc :
        (∫ x in (0 : ℝ)..1, f x) =
          ∫ x in Set.Ioc (0 : ℝ) 1, f x ∂(volume : Measure ℝ) := by
      simpa using
        (intervalIntegral.integral_of_le
          (μ := (volume : Measure ℝ))
          (a := (0 : ℝ))
          (b := (1 : ℝ))
          (f := f)
          (by norm_num : (0 : ℝ) ≤ 1))
    exact hIccIoc.trans hIntervalIoc.symm
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc : (k : ℝ) * Real.pi ≠ 0 := mul_ne_zero hkReal Real.pi_ne_zero
  have hComp :
      (∫ x in (0 : ℝ)..1, f x)
        = ((k : ℝ) * Real.pi)⁻¹ •
          (∫ x in ((k : ℝ) * Real.pi * (0 : ℝ))..((k : ℝ) * Real.pi * (1 : ℝ)),
            Real.cos x) := by
    simpa [f, mul_assoc] using
      (intervalIntegral.integral_comp_mul_left
        (f := fun x : ℝ => Real.cos x)
        (a := (0 : ℝ))
        (b := (1 : ℝ))
        (c := (k : ℝ) * Real.pi)
        hc)
  have hCos :
      (∫ x in ((k : ℝ) * Real.pi * (0 : ℝ))..((k : ℝ) * Real.pi * (1 : ℝ)),
        Real.cos x) = 0 := by
    calc
      (∫ x in ((k : ℝ) * Real.pi * (0 : ℝ))..((k : ℝ) * Real.pi * (1 : ℝ)),
          Real.cos x)
          = Real.sin (((k : ℝ) * Real.pi) * (1 : ℝ)) -
              Real.sin (((k : ℝ) * Real.pi) * (0 : ℝ)) := by
              simpa using
                (integral_cos
                  (a := ((k : ℝ) * Real.pi * (0 : ℝ)))
                  (b := ((k : ℝ) * Real.pi * (1 : ℝ))))
      _ = 0 := by
            simp [Real.sin_nat_mul_pi]
  calc
    (∫ t : UnitInterval,
      Real.cos ((k : ℝ) * Real.pi * (t : ℝ))
      ∂(uniform01 : Measure UnitInterval))
        = ∫ x in Set.Icc (0 : ℝ) 1, f x ∂(volume : Measure ℝ) := hSubtype
    _ = ∫ x in (0 : ℝ)..1, f x := hIccToInterval
    _ = ((k : ℝ) * Real.pi)⁻¹ •
          (∫ x in ((k : ℝ) * Real.pi * (0 : ℝ))..((k : ℝ) * Real.pi * (1 : ℝ)),
            Real.cos x) := hComp
    _ = 0 := by simpa [hCos]

/-- Stone-Weierstrass / Fourier-density draft:
finite cosine sums approximate any continuous function on `[0,1]`. -/
lemma cosine_span_uniformly_dense_on_unitInterval
    (f : C(UnitInterval, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ coeff : Fin n → ℝ, ∃ freq : Fin n → ℕ,
      ∀ t : UnitInterval,
        |f t - ∑ i, coeff i * Real.cos ((freq i : ℝ) * Real.pi * (t : ℝ))| < ε := by
  /- Roadmap:
  1. Reduce to classical trigonometric polynomial density on `[0,1]`.
  2. Restrict to cosine basis using even-extension symmetry.
  3. Package coefficients/frequencies in `Fin n` data. -/
  sorry

/-- Rotational invariance of angular kernel under orthogonal actions on
sphere arguments. -/
lemma kernelAngChordal_rotationInvariant
    (d : ℕ) (β α : ℝ)
    (O : (Vec d) ≃ₗᵢ[ℝ] Vec d)
    (u u' : Sphere d) :
    kernelAngChordal (d := d) β α (rotateSphere O u) (rotateSphere O u') =
      kernelAngChordal (d := d) β α u u' := by
  unfold kernelAngChordal sphereInner rotateSphere
  simp [LinearIsometryEquiv.inner_map_map]

/-- Characteristicness of angular kernel (deferred local theorem). -/
theorem kernelAngChordal_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (kernelAngChordal (d := d) β α) := by
  exact universal_implies_characteristic _
    (kernelAngChordal_universal d hDim β α hβ hα)

/-- Characteristicness of Neumann radial kernel (deferred local theorem). -/
theorem kernelRadNeumann_characteristic
    (β : ℝ) (hβ : 0 < β) :
    IsCharacteristicKernel (kernelRadNeumann β) := by
  exact universal_implies_characteristic _
    (kernelRadNeumann_universal β hβ)

/-- Characteristicness of the wristband Neumann product kernel
(deferred local theorem). -/
theorem wristbandKernelNeumann_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (wristbandKernelNeumann (d := d) β α) := by
  have hAngU : IsUniversalKernel (kernelAngChordal (d := d) β α) :=
    kernelAngChordal_universal d hDim β α hβ hα
  have hRadU : IsUniversalKernel (kernelRadNeumann β) :=
    kernelRadNeumann_universal β hβ
  have hProdU : IsUniversalKernel
      (fun (p q : Sphere d × UnitInterval) =>
        kernelAngChordal (d := d) β α p.1 q.1 * kernelRadNeumann β p.2 q.2) :=
    productKernel_universal
      (Kx := kernelAngChordal (d := d) β α)
      (Ky := kernelRadNeumann β)
      hAngU hRadU
  simpa [wristbandKernelNeumann] using
    (universal_implies_characteristic
      (K := fun (p q : Sphere d × UnitInterval) =>
        kernelAngChordal (d := d) β α p.1 q.1 * kernelRadNeumann β p.2 q.2)
      hProdU)

/-- Angular potential is constant under spherical uniform law
(deferred local theorem). -/
theorem angularPotential_constant
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    ∃ c : ℝ,
      HasConstantPotential
        (kernelAngChordal (d := d) β α) (sphereUniform d) c := by
  have _hβ : 0 < β := hβ
  have _hα : 0 < α := hα
  have hRotatePotential :
      ∀ (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) (u : Sphere d),
        kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) (rotateSphere O u)
          = kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) u := by
    intro O u
    have hMapDistDist :
        pushforward (rotateSphere O) (sphereUniform d) (measurable_rotateSphere O) = sphereUniform d :=
      sphereUniform_rotationInvariant d O
    have hMapDist :
        Measure.map (rotateSphere O) (sphereUniform d : Measure (Sphere d))
          = (sphereUniform d : Measure (Sphere d)) := by
      simpa [pushforward] using
        congrArg (fun ν : Distribution (Sphere d) => (ν : Measure (Sphere d))) hMapDistDist
    let g : Sphere d → ℝ := fun v => kernelAngChordal (d := d) β α (rotateSphere O u) v
    have hgAEStrong :
        MeasureTheory.AEStronglyMeasurable g
          (Measure.map (rotateSphere O) (sphereUniform d : Measure (Sphere d))) := by
      have hgMeas : Measurable g := by
        have hPair : Measurable (fun v : Sphere d => (rotateSphere O u, v)) :=
          measurable_const.prodMk measurable_id
        simpa [g] using (measurable_kernelAngChordal (d := d) β α).comp hPair
      exact hgMeas.aestronglyMeasurable
    unfold kernelPotential
    calc
      (∫ v, kernelAngChordal (d := d) β α (rotateSphere O u) v ∂(sphereUniform d : Measure (Sphere d)))
          = ∫ v, g v ∂(Measure.map (rotateSphere O) (sphereUniform d : Measure (Sphere d))) := by
              simp [g, hMapDist]
      _ = ∫ v, g (rotateSphere O v) ∂(sphereUniform d : Measure (Sphere d)) := by
            simpa [g] using
              (MeasureTheory.integral_map
                (μ := (sphereUniform d : Measure (Sphere d)))
                (φ := rotateSphere O)
                (f := g)
                (hφ := (measurable_rotateSphere O).aemeasurable)
                (hfm := hgAEStrong))
      _ = ∫ v, kernelAngChordal (d := d) β α u v ∂(sphereUniform d : Measure (Sphere d)) := by
            refine integral_congr_ae ?_
            filter_upwards with v
            simpa [g] using kernelAngChordal_rotationInvariant d β α O u v
      _ = kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) u := by
            rfl
  have hAllEq :
      ∀ u v : Sphere d,
        kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) u
          = kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) v := by
    intro u v
    rcases orthogonal_group_transitive_on_sphere d hDim u v with ⟨O, hO⟩
    have hRot := hRotatePotential O u
    have hEqVU :
        kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) v
          = kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) u := by
      simpa [hO] using hRot
    exact hEqVU.symm
  classical
  by_cases hne : Nonempty (Sphere d)
  · rcases hne with ⟨u0⟩
    refine ⟨kernelPotential (kernelAngChordal (d := d) β α) (sphereUniform d) u0, ?_⟩
    intro w
    exact hAllEq w u0
  · refine ⟨0, ?_⟩
    intro w
    exact (hne ⟨w⟩).elim

/-- Imported constant-potential fact wrapper for the Neumann radial kernel. -/
theorem neumannPotential_constant
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ,
      HasConstantPotential (kernelRadNeumann β) uniform01 c := by
  exact neumannPotential_constant_imported β hβ

end WristbandLossProofs
