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

/-! ## Kernel-Theory Scaffolding (local/deferred proofs)

These are project-level targets intended to be proven in-repo. They are not
imported axioms.
-/

/-- PSD closure route for Neumann kernel from cosine expansion:
rank-1 PSD modes + nonnegative coefficients + convergent series. -/
lemma kernelRadNeumann_posSemiDef
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β) := by
  sorry

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
  sorry

/-- Cosine mode orthogonality on `[0,1]` under uniform law:
`k ≥ 1` mode integrates to `0`. -/
lemma cosine_mode_integral_uniform01
    (k : ℕ) (hk : 0 < k) :
    ∫ t : UnitInterval,
      Real.cos ((k : ℝ) * Real.pi * (t : ℝ))
      ∂(uniform01 : Measure UnitInterval) = 0 := by
  sorry

/-- Stone-Weierstrass / Fourier-density draft:
finite cosine sums approximate any continuous function on `[0,1]`. -/
lemma cosine_span_uniformly_dense_on_unitInterval
    (f : C(UnitInterval, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ coeff : Fin n → ℝ, ∃ freq : Fin n → ℕ,
      ∀ t : UnitInterval,
        |f t - ∑ i, coeff i * Real.cos ((freq i : ℝ) * Real.pi * (t : ℝ))| < ε := by
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
  sorry

/-- Neumann radial potential is constant under `uniform01`
(deferred local theorem). -/
theorem neumannPotential_constant
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ,
      HasConstantPotential (kernelRadNeumann β) uniform01 c := by
  sorry

end WristbandLossProofs
