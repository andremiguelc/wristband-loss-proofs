import WristbandLossProofs.Poisson.PoissonMinimization

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Estimator

`sampledEnergy_eq_kernelEnergy` is about `sampledKernel`, the kernel obtained by
averaging the feature product over the draw law. Nothing is drawn there: the
average is taken before the energy.

What the loss computes is the other order. It draws `D` times, forms the
empirical average of the `D` feature products, and takes the energy of *that*
kernel. `realizedWristbandKernel` is that object, and it is random. The theorem
below says its energy is unbiased for the true energy:

  `∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P = kernelEnergy K P`

with `ω` ranging over `D` independent draws.

The two statements are different, and the difference is an exchange of
`∫ dP dP` with `∫` over the draws. That exchange is Fubini on
`(draw law)^D × (P ⊗ P)` and it needs an integrability hypothesis:
`HasIntegrableDrawEnergy`. The hypothesis is not decoration. Without it both
sides are defined — the Bochner integral returns zero off its domain — and they
need not agree.

`hasIntegrableDrawEnergy_of_sq` says what the hypothesis amounts to: a finite
second moment for the feature, a bounded radial factor, and joint measurability.
None of the three is supplied by `AngularSampler`, which carries no measurability
at all, so all three stay hypotheses here.

`kernelEnergy_featureForm` is separate and elementary. It says the energy of a
finite-rank kernel is a sum over features of a squared mean, with no sum over
pairs of points anywhere. That is the identity the implementation runs on.
-/

/-! ### The realized kernel -/

/-- The law of `D` independent draws from a sampler. -/
def drawLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : AngularSampler d Ω)
    (D : ℕ) : Distribution (Fin D → Ω) :=
  ⟨Measure.pi fun _ => (S.law : Measure Ω), inferInstance⟩

/-- The rank-one wristband kernel of a single draw. Its average over the draw
law is `wristbandKernelNeumann`; by itself it is not a kernel one would use, and
it is not positive semi-definite in any useful sense. -/
def drawWristbandKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) (z : Ω) (w w' : Wristband d) : ℝ :=
  S.feat z w.1 * S.feat z w'.1 * kernelRadNeumann β w.2 w'.2

/-- The angular kernel `D` draws actually produce: the empirical average of the
`D` feature products, not its expectation. -/
def realizedAngularKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) {D : ℕ} (ω : Fin D → Ω) (u u' : Sphere d) : ℝ :=
  (D : ℝ)⁻¹ * ∑ j : Fin D, S.feat (ω j) u * S.feat (ω j) u'

/-- The wristband kernel `D` draws produce. The radial factor is exact: only the
angular factor is sampled. -/
def realizedWristbandKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) {D : ℕ} (ω : Fin D → Ω)
    (w w' : Wristband d) : ℝ :=
  realizedAngularKernel S ω w.1 w'.1 * kernelRadNeumann β w.2 w'.2

/-- The hypothesis the exchange of integrals needs: one draw's kernel is
integrable on the joint space of a draw and a pair of points.

Three things are being asked at once. The map is jointly a.e.-strongly
measurable in the draw and the pair — `AngularSampler` requires no measurability
of `feat`, so this does not come for free. The feature product has a finite first
moment. And the radial factor does not spoil either. `hasIntegrableDrawEnergy_of_sq`
gives a sufficient condition in those terms. -/
def HasIntegrableDrawEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) (P : Distribution (Wristband d)) : Prop :=
  Integrable (fun p : Ω × (Wristband d × Wristband d) =>
      drawWristbandKernel S β p.1 p.2.1 p.2.2)
    ((S.law : Measure Ω).prod
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))))

/-! ### Energy as one integral over pairs

`kernelEnergy` is written as an iterated integral. Every exchange below happens
on the product, so this is the form to work in. -/

/-- The iterated integral defining `kernelEnergy` collapses to one integral over
`P ⊗ P` when the kernel is integrable there. -/
lemma kernelEnergy_eq_integral_prod {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (P : Distribution X)
    (hK : Integrable (fun q : X × X => K q.1 q.2)
      ((P : Measure X).prod (P : Measure X))) :
    kernelEnergy K P = ∫ q, K q.1 q.2 ∂((P : Measure X).prod (P : Measure X)) :=
  integral_integral hK

/-! ### The exchange -/

/-- The realized kernel is the average of the `D` single-draw kernels. The exact
radial factor distributes across the sum. -/
lemma realizedWristbandKernel_eq_average {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) {D : ℕ} (ω : Fin D → Ω)
    (w w' : Wristband d) :
    realizedWristbandKernel S β ω w w'
      = (D : ℝ)⁻¹ * ∑ j : Fin D, drawWristbandKernel S β (ω j) w w' := by
  simp only [realizedWristbandKernel, realizedAngularKernel, drawWristbandKernel]
  rw [mul_assoc, Finset.sum_mul]

/-- At a fixed draw vector, the realized energy is the average of the `D`
single-draw energies. This is the exchange of the finite sum with `∫ dP dP`, and
it needs each single-draw kernel to be integrable on `P ⊗ P`. -/
lemma realizedEnergy_eq_average {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) {D : ℕ} (ω : Fin D → Ω)
    (P : Distribution (Wristband d))
    (h : ∀ j : Fin D, Integrable (fun q : Wristband d × Wristband d =>
        drawWristbandKernel S β (ω j) q.1 q.2)
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))) :
    kernelEnergy (realizedWristbandKernel S β ω) P
      = (D : ℝ)⁻¹ * ∑ j : Fin D, ∫ q, drawWristbandKernel S β (ω j) q.1 q.2
          ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
  have hsum : Integrable (fun q : Wristband d × Wristband d =>
      realizedWristbandKernel S β ω q.1 q.2)
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
    have hav : Integrable (fun q : Wristband d × Wristband d =>
        (D : ℝ)⁻¹ * ∑ j : Fin D, drawWristbandKernel S β (ω j) q.1 q.2)
        ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) :=
      (integrable_finset_sum _ fun j _ => h j).const_mul _
    exact hav.congr (by filter_upwards with q using
      (realizedWristbandKernel_eq_average S β ω q.1 q.2).symm)
  rw [kernelEnergy_eq_integral_prod _ _ hsum]
  simp only [realizedWristbandKernel_eq_average]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => h j]

/-- Averaging a single draw's energy over the draw law gives the true energy.
This is the exchange of `∫ dP dP` with the draw integral, and unbiasedness is
what identifies the inner integral with the wristband kernel. -/
lemma drawEnergy_average_eq_kernelEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β α : ℝ)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P) :
    ∫ z, (∫ q, drawWristbandKernel S β z q.1 q.2
        ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d))))
        ∂(S.law : Measure Ω)
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  have hpt : ∀ q : Wristband d × Wristband d,
      ∫ z, drawWristbandKernel S β z q.1 q.2 ∂(S.law : Measure Ω)
        = wristbandKernelNeumann (d := d) β α q.1 q.2 := by
    intro q
    simp only [drawWristbandKernel]
    rw [integral_mul_const, wristbandKernelNeumann, ← hUnbiased q.1.1 q.2.1,
      sampledKernel]
  have hW : Integrable (fun q : Wristband d × Wristband d =>
      wristbandKernelNeumann (d := d) β α q.1 q.2)
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
    refine (Integrable.integral_prod_right hInt).congr ?_
    filter_upwards with q using hpt q
  have hInt' : Integrable (Function.uncurry
      (fun (z : Ω) (q : Wristband d × Wristband d) =>
        drawWristbandKernel S β z q.1 q.2))
      ((S.law : Measure Ω).prod
        ((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))) := hInt
  rw [integral_integral_swap hInt']
  simp only [hpt]
  exact (kernelEnergy_eq_integral_prod _ _ hW).symm

/-! ### Unbiasedness of the realized energy -/

/-- **The energy of the realized kernel is unbiased for the true energy.**

`sampledEnergy_eq_kernelEnergy` averages the feature product first and then takes
the energy. This averages the draws last, which is the order the loss computes
in. The two agree, and the proof is the exchange of the draw integral with
`∫ dP dP` — legitimate under `HasIntegrableDrawEnergy` and not otherwise.

The statement is about the mean over draws only. A single realization is a
finite-rank kernel with its own minimizer, which is elsewhere; that is why the
draw has to be refreshed each step. -/
theorem realizedEnergy_unbiased {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β α : ℝ) {D : ℕ} (hD : 0 < D)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P) :
    ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P
        ∂(drawLaw S D : Measure (Fin D → Ω))
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  set μ : Measure Ω := (S.law : Measure Ω) with hμ
  set PP : Measure (Wristband d × Wristband d) :=
    (P : Measure (Wristband d)).prod (P : Measure (Wristband d)) with hPP
  set g : Ω → ℝ := fun z => ∫ q, drawWristbandKernel S β z q.1 q.2 ∂PP with hg_def
  have hg : Integrable g μ := Integrable.integral_prod_left hInt
  have hmp : ∀ j : Fin D,
      MeasurePreserving (Function.eval j) (Measure.pi fun _ : Fin D => μ) μ :=
    fun j => measurePreserving_eval (fun _ : Fin D => μ) j
  have hae : ∀ᵐ z ∂μ, Integrable (fun q : Wristband d × Wristband d =>
      drawWristbandKernel S β z q.1 q.2) PP := Integrable.prod_right_ae hInt
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin D => μ), ∀ j : Fin D,
      Integrable (fun q : Wristband d × Wristband d =>
        drawWristbandKernel S β (ω j) q.1 q.2) PP :=
    ae_all_iff.mpr fun j => (hmp j).quasiMeasurePreserving.tendsto_ae.eventually hae
  have hgj : ∀ j : Fin D, Integrable (fun ω : Fin D → Ω => g (ω j))
      (Measure.pi fun _ : Fin D => μ) :=
    fun j => ((hmp j).integrable_comp hg.aestronglyMeasurable).mpr hg
  have heval : ∀ j : Fin D,
      ∫ ω, g (ω j) ∂(Measure.pi fun _ : Fin D => μ) = ∫ z, g z ∂μ := by
    intro j
    have hm := hmp j
    have hmap := integral_map (φ := Function.eval j)
      (μ := Measure.pi fun _ : Fin D => μ) hm.measurable.aemeasurable
      (f := g) (by rw [hm.map_eq]; exact hg.aestronglyMeasurable)
    rw [hm.map_eq] at hmap
    exact hmap.symm
  have hlaw : (drawLaw S D : Measure (Fin D → Ω))
      = Measure.pi fun _ : Fin D => μ := rfl
  rw [hlaw]
  have hpull : ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P
      ∂(Measure.pi fun _ : Fin D => μ)
      = ∫ ω, (D : ℝ)⁻¹ * ∑ j : Fin D, g (ω j) ∂(Measure.pi fun _ : Fin D => μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hall] with ω h using realizedEnergy_eq_average S β ω P h
  rw [hpull, integral_const_mul, integral_finset_sum _ fun j _ => hgj j]
  simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_mul]
  exact drawEnergy_average_eq_kernelEnergy S β α hUnbiased P hInt

/-- The Poisson mode sampler computes an unbiased estimate of the energy. -/
theorem poissonRealizedEnergy_unbiased (d : ℕ) (β α : ℝ) (hβ : 0 < β) {D : ℕ}
    (hD : 0 < D) (P : Distribution (Wristband d))
    (hInt : HasIntegrableDrawEnergy (poissonAngularSampler d β α hβ) β P) :
    ∫ ω, kernelEnergy
        (realizedWristbandKernel (poissonAngularSampler d β α hβ) β ω) P
        ∂(drawLaw (poissonAngularSampler d β α hβ) D
          : Measure (Fin D → RademacherDraw d))
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P :=
  realizedEnergy_unbiased _ β α hD (poissonAngularSampler_unbiased d β α hβ) P hInt

/-! ### What unbiasedness transfers

Minimization now reads on the estimator rather than on the kernel it estimates.
Both statements carry the integrability hypothesis twice, once at `P` and once
at the uniform measure. -/

/-- The expected realized energy is smallest at the uniform measure. -/
theorem realizedEnergy_minimized_at_uniform (d : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ)
    (hβ : 0 < β) (hα : 0 < α) {D : ℕ} (hD : 0 < D)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hIntP : HasIntegrableDrawEnergy S β P)
    (hIntU : HasIntegrableDrawEnergy S β (wristbandUniform d hDim1)) :
    ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P
        ∂(drawLaw S D : Measure (Fin D → Ω))
      ≥ ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) (wristbandUniform d hDim1)
        ∂(drawLaw S D : Measure (Fin D → Ω)) := by
  rw [realizedEnergy_unbiased S β α hD hUnbiased P hIntP,
    realizedEnergy_unbiased S β α hD hUnbiased _ hIntU]
  exact kernelEnergy_minimized_at_uniform d hDim β α hβ hα P (hDim1 := hDim1)

/-- The uniform measure is the only distribution at that minimum. -/
theorem realizedEnergy_minimizer_unique (d : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ)
    (hβ : 0 < β) (hα : 0 < α) {D : ℕ} (hD : 0 < D)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hIntP : HasIntegrableDrawEnergy S β P)
    (hIntU : HasIntegrableDrawEnergy S β (wristbandUniform d hDim1))
    (hEq : ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P
        ∂(drawLaw S D : Measure (Fin D → Ω))
      = ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) (wristbandUniform d hDim1)
        ∂(drawLaw S D : Measure (Fin D → Ω))) :
    P = wristbandUniform d hDim1 := by
  rw [realizedEnergy_unbiased S β α hD hUnbiased P hIntP,
    realizedEnergy_unbiased S β α hD hUnbiased _ hIntU] at hEq
  exact kernelEnergy_minimizer_unique d hDim β α hβ hα P (hDim1 := hDim1) (hEq := hEq)

/-! ### A sufficient condition for the hypothesis -/

/-- `HasIntegrableDrawEnergy` holds when the feature has a finite second moment,
the radial factor is bounded, and the draw kernel is jointly measurable.

The bound is `|ψ(u)ψ(u')k| ≤ (C/2)(ψ(u)² + ψ(u')²)`, so only a second moment is
needed and the two marginals of `P ⊗ P` each supply one.

The second moment is the quantity the sampler's variance is written in, and it is
finite for the Poisson sampler. The other two hypotheses are not proved here: the
radial bound is a theta-function estimate, and joint measurability of `feat` is
not part of `AngularSampler`. -/
lemma hasIntegrableDrawEnergy_of_sq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) (P : Distribution (Wristband d)) (C : ℝ)
    (hMeas : AEStronglyMeasurable (fun p : Ω × (Wristband d × Wristband d) =>
        drawWristbandKernel S β p.1 p.2.1 p.2.2)
      ((S.law : Measure Ω).prod
        ((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))))
    (hRad : ∀ t t' : UnitInterval, |kernelRadNeumann β t t'| ≤ C)
    (hSq : Integrable (fun p : Ω × Wristband d => S.feat p.1 p.2.1 ^ 2)
      ((S.law : Measure Ω).prod (P : Measure (Wristband d)))) :
    HasIntegrableDrawEnergy S β P := by
  have hC : 0 ≤ C :=
    le_trans (abs_nonneg _) (hRad ⟨0, by norm_num⟩ ⟨0, by norm_num⟩)
  have hfst : Integrable (fun p : Ω × (Wristband d × Wristband d) =>
      S.feat p.1 p.2.1.1 ^ 2)
      ((S.law : Measure Ω).prod
        ((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))) :=
    ((((MeasurePreserving.id (S.law : Measure Ω)).prod
      (measurePreserving_fst (μ := (P : Measure (Wristband d)))
        (ν := (P : Measure (Wristband d))))).integrable_comp
      hSq.aestronglyMeasurable).mpr hSq)
  have hsnd : Integrable (fun p : Ω × (Wristband d × Wristband d) =>
      S.feat p.1 p.2.2.1 ^ 2)
      ((S.law : Measure Ω).prod
        ((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))) :=
    ((((MeasurePreserving.id (S.law : Measure Ω)).prod
      (measurePreserving_snd (μ := (P : Measure (Wristband d)))
        (ν := (P : Measure (Wristband d))))).integrable_comp
      hSq.aestronglyMeasurable).mpr hSq)
  refine Integrable.mono' ((hfst.add hsnd).const_mul (C / 2)) hMeas ?_
  filter_upwards with p
  simp only [drawWristbandKernel, Pi.add_apply]
  have hk := hRad p.2.1.2 p.2.2.2
  set x := S.feat p.1 p.2.1.1
  set y := S.feat p.1 p.2.2.1
  set k := kernelRadNeumann β p.2.1.2 p.2.2.2
  have habs : ‖x * y * k‖ = |x| * |y| * |k| := by simp [Real.norm_eq_abs]
  rw [habs]
  have h1 : |x| * |y| * |k| ≤ |x| * |y| * C :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  refine h1.trans ?_
  have h2 : 2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  nlinarith [abs_nonneg x, abs_nonneg y, hC]

/-! ### Where the pairwise sum goes

The energy of a finite-rank kernel is a sum over features of a squared mean. No
sum over pairs of points survives, which is the whole reason the loss is linear
in the batch rather than quadratic.

Stated for the angular factor alone, and for a distribution on the sphere. The
radial factor is exact and carries its own finite basis; the joint version is the
product of the two lists, with the same algebra applied twice. -/

/-- The energy of the kernel `(1/D) ∑ⱼ ψⱼ(x) ψⱼ(x')` is `(1/D) ∑ⱼ (∫ψⱼ dP)²`. -/
theorem kernelEnergy_featureForm {X : Type*} [MeasurableSpace X] {D : ℕ}
    (ψ : Fin D → X → ℝ) (P : Distribution X)
    (hψ : ∀ j : Fin D, Integrable (ψ j) (P : Measure X)) :
    kernelEnergy (fun x x' => (D : ℝ)⁻¹ * ∑ j : Fin D, ψ j x * ψ j x') P
      = (D : ℝ)⁻¹ * ∑ j : Fin D, (∫ x, ψ j x ∂(P : Measure X)) ^ 2 := by
  have hinner : ∀ x : X,
      ∫ x', (D : ℝ)⁻¹ * ∑ j : Fin D, ψ j x * ψ j x' ∂(P : Measure X)
        = (D : ℝ)⁻¹ * ∑ j : Fin D, ψ j x * ∫ x', ψ j x' ∂(P : Measure X) := by
    intro x
    rw [integral_const_mul, integral_finset_sum _ fun j _ => (hψ j).const_mul (ψ j x)]
    simp only [integral_const_mul]
  simp only [kernelEnergy, hinner]
  rw [integral_const_mul, integral_finset_sum _ fun j _ => (hψ j).mul_const _]
  simp only [integral_mul_const, sq]

/-- The realized angular energy read off the drawn features: one mean per
feature, squared and averaged. -/
theorem realizedAngularEnergy_featureForm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) {D : ℕ} (ω : Fin D → Ω) (P : Distribution (Sphere d))
    (hFeat : ∀ j : Fin D,
      Integrable (fun u => S.feat (ω j) u) (P : Measure (Sphere d))) :
    kernelEnergy (realizedAngularKernel S ω) P
      = (D : ℝ)⁻¹ * ∑ j : Fin D,
          (∫ u, S.feat (ω j) u ∂(P : Measure (Sphere d))) ^ 2 :=
  kernelEnergy_featureForm (fun j u => S.feat (ω j) u) P hFeat

end WristbandLossProofs
