import WristbandLossProofs.Fourier.FourierLaw
import WristbandLossProofs.Poisson.PoissonSecondMoment

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## Fourier Foundations

Local derivations for the Fourier branch. They reach two conclusions.

The first is unbiasedness. `kernelAngChordal_eq_chordalGaussian` rewrites the
angular kernel in the chordal form the frequency law speaks about. Feed that into
`fourierFeature_law`, and `fourierAngularSampler` is unbiased.

The second is the set of side conditions. `AngularSampler` alone gives no
measurability and no moment, so the estimator theorems carry those as
hypotheses. Here they become theorems:

- `fourier_hasIntegrableDrawEnergy` — the draw kernel is integrable.
- `fourier_drawEnergy_memLp_two` — one draw's energy is square-integrable.
- `fourier_drawEnergy_variance_le` — one draw's energy has variance at most
  `4 · (sup k_rad)²`.

Every one of the three comes from `|fourierFeature ω u| ≤ √2` together with the
bound and the continuity of the radial factor. None of them reads the draw law.
So they hold for any law of the draw, and a change of law cannot break them. A
sampler whose feature has no bound has no counterpart to any of the three.

The variance bound is Popoviciu applied to a bounded quantity. It is not tight.
The true variance of one feature at the uniform target is near half the squared
energy, and it does not grow with the kernel scale; the bound below does grow,
because it uses only the extreme value the draw energy could take.
-/

/-! ### The sampler -/

/-- The sampler whose expected feature product is the angular kernel: the
frequency-and-phase law of `FourierLaw`, fed the kernel's own scale. -/
def fourierAngularSampler (d : ℕ) (β α : ℝ) (_hβ : 0 < β) :
    AngularSampler d (FourierDraw d) :=
  fourierFeatureSampler d (2 * β * α ^ 2)

lemma fourierAngularSampler_unbiased (d : ℕ) (β α : ℝ) (hβ : 0 < β) :
    IsUnbiasedFor (fourierAngularSampler d β α hβ)
      (kernelAngChordal (d := d) β α) := by
  intro u u'
  rw [kernelAngChordal_eq_chordalGaussian]
  exact fourierFeature_law d (2 * β * α ^ 2) (by positivity) u u'

/-! ### Joint continuity

The draw kernel is a product of two cosines and the radial factor. Each is
continuous in the draw and in the two points together, so the product is. That
gives the measurability side condition of the integrability lemma. -/

lemma continuous_fourierDrawKernel {d : ℕ} (β α : ℝ) (hβ : 0 < β) :
    Continuous (fun p : FourierDraw d × (Wristband d × Wristband d) =>
      drawWristbandKernel (fourierAngularSampler d β α hβ) β p.1 p.2.1 p.2.2) := by
  unfold drawWristbandKernel fourierAngularSampler fourierFeatureSampler fourierFeature
  simp only
  have h1 : Continuous (fun p : FourierDraw d × (Wristband d × Wristband d) =>
      Real.sqrt 2 * Real.cos (@inner ℝ (Vec d) _ p.1.1 p.2.1.1.1 + p.1.2)) := by fun_prop
  have h2 : Continuous (fun p : FourierDraw d × (Wristband d × Wristband d) =>
      Real.sqrt 2 * Real.cos (@inner ℝ (Vec d) _ p.1.1 p.2.2.1.1 + p.1.2)) := by fun_prop
  have h3 : Continuous (fun p : FourierDraw d × (Wristband d × Wristband d) =>
      kernelRadNeumann β p.2.1.2 p.2.2.2) :=
    (continuous_kernelRadNeumann β hβ).comp
      ((continuous_snd.fst.snd).prodMk (continuous_snd.snd.snd))
  exact (h1.mul h2).mul h3

lemma continuous_fourierFeatureSq {d : ℕ} (β α : ℝ) (hβ : 0 < β) :
    Continuous (fun p : FourierDraw d × Wristband d =>
      (fourierAngularSampler d β α hβ).feat p.1 p.2.1 ^ 2) := by
  unfold fourierAngularSampler fourierFeatureSampler fourierFeature
  simp only
  fun_prop

/-! ### The side conditions become theorems -/

/-- **The draw kernel is integrable, at every distribution.** The feature has a
bound, so it has a second moment without any hypothesis on the distribution. -/
lemma fourier_hasIntegrableDrawEnergy {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    HasIntegrableDrawEnergy (fourierAngularSampler d β α hβ) β P := by
  refine hasIntegrableDrawEnergy_of_sq _ β P (neumannSup β)
    (continuous_fourierDrawKernel β α hβ).aestronglyMeasurable ?_ ?_
  · intro t t'
    rw [abs_of_nonneg (kernelRadNeumann_nonneg β t t')]
    exact kernelRadNeumann_le_neumannSup β hβ t t'
  · refine Integrable.mono' (integrable_const 2)
      (continuous_fourierFeatureSq β α hβ).aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact fourierFeature_sq_le_two p.1 p.2.1

/-- One draw's energy stays inside a fixed interval, at every draw and at every
distribution. The interval reads the radial bound alone. -/
lemma fourier_drawEnergy_mem_Icc {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) (z : FourierDraw d) :
    drawEnergy (fourierAngularSampler d β α hβ) β P z
      ∈ Set.Icc (-(2 * neumannSup β)) (2 * neumannSup β) := by
  have hbound : ‖drawEnergy (fourierAngularSampler d β α hβ) β P z‖
      ≤ 2 * neumannSup β := by
    unfold drawEnergy
    have h := norm_integral_le_of_norm_le_const
      (μ := (P : Measure (Wristband d)).prod (P : Measure (Wristband d)))
      (f := fun q : Wristband d × Wristband d =>
        drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2)
      (C := 2 * neumannSup β) ?_
    · simpa using h
    · filter_upwards with q
      rw [Real.norm_eq_abs]
      show |fourierFeature z q.1.1 * fourierFeature z q.2.1
        * kernelRadNeumann β q.1.2 q.2.2| ≤ 2 * neumannSup β
      exact abs_featPair_mul_le (abs_fourierFeature_le z q.1.1)
        (abs_fourierFeature_le z q.2.1) (kernelRadNeumann_nonneg β q.1.2 q.2.2)
        (kernelRadNeumann_le_neumannSup β hβ q.1.2 q.2.2)
  rw [Real.norm_eq_abs, abs_le] at hbound
  exact ⟨hbound.1, hbound.2⟩

lemma fourier_drawEnergy_aestronglyMeasurable {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    AEStronglyMeasurable (drawEnergy (fourierAngularSampler d β α hβ) β P)
      ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d)) :=
  (Integrable.integral_prod_left
    (fourier_hasIntegrableDrawEnergy β α hβ P)).aestronglyMeasurable

/-- **One draw's energy is square-integrable, at every distribution.** -/
lemma fourier_drawEnergy_memLp_two {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    MemLp (drawEnergy (fourierAngularSampler d β α hβ) β P) 2
      ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d)) :=
  MemLp.of_bound (fourier_drawEnergy_aestronglyMeasurable β α hβ P) (2 * neumannSup β)
    (by
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_le]
      exact fourier_drawEnergy_mem_Icc β α hβ P z)

/-- **One draw's energy has variance at most `4 · (sup k_rad)²`.**

Popoviciu applied to the interval of `fourier_drawEnergy_mem_Icc`. The constant
reads the radial factor alone: it holds at every dimension, at every angular
scale and at every distribution. -/
theorem fourier_drawEnergy_variance_le {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    Var[drawEnergy (fourierAngularSampler d β α hβ) β P;
        ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d))]
      ≤ 4 * neumannSup β ^ 2 := by
  have h := variance_le_sq_of_bounded
    (μ := ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d)))
    (a := -(2 * neumannSup β)) (b := 2 * neumannSup β)
    (X := drawEnergy (fourierAngularSampler d β α hβ) β P)
    (by filter_upwards with z using fourier_drawEnergy_mem_Icc β α hβ P z)
    (fourier_drawEnergy_aestronglyMeasurable β α hβ P).aemeasurable
  refine h.trans (le_of_eq ?_)
  ring

/-! ### A constant the distribution can lower

`neumannSup β` is the largest value the radial factor takes anywhere on the unit
square. The draw energy never reaches it unless the distribution puts all its
radial mass where the factor is largest. `radialEnergy` replaces that extreme by
the mean the distribution actually produces, and the mean is what a batch
measures. The two differ by a factor of about eight at the working bandwidth, and
the variance constant is the square of that. -/

/-- The energy of the radial factor alone, read on the product measure. -/
def radialEnergy {d : ℕ} (β : ℝ) (P : Distribution (Wristband d)) : ℝ :=
  ∫ q, kernelRadNeumann β q.1.2 q.2.2
    ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))

lemma continuous_radialFactor {d : ℕ} (β : ℝ) (hβ : 0 < β) :
    Continuous (fun q : Wristband d × Wristband d =>
      kernelRadNeumann β q.1.2 q.2.2) :=
  (continuous_kernelRadNeumann β hβ).comp
    ((continuous_fst.snd).prodMk (continuous_snd.snd))

lemma integrable_radialFactor {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    Integrable (fun q : Wristband d × Wristband d => kernelRadNeumann β q.1.2 q.2.2)
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
  refine Integrable.mono' (integrable_const (neumannSup β))
    (continuous_radialFactor β hβ).aestronglyMeasurable ?_
  filter_upwards with q
  rw [Real.norm_eq_abs, abs_of_nonneg (kernelRadNeumann_nonneg β q.1.2 q.2.2)]
  exact kernelRadNeumann_le_neumannSup β hβ q.1.2 q.2.2

lemma radialEnergy_nonneg {d : ℕ} (β : ℝ) (P : Distribution (Wristband d)) :
    0 ≤ radialEnergy β P :=
  integral_nonneg fun q => kernelRadNeumann_nonneg β q.1.2 q.2.2

lemma continuous_drawKernel_at {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (z : FourierDraw d) :
    Continuous (fun q : Wristband d × Wristband d =>
      drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2) := by
  unfold drawWristbandKernel fourierAngularSampler fourierFeatureSampler fourierFeature
  simp only
  have h1 : Continuous (fun q : Wristband d × Wristband d =>
      Real.sqrt 2 * Real.cos (@inner ℝ (Vec d) _ z.1 q.1.1.1 + z.2)) := by fun_prop
  have h2 : Continuous (fun q : Wristband d × Wristband d =>
      Real.sqrt 2 * Real.cos (@inner ℝ (Vec d) _ z.1 q.2.1.1 + z.2)) := by fun_prop
  exact (h1.mul h2).mul (continuous_radialFactor β hβ)

lemma integrable_drawKernel_at {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) (z : FourierDraw d) :
    Integrable (fun q : Wristband d × Wristband d =>
      drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2)
      ((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
  refine Integrable.mono' ((integrable_radialFactor β hβ P).const_mul 2)
    (continuous_drawKernel_at β α hβ z).aestronglyMeasurable ?_
  filter_upwards with q
  rw [Real.norm_eq_abs]
  show |fourierFeature z q.1.1 * fourierFeature z q.2.1
    * kernelRadNeumann β q.1.2 q.2.2| ≤ 2 * kernelRadNeumann β q.1.2 q.2.2
  exact abs_featPair_mul_le (abs_fourierFeature_le z q.1.1)
    (abs_fourierFeature_le z q.2.1) (kernelRadNeumann_nonneg β q.1.2 q.2.2) le_rfl

/-- **One draw's energy stays inside twice the radial energy.** The angular
factor of one draw is a product of two cosines, so it never moves the radial
factor by more than two. -/
lemma fourier_drawEnergy_mem_Icc_radial {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) (z : FourierDraw d) :
    drawEnergy (fourierAngularSampler d β α hβ) β P z
      ∈ Set.Icc (-(2 * radialEnergy β P)) (2 * radialEnergy β P) := by
  have hbound : |drawEnergy (fourierAngularSampler d β α hβ) β P z|
      ≤ 2 * radialEnergy β P := by
    unfold drawEnergy radialEnergy
    calc |∫ q, drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2
            ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))|
        ≤ ∫ q, |drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2|
            ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (μ := (P : Measure (Wristband d)).prod (P : Measure (Wristband d)))
              (f := fun q : Wristband d × Wristband d =>
                drawWristbandKernel (fourierAngularSampler d β α hβ) β z q.1 q.2)
      _ ≤ ∫ q, 2 * kernelRadNeumann β q.1.2 q.2.2
            ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) := by
          refine integral_mono (integrable_drawKernel_at β α hβ P z).abs
            ((integrable_radialFactor β hβ P).const_mul 2) fun q => ?_
          show |fourierFeature z q.1.1 * fourierFeature z q.2.1
            * kernelRadNeumann β q.1.2 q.2.2| ≤ 2 * kernelRadNeumann β q.1.2 q.2.2
          exact abs_featPair_mul_le (abs_fourierFeature_le z q.1.1)
            (abs_fourierFeature_le z q.2.1)
            (kernelRadNeumann_nonneg β q.1.2 q.2.2) le_rfl
      _ = 2 * ∫ q, kernelRadNeumann β q.1.2 q.2.2
            ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d))) :=
          integral_const_mul _ _
  rw [abs_le] at hbound
  exact ⟨hbound.1, hbound.2⟩

/-- **One draw's energy has variance at most `4 · E_rad(P)²`.**

The same argument as `fourier_drawEnergy_variance_le`, with the mean of the
radial factor in place of its largest value. This constant is what a batch can
measure, and it is smaller. -/
theorem fourier_drawEnergy_variance_le_radial {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (P : Distribution (Wristband d)) :
    Var[drawEnergy (fourierAngularSampler d β α hβ) β P;
        ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d))]
      ≤ 4 * radialEnergy β P ^ 2 := by
  have h := variance_le_sq_of_bounded
    (μ := ((fourierAngularSampler d β α hβ).law : Measure (FourierDraw d)))
    (a := -(2 * radialEnergy β P)) (b := 2 * radialEnergy β P)
    (X := drawEnergy (fourierAngularSampler d β α hβ) β P)
    (by filter_upwards with z using fourier_drawEnergy_mem_Icc_radial β α hβ P z)
    (fourier_drawEnergy_aestronglyMeasurable β α hβ P).aemeasurable
  refine h.trans (le_of_eq ?_)
  ring

end WristbandLossProofs
