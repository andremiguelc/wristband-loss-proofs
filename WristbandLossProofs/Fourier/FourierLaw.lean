import WristbandLossProofs.Fourier.FourierPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory ProbabilityTheory

/-! # Fourier Law

The law of one draw, built explicitly, and the identity that makes the sampler
unbiased. Nothing here is imported: the branch has no axioms of its own.

An explicit law is what lets an implementation be checked against the proof. The
frequency is a centred Gaussian with covariance `c I`, assembled one coordinate
at a time. The phase is uniform on one period. The draw is the pair.

References. The estimator is that of Rahimi, A.; Recht, B. (2007), "Random
Features for Large-Scale Kernel Machines", *NIPS* 2007, 1177-1184, which rests on
Bochner, S. (1933), "Monotone Funktionen, Stieltjessche Integrale und harmonische
Analyse", *Math. Ann.* 108, 378-410. The proof below follows neither source. It
computes the characteristic function of the coordinatewise Gaussian directly, so
the sources are an attribution and not a dependency.

Mathlib has no Gaussian measure above one dimension, and no cosine integral
against a Gaussian at any dimension. `gaussianVec`, `charFun_gaussianVec` and
`integral_cos_inner_gaussianVec` fill that gap and are of use beyond this branch.
-/

/-! ## The two marginals -/

/-- The centred Gaussian on `Vec d` with covariance `v I`, one coordinate at a
time. -/
def gaussianVec (d : ℕ) (v : NNReal) : Measure (Vec d) :=
  (Measure.pi fun _ : Fin d => gaussianReal 0 v).map (WithLp.toLp 2)

instance instIsProbabilityMeasureGaussianVec (d : ℕ) (v : NNReal) :
    IsProbabilityMeasure (gaussianVec d v) :=
  Measure.isProbabilityMeasure_map
    (WithLp.measurable_toLp 2 (Fin d → ℝ)).aemeasurable

/-- The uniform law on one period. -/
def phaseUniform : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • Measure.restrict volume (Set.Icc 0 (2 * Real.pi))

instance instIsProbabilityMeasurePhaseUniform : IsProbabilityMeasure phaseUniform := by
  constructor
  simp only [phaseUniform, Measure.coe_smul, Pi.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, Real.volume_Icc, sub_zero]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne' ENNReal.ofReal_ne_top

/-! ## The law of one draw -/

/-- The law of one draw: an independent frequency and phase. A negative `c`
clamps the covariance to zero, so the identity below asks for `0 ≤ c`. -/
def fourierFeatureLaw (d : ℕ) (c : ℝ) : Distribution (FourierDraw d) :=
  ⟨(gaussianVec d c.toNNReal).prod phaseUniform, inferInstance⟩

/-! ## The characteristic function of the frequency -/

/-- The characteristic function of `gaussianVec`. The coordinates are
independent, so the value is a product of one-dimensional values, and the
exponents add to the squared norm. -/
lemma charFun_gaussianVec {d : ℕ} (v : NNReal) (t : Vec d) :
    charFun (gaussianVec d v) t
      = ((Real.exp (-((v : ℝ) * ‖t‖ ^ 2) / 2) : ℝ) : ℂ) := by
  rw [gaussianVec, charFun_pi]
  have hterm : ∀ i : Fin d,
      charFun (gaussianReal 0 v) (t.ofLp i)
        = ((Real.exp (-((v : ℝ) * (t.ofLp i) ^ 2) / 2) : ℝ) : ℂ) := by
    intro i
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [hterm]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  have hshape : ∀ i : Fin d,
      -((v : ℝ) * (t.ofLp i) ^ 2) / 2 = (-((v : ℝ) / 2)) * (t.ofLp i) ^ 2 :=
    fun i => by ring
  simp only [hshape, ← Finset.mul_sum]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-- The real form of `charFun_gaussianVec`. The imaginary part cancels, because
the law is symmetric about the origin. -/
lemma integral_cos_inner_gaussianVec {d : ℕ} (v : NNReal) (t : Vec d) :
    ∫ w, Real.cos (inner ℝ w t) ∂(gaussianVec d v)
      = Real.exp (-((v : ℝ) * ‖t‖ ^ 2) / 2) := by
  have hint : Integrable
      (fun w : Vec d => Complex.exp ((inner ℝ w t : ℝ) * Complex.I))
      (gaussianVec d v) :=
    Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      (by filter_upwards with w; simp)
  have h := integral_re (𝕜 := ℂ) (μ := gaussianVec d v) hint
  rw [show (∫ w, Complex.exp ((inner ℝ w t : ℝ) * Complex.I) ∂(gaussianVec d v))
      = charFun (gaussianVec d v) t from rfl, charFun_gaussianVec] at h
  simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re,
    Complex.ofReal_re] using h

/-! ## What the phase removes -/

/-- A uniform phase averages a shifted cosine to zero, at any shift. The doubled
phase covers two periods, so the integral is still zero. This is the reason one
feature does the work that a cosine and a sine would do together. -/
lemma integral_cos_add_two_mul_phaseUniform (a : ℝ) :
    ∫ b, Real.cos (a + 2 * b) ∂phaseUniform = 0 := by
  rw [phaseUniform, integral_smul_measure]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_comp_add_mul (f := Real.cos) (by norm_num : (2 : ℝ) ≠ 0) a,
    integral_cos]
  rw [show a + 2 * (2 * Real.pi) = a + 2 * Real.pi + 2 * Real.pi by ring,
    Real.sin_add_two_pi, Real.sin_add_two_pi]
  simp

/-! ## The product of two features -/

/-- The product of two features splits into a term that carries the two points
and a term that carries the phase. -/
lemma fourierFeature_mul_apply {d : ℕ} (w : Vec d) (b : ℝ) (u u' : Sphere d) :
    fourierFeature (w, b) u * fourierFeature (w, b) u'
      = Real.cos (inner ℝ w u.1 - inner ℝ w u'.1)
        + Real.cos ((inner ℝ w u.1 + inner ℝ w u'.1) + 2 * b) := by
  unfold fourierFeature
  simp only
  set A := @inner ℝ (Vec d) _ w u.1 with hA
  set B := @inner ℝ (Vec d) _ w u'.1 with hB
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * Real.cos (A + b) * (Real.sqrt 2 * Real.cos (B + b))
      = (Real.sqrt 2 * Real.sqrt 2) * (Real.cos (A + b) * Real.cos (B + b)) := by ring
    _ = 2 * Real.cos (A + b) * Real.cos (B + b) := by rw [h2]; ring
    _ = Real.cos ((A + b) - (B + b)) + Real.cos ((A + b) + (B + b)) :=
        Real.two_mul_cos_mul_cos _ _
    _ = Real.cos (A - B) + Real.cos ((A + B) + 2 * b) := by
        rw [show (A + b) - (B + b) = A - B by ring,
          show (A + b) + (B + b) = (A + B) + 2 * b by ring]

/-- The product of two features is integrable at every draw law. The feature has
a bound, so no property of the law is used. -/
lemma integrable_fourierFeature_mul {d : ℕ} (μ : Measure (FourierDraw d))
    [IsProbabilityMeasure μ] (u u' : Sphere d) :
    Integrable (fun ω => fourierFeature ω u * fourierFeature ω u') μ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    (Continuous.aestronglyMeasurable (by unfold fourierFeature; fun_prop)) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, ← mul_one (fourierFeature ω u * fourierFeature ω u'),
    ← mul_one (2 : ℝ)]
  exact abs_featPair_mul_le (abs_fourierFeature_le ω u) (abs_fourierFeature_le ω u')
    zero_le_one le_rfl

lemma integrable_cos_add_two_mul (K : ℝ) :
    Integrable (fun b : ℝ => Real.cos (K + 2 * b)) phaseUniform :=
  Integrable.mono' (integrable_const (1 : ℝ))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (by filter_upwards with b; simpa using Real.abs_cos_le_one _)

/-! ## The identity -/

/-- **The mean product of two features is the angular kernel.** The phase removes
the term that carries it, and what remains is the characteristic function of the
frequency at the difference of the two points. -/
theorem fourierFeature_law (d : ℕ) (c : ℝ) (hc : 0 ≤ c) (u u' : Sphere d) :
    ∫ ω, fourierFeature ω u * fourierFeature ω u'
        ∂(fourierFeatureLaw d c : Measure (FourierDraw d))
      = chordalGaussian c u u' := by
  change ∫ ω, fourierFeature ω u * fourierFeature ω u'
      ∂((gaussianVec d c.toNNReal).prod phaseUniform) = _
  rw [integral_prod _ (integrable_fourierFeature_mul _ u u')]
  simp only [fourierFeature_mul_apply]
  have hinner : ∀ w : Vec d,
      (∫ b, (Real.cos (inner ℝ w u.1 - inner ℝ w u'.1)
          + Real.cos ((inner ℝ w u.1 + inner ℝ w u'.1) + 2 * b)) ∂phaseUniform)
        = Real.cos (inner ℝ w (u.1 - u'.1)) := by
    intro w
    rw [integral_add (integrable_const _) (integrable_cos_add_two_mul _),
      integral_cos_add_two_mul_phaseUniform, add_zero, integral_const,
      probReal_univ, smul_eq_mul, one_mul, inner_sub_right]
  simp only [hinner]
  rw [integral_cos_inner_gaussianVec, Real.coe_toNNReal c hc, chordalGaussian]
  congr 1
  ring

/-! ## The sampler -/

/-- The sampler assembled from the law and the explicit feature map. -/
def fourierFeatureSampler (d : ℕ) (c : ℝ) :
    AngularSampler d (FourierDraw d) where
  law := fourierFeatureLaw d c
  feat := fourierFeature

end WristbandLossProofs
