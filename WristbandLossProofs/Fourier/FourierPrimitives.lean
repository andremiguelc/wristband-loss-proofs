import WristbandLossProofs.Poisson.PoissonPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Fourier Primitives

Definitions for computing the angular kernel from random cosines.

The angular kernel is a Gaussian in the chordal distance:

  `kernelAngChordal β α u u' = exp(-(c/2) · ‖u - u'‖²)`,   `c = 2βα²`.

A Gaussian of that shape is the mean of a product of two cosines, over a
frequency drawn from a centred Gaussian and a phase drawn from one period. One
draw is therefore a frequency together with a phase, and the feature is one
cosine. `FourierDraw` is that draw, and `fourierFeature` is that feature.
`FourierLaw` builds the law of the draw and proves that identity.
`FourierFoundations` derives what the law implies.

The feature has a bound that holds at every point of the sphere and at every
draw: `|fourierFeature ω u| ≤ √2`. That bound is what separates this sampler
from a random Maclaurin sampler, whose feature is a product of projections and
has no bound. Every result below about integrability, about square-integrability
and about variance comes from that one inequality, and none of them reads the
law. So a change of law cannot break them.

The second section collects two properties of the radial factor: it has a bound
on the unit square, and it is continuous there. Both are kernel-level facts. The
draw energy needs them, because the radial factor stays exact while the angular
factor is sampled.
-/

/-! ### The draw and the feature -/

/-- One draw: a frequency in `ℝ^d`, together with a phase. Under the law of
`FourierLaw` the frequency is Gaussian with covariance `c I` and the phase is
uniform on one period. -/
abbrev FourierDraw (d : ℕ) : Type := Vec d × ℝ

/-- The random feature of a draw: `√2 · cos(⟪ω, u⟫ + b)`. -/
def fourierFeature {d : ℕ} (ω : FourierDraw d) (u : Sphere d) : ℝ :=
  Real.sqrt 2 * Real.cos (@inner ℝ (Vec d) _ ω.1 u.1 + ω.2)

/-- The angular kernel written as a Gaussian in the chordal distance. This is the
form in which the frequency law is stated, because it is the form Bochner's
theorem speaks about. -/
def chordalGaussian {d : ℕ} (c : ℝ) (u u' : Sphere d) : ℝ :=
  Real.exp (-(c / 2) * ‖u.1 - u'.1‖ ^ 2)

/-! ### The bound on the feature -/

/-- The squared chordal distance of two points of the unit sphere. -/
lemma norm_sub_sq_sphere {d : ℕ} (u u' : Sphere d) :
    ‖u.1 - u'.1‖ ^ 2 = 2 - 2 * sphereInner u u' := by
  have hu : ‖u.1‖ = 1 := by simp
  have hu' : ‖u'.1‖ = 1 := by simp
  rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hu, hu']
  simp [sphereInner, real_inner_comm u.1 u'.1]
  ring

/-- The chordal form and the inner-product form agree. -/
lemma kernelAngChordal_eq_chordalGaussian {d : ℕ} (β α : ℝ) (u u' : Sphere d) :
    kernelAngChordal β α u u' = chordalGaussian (2 * β * α ^ 2) u u' := by
  rw [kernelAngChordal, chordalGaussian, norm_sub_sq_sphere]
  congr 1
  ring

/-- **The feature has a bound that no draw and no point can exceed.** -/
lemma fourierFeature_sq_le_two {d : ℕ} (ω : FourierDraw d) (u : Sphere d) :
    fourierFeature ω u ^ 2 ≤ 2 := by
  rw [fourierFeature, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [Real.neg_one_le_cos (@inner ℝ (Vec d) _ ω.1 u.1 + ω.2),
    Real.cos_le_one (@inner ℝ (Vec d) _ ω.1 u.1 + ω.2)]

lemma abs_fourierFeature_le {d : ℕ} (ω : FourierDraw d) (u : Sphere d) :
    |fourierFeature ω u| ≤ Real.sqrt 2 := by
  have h2 : |fourierFeature ω u| ^ 2 ≤ Real.sqrt 2 ^ 2 := by
    rw [sq_abs, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    exact fourierFeature_sq_le_two ω u
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.sqrt_nonneg 2) two_ne_zero).mp h2

/-- Two features, each of size at most `√2`, against a non-negative third factor
of size at most `C`. This is the shape of one term of the draw energy. -/
lemma abs_featPair_mul_le {x y k C : ℝ} (hx : |x| ≤ Real.sqrt 2)
    (hy : |y| ≤ Real.sqrt 2) (hk0 : 0 ≤ k) (hk : k ≤ C) : |x * y * k| ≤ 2 * C := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hxy : |x| * |y| ≤ 2 := by
    nlinarith [abs_nonneg x, abs_nonneg y, Real.sqrt_nonneg 2]
  have hC : 0 ≤ C := hk0.trans hk
  rw [abs_mul, abs_mul, abs_of_nonneg hk0]
  nlinarith [abs_nonneg x, abs_nonneg y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

/-! ### The radial factor

`kernelRadNeumann` is an infinite sum of shifted Gaussians. Both shifts stay
inside `[-2, 2]` when the two radial coordinates stay inside `[0, 1]`. So one
shifted Gaussian of the sum is below a term that does not read the coordinates.
`radialDominant` is that term. It gives a bound on the whole sum, and it gives
continuity through `continuous_tsum`.

The three summands of `radialDominant` are the shifts at `2`, at `-2` and at `0`.
Each of them is a Gaussian image sum, so each is summable. Their sum dominates
because the image nearest to any point of `[-2, 2]` is never nearer than one of
those three. -/

/-- Three shifted Gaussians that together dominate one image term of the Neumann
series, at every pair of radial coordinates. -/
def radialDominant (β : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-β * (2 - 2 * n) ^ 2) + Real.exp (-β * (-2 - 2 * n) ^ 2)
    + Real.exp (-β * (0 - 2 * n) ^ 2)

lemma radialDominant_nonneg (β : ℝ) (n : ℤ) : 0 ≤ radialDominant β n := by
  unfold radialDominant; positivity

lemma radialDominant_summable (β : ℝ) (hβ : 0 < β) : Summable (radialDominant β) :=
  ((gaussianImageSum_summable β hβ 2).add (gaussianImageSum_summable β hβ (-2))).add
    (gaussianImageSum_summable β hβ 0)

/-- A shifted Gaussian at any offset of size at most two is below the dominant.
The three cases are the sign of the image index. -/
lemma exp_shift_le_radialDominant (β : ℝ) (hβ : 0 < β) (x : ℝ) (hx : |x| ≤ 2)
    (n : ℤ) : Real.exp (-β * (x - 2 * n) ^ 2) ≤ radialDominant β n := by
  have hx' := abs_le.mp hx
  have key : ∃ c : ℝ, (c = 2 ∨ c = -2 ∨ c = 0) ∧ (c - 2 * n) ^ 2 ≤ (x - 2 * n) ^ 2 := by
    rcases lt_trichotomy (n : ℝ) 0 with hn | hn | hn
    · refine ⟨-2, Or.inr (Or.inl rfl), ?_⟩
      have hn' : (n : ℝ) ≤ -1 := by
        have h0 : n < 0 := by exact_mod_cast hn
        have h1 : n ≤ -1 := by omega
        exact_mod_cast h1
      nlinarith [hx'.1, hx'.2]
    · refine ⟨0, Or.inr (Or.inr rfl), ?_⟩
      rw [hn]; nlinarith [sq_nonneg x]
    · refine ⟨2, Or.inl rfl, ?_⟩
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by
        have h0 : 0 < n := by exact_mod_cast hn
        have h1 : (1 : ℤ) ≤ n := by omega
        exact_mod_cast h1
      nlinarith [hx'.1, hx'.2]
  obtain ⟨c, hc, hle⟩ := key
  refine (Real.exp_le_exp.mpr (by nlinarith : -β * (x - 2 * n) ^ 2
    ≤ -β * (c - 2 * n) ^ 2)).trans ?_
  unfold radialDominant
  rcases hc with h | h | h <;> subst h <;>
    [ (have := Real.exp_nonneg (-β * (-2 - 2 * (n:ℝ)) ^ 2);
       have := Real.exp_nonneg (-β * (0 - 2 * (n:ℝ)) ^ 2); linarith);
      (have := Real.exp_nonneg (-β * (2 - 2 * (n:ℝ)) ^ 2);
       have := Real.exp_nonneg (-β * (0 - 2 * (n:ℝ)) ^ 2); linarith);
      (have := Real.exp_nonneg (-β * (2 - 2 * (n:ℝ)) ^ 2);
       have := Real.exp_nonneg (-β * (-2 - 2 * (n:ℝ)) ^ 2); linarith) ]

/-- The bound on the radial factor over the unit square. -/
def neumannSup (β : ℝ) : ℝ := 2 * ∑' n : ℤ, radialDominant β n

lemma neumannSup_nonneg (β : ℝ) : 0 ≤ neumannSup β := by
  have h : (0 : ℝ) ≤ ∑' n : ℤ, radialDominant β n :=
    tsum_nonneg (g := radialDominant β) (radialDominant_nonneg β)
  unfold neumannSup; linarith

lemma abs_sub_le_two_of_unitInterval (t t' : UnitInterval) :
    |(t : ℝ) - (t' : ℝ)| ≤ 2 := by
  have h1 := t.2; have h2 := t'.2
  simp only [Set.mem_Icc] at h1 h2
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma abs_add_le_two_of_unitInterval (t t' : UnitInterval) :
    |(t : ℝ) + (t' : ℝ)| ≤ 2 := by
  have h1 := t.2; have h2 := t'.2
  simp only [Set.mem_Icc] at h1 h2
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma kernelRadNeumann_nonneg (β : ℝ) (t t' : UnitInterval) :
    0 ≤ kernelRadNeumann β t t' := by
  unfold kernelRadNeumann
  exact tsum_nonneg fun n => by positivity

/-- **The radial factor has a bound on the unit square.** -/
lemma kernelRadNeumann_le_neumannSup (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    kernelRadNeumann β t t' ≤ neumannSup β := by
  have hsum := kernelRadNeumann_summable β hβ t t'
  have hdom : Summable (fun n : ℤ => 2 * radialDominant β n) :=
    (radialDominant_summable β hβ).mul_left 2
  have hle : ∀ n : ℤ,
      Real.exp (-β * ((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2) +
        Real.exp (-β * ((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2)
      ≤ 2 * radialDominant β n := by
    intro n
    have h1 := exp_shift_le_radialDominant β hβ ((t : ℝ) - (t' : ℝ))
      (abs_sub_le_two_of_unitInterval t t') n
    have h2 := exp_shift_le_radialDominant β hβ ((t : ℝ) + (t' : ℝ))
      (abs_add_le_two_of_unitInterval t t') n
    linarith
  calc kernelRadNeumann β t t' ≤ ∑' n : ℤ, 2 * radialDominant β n :=
        hsum.tsum_le_tsum hle hdom
    _ = neumannSup β := by rw [neumannSup, tsum_mul_left]

/-- **The radial factor is continuous on the unit square.** The same dominating
term that gives the bound gives uniform convergence of the image sum. -/
lemma continuous_kernelRadNeumann (β : ℝ) (hβ : 0 < β) :
    Continuous (fun q : UnitInterval × UnitInterval => kernelRadNeumann β q.1 q.2) := by
  have hcont : ∀ n : ℤ, Continuous (fun q : UnitInterval × UnitInterval =>
      Real.exp (-β * ((q.1 : ℝ) - (q.2 : ℝ) - 2 * n) ^ 2) +
        Real.exp (-β * ((q.1 : ℝ) + (q.2 : ℝ) - 2 * n) ^ 2)) := fun n => by fun_prop
  have hbound : ∀ (n : ℤ) (q : UnitInterval × UnitInterval),
      ‖Real.exp (-β * ((q.1 : ℝ) - (q.2 : ℝ) - 2 * n) ^ 2) +
        Real.exp (-β * ((q.1 : ℝ) + (q.2 : ℝ) - 2 * n) ^ 2)‖
      ≤ 2 * radialDominant β n := by
    intro n q
    have h1 := exp_shift_le_radialDominant β hβ ((q.1 : ℝ) - (q.2 : ℝ))
      (abs_sub_le_two_of_unitInterval q.1 q.2) n
    have h2 := exp_shift_le_radialDominant β hβ ((q.1 : ℝ) + (q.2 : ℝ))
      (abs_add_le_two_of_unitInterval q.1 q.2) n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  exact continuous_tsum hcont ((radialDominant_summable β hβ).mul_left 2) hbound

end WristbandLossProofs
