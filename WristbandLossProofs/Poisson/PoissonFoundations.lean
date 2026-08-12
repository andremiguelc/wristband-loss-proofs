import WristbandLossProofs.Poisson.PoissonImportedFacts
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Foundations

Local derivations for the Poisson branch. They reach one conclusion:
`poissonAngularSampler` is unbiased for the angular kernel.

`kernelAngChordal_maclaurinExpansion` rewrites the angular kernel as a power
series in `⟪u, u'⟫`. Its coefficients are `poissonWeight (2βα²)`.
`randomMaclaurin_law_exists` asks two things of its input, and
`poissonWeight_nonneg` and `poissonWeight_summable` give them. Feed one result
into the other. This gives the sampler and its unbiasedness.

This file imports no fact. The expansion is the exponential series, and the
coefficient facts are elementary.
-/

/-! ### The exponential series -/

/-- `Real.exp` as a power series, assembled from the two Mathlib halves. -/
lemma real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ### Poisson weights -/

lemma poissonWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ poissonWeight c m :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hc m))
    (Nat.cast_nonneg _)

lemma poissonWeight_summable (c : ℝ) : Summable (poissonWeight c) := by
  have h := (Real.summable_pow_div_factorial c).mul_left (Real.exp (-c))
  refine h.congr fun m => ?_
  rw [poissonWeight]
  ring

/-- The coefficients are a probability distribution over the exponent. This states
that the angular kernel has the value `1` at `⟪u, u⟫ = 1`. -/
lemma poissonWeight_tsum_eq_one (c : ℝ) : ∑' m : ℕ, poissonWeight c m = 1 := by
  have h : ∑' m : ℕ, poissonWeight c m
      = Real.exp (-c) * ∑' m : ℕ, c ^ m / (Nat.factorial m : ℝ) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by rw [poissonWeight]; ring
  rw [h, ← real_exp_eq_tsum, ← Real.exp_add]
  simp

/-! ### The angular kernel is a Poisson mixture -/

/-- The angular kernel written as a power series in `⟪u, u'⟫`, with Poisson
coefficients of mean `c = 2βα²`. Derived, not imported: it is `exp` expanded. -/
lemma kernelAngChordal_maclaurinExpansion {d : ℕ} (β α : ℝ) (u u' : Sphere d) :
    kernelAngChordal β α u u'
      = dotProductKernel (poissonWeight (2 * β * α ^ 2)) u u' := by
  have hsplit : kernelAngChordal β α u u'
      = Real.exp (-(2 * β * α ^ 2))
        * Real.exp (2 * β * α ^ 2 * sphereInner u u') := by
    rw [kernelAngChordal, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit, real_exp_eq_tsum (2 * β * α ^ 2 * sphereInner u u'),
    ← tsum_mul_left, dotProductKernel]
  refine tsum_congr fun m => ?_
  rw [poissonWeight, mul_pow]
  ring

/-! ### The sampler for the angular kernel -/

/-- The sampler whose expected feature product is the angular kernel: the
random-feature law of `PoissonImportedFacts`, fed the Poisson coefficients. -/
def poissonAngularSampler (d : ℕ) (β α : ℝ) (hβ : 0 < β) :
    AngularSampler d (RademacherDraw d) :=
  randomMaclaurinSampler d (poissonWeight (2 * β * α ^ 2))
    (poissonWeight_nonneg (by positivity))
    (poissonWeight_summable _)

lemma poissonAngularSampler_unbiased (d : ℕ) (β α : ℝ) (hβ : 0 < β) :
    IsUnbiasedFor (poissonAngularSampler d β α hβ)
      (kernelAngChordal (d := d) β α) := by
  intro u u'
  have h := (randomMaclaurin_law_exists d (poissonWeight (2 * β * α ^ 2))
    (poissonWeight_nonneg (by positivity))
    (poissonWeight_summable _)).choose_spec u u'
  rw [kernelAngChordal_maclaurinExpansion]
  exact h

end WristbandLossProofs
