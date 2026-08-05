import WristbandLossProofs.Poisson.PoissonImportedFacts
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Foundations

Local derivations for the Poisson branch. Two independent strands.

**The kernel is a Poisson mixture.** `kernelAngChordal_maclaurinExpansion`
rewrites the angular kernel as a power series in `⟪u, u'⟫` whose coefficients
are `poissonWeight (2βα²)`. Those coefficients are non-negative and sum to `1`,
which is exactly what `randomMaclaurin_law_exists` asks of its input — so this
strand is what licenses `poissonAngularSampler` at the end of the file. Nothing
here is imported: it is the exponential series.

**Finite rank has a blind spot.** `kernelEnergy_eq_sum_sq_of_rankWitness` shows
that a rank-`r` kernel's energy is a function of the `r` feature means and
nothing else. Blindness is then immediate: any two distributions with equal
feature means have equal energy. This is the whole content of the negative
result, and the only thing imported is the existence of such a pair.
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

/-- The coefficients are a probability distribution over the exponent. This is
the statement that the angular kernel is normalised at `⟪u, u⟫ = 1`. -/
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

/-! ### Finite rank determines the energy -/

/-- A rank-`r` kernel's energy is the sum of the squared feature means. This is
where the blindness comes from: the energy sees the `r` numbers `∫ f i dP` and
nothing else about `P`. -/
lemma kernelEnergy_eq_sum_sq_of_rankWitness
    {X : Type*} [MeasurableSpace X] {r : ℕ}
    (K : X → X → ℝ) (f : Fin r → X → ℝ) (P : Distribution X)
    (hK : ∀ x y, K x y = ∑ i : Fin r, f i x * f i y)
    (hInt : ∀ i, Integrable (f i) (P : Measure X)) :
    kernelEnergy K P = ∑ i : Fin r, (∫ x, f i x ∂(P : Measure X)) ^ 2 := by
  have hinner : ∀ x : X,
      ∫ y, K x y ∂(P : Measure X)
        = ∑ i : Fin r, f i x * ∫ y, f i y ∂(P : Measure X) := by
    intro x
    calc ∫ y, K x y ∂(P : Measure X)
        = ∫ y, ∑ i : Fin r, f i x * f i y ∂(P : Measure X) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun y => hK x y)
      _ = ∑ i : Fin r, ∫ y, f i x * f i y ∂(P : Measure X) :=
          integral_finset_sum _ fun i _ => (hInt i).const_mul _
      _ = ∑ i : Fin r, f i x * ∫ y, f i y ∂(P : Measure X) :=
          Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [kernelEnergy]
  calc ∫ x, ∫ y, K x y ∂(P : Measure X) ∂(P : Measure X)
      = ∫ x, ∑ i : Fin r, f i x * ∫ y, f i y ∂(P : Measure X)
          ∂(P : Measure X) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = ∑ i : Fin r, ∫ x, f i x * (∫ y, f i y ∂(P : Measure X))
          ∂(P : Measure X) :=
        integral_finset_sum _ fun i _ => (hInt i).mul_const _
    _ = ∑ i : Fin r, (∫ x, f i x ∂(P : Measure X)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by
          rw [integral_mul_const]; ring

/-- Blindness, given a witness. Two distributions agreeing on the rank
witness's features have equal energy, so if one of them is not `μ₀` the kernel
cannot distinguish them. -/
theorem isBlindAt_of_rankWitness
    {X : Type*} [MeasurableSpace X] {r : ℕ}
    (K : X → X → ℝ) (f : Fin r → X → ℝ) (μ₀ P : Distribution X)
    (hK : ∀ x y, K x y = ∑ i : Fin r, f i x * f i y)
    (hne : P ≠ μ₀)
    (hAgree : AgreeOnFeatures f P μ₀)
    (hIntP : ∀ i, Integrable (f i) (P : Measure X))
    (hIntQ : ∀ i, Integrable (f i) (μ₀ : Measure X)) :
    IsBlindAt K μ₀ := by
  refine ⟨P, hne, ?_⟩
  rw [kernelEnergy_eq_sum_sq_of_rankWitness K f P hK hIntP,
    kernelEnergy_eq_sum_sq_of_rankWitness K f μ₀ hK hIntQ]
  exact Finset.sum_congr rfl fun i _ => by rw [hAgree i]

/-- The wristband instance: any finite-rank kernel on the wristband is blind at
the uniform measure. This is what the `ℓ ≤ L` truncation buys — the truncated
kernel has rank `∑_{ℓ≤L} N_ℓ`, and no amount of training removes the defect. -/
theorem isBlindAt_of_hasFiniteRank
    (d : ℕ) (hDim : 1 ≤ d) (r : ℕ) (K : Wristband d → Wristband d → ℝ)
    (f : Fin r → Wristband d → ℝ)
    (hK : ∀ x y, K x y = ∑ i : Fin r, f i x * f i y)
    (hf : ∀ i, Integrable (f i)
      ((wristbandUniform d hDim : Distribution (Wristband d)) :
        Measure (Wristband d))) :
    IsBlindAt K (wristbandUniform d hDim) := by
  obtain ⟨P, hne, hIntP, hAgree⟩ := finiteRank_hasNontrivialFibre d hDim r f hf
  exact isBlindAt_of_rankWitness K f _ P hK hne hAgree hIntP hf

end WristbandLossProofs
