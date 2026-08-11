import WristbandLossProofs.Poisson.PoissonVariance

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## The second moment as a certified lower bound on the gap

`kernelEnergy K P - kernelEnergy K μ₀` is the quantity the loss reports, and by
`energy_eq_mmdSq_of_constantPotential` it is `MMD²(P, μ₀)`. Nothing downstream can
be trusted without a lower bound on it, and a lower bound is what a batch
measurement can supply.

The mechanism is a split. Write the angular kernel as

  `kernelAngChordal = angularRemainder + a * dotSqKernel`,   `a = e^{-c} c² / 2`,

where `dotSqKernel u u' = ⟪u, u'⟫²` and `c = 2βα²`. The coefficient `a` is the
quadratic Maclaurin coefficient of `exp(c(t-1))`, so the remainder is the same
series with that one term deleted — its coefficients are still non-negative, so
it is still a kernel whose energy the uniform measure minimizes. Subtracting the
two energies, the remainder can only help, and what is left is a bound written
entirely in `dotSqKernel`:

  `a * (E_dotSq(P) - E_dotSq(μ₀))  ≤  E_ang(P) - E_ang(μ₀)`.

The left side is measurable from a batch in closed form: `E_dotSq(P)` is
`‖E_P[u uᵀ]‖²_F`, the sum of the squared eigenvalues of the second-moment matrix,
and `E_dotSq(μ₀) = 1/d`. That is the "cliff" a practitioner reads off a batch,
and its reciprocal is the participation ratio.

`energyGap_ge_of_remainder` is the general statement and is elementary — it is
linearity of the energy in the kernel, nothing more. The single imported fact is
that the remainder's energy is minimized at the uniform measure.

The inequality points the safe way. A *lower* bound on the gap gives, through
`featureCount_suffices`, an *upper* bound on the features needed — so a budget
chosen from it is at worst too generous. The bound sees only the quadratic part
of the deviation, so a `P` that matches the uniform second moment exactly is
certified as `0` however far away it is; the bound is one-sided, not an estimate.
-/

/-! ### Energy is linear in the kernel -/

/-- Both integrals defining `kernelEnergy K P` exist. `kernelEnergy` is an
iterated integral and Bochner integration returns zero off its domain, so
linearity is not free. -/
structure HasEnergy {X : Type*} [MeasurableSpace X] (K : X → X → ℝ)
    (P : Distribution X) : Prop where
  inner : ∀ᵐ x ∂(P : Measure X), Integrable (fun y => K x y) (P : Measure X)
  outer : Integrable (fun x => ∫ y, K x y ∂(P : Measure X)) (P : Measure X)

lemma kernelEnergy_add {X : Type*} [MeasurableSpace X] (K L : X → X → ℝ)
    (P : Distribution X) (hK : HasEnergy K P) (hL : HasEnergy L P) :
    kernelEnergy (fun x y => K x y + L x y) P
      = kernelEnergy K P + kernelEnergy L P := by
  simp only [kernelEnergy]
  have hinner : (fun x => ∫ y, (K x y + L x y) ∂(P : Measure X))
      =ᵐ[(P : Measure X)]
      fun x => (∫ y, K x y ∂(P : Measure X)) + (∫ y, L x y ∂(P : Measure X)) := by
    filter_upwards [hK.inner, hL.inner] with x h1 h2 using integral_add h1 h2
  rw [integral_congr_ae hinner]
  exact integral_add hK.outer hL.outer

lemma kernelEnergy_const_mul {X : Type*} [MeasurableSpace X] (a : ℝ)
    (K : X → X → ℝ) (P : Distribution X) :
    kernelEnergy (fun x y => a * K x y) P = a * kernelEnergy K P := by
  simp only [kernelEnergy, integral_const_mul]

/-! ### The splitting bound -/

/-- **Dropping a non-negative-coefficient remainder can only lower the gap.**

If `K = R + a·Q` with `a ≥ 0`, and the uniform measure minimizes `R`'s energy,
then `K`'s gap over the uniform measure dominates `a` times `Q`'s gap.

Elementary: linearity of the energy plus one inequality. The content is entirely
in the hypothesis `hR`, which is where the analysis lives. -/
theorem energyGap_ge_of_remainder {X : Type*} [MeasurableSpace X]
    (K R Q : X → X → ℝ) (a : ℝ) (P μ₀ : Distribution X)
    (hsplit : ∀ x y, K x y = R x y + a * Q x y)
    (hRP : HasEnergy R P) (hQP : HasEnergy (fun x y => a * Q x y) P)
    (hRU : HasEnergy R μ₀) (hQU : HasEnergy (fun x y => a * Q x y) μ₀)
    (hR : kernelEnergy R μ₀ ≤ kernelEnergy R P) :
    a * (kernelEnergy Q P - kernelEnergy Q μ₀)
      ≤ kernelEnergy K P - kernelEnergy K μ₀ := by
  have hK : K = fun x y => R x y + a * Q x y := by
    funext x y; exact hsplit x y
  have hP : kernelEnergy K P = kernelEnergy R P + a * kernelEnergy Q P := by
    rw [hK, kernelEnergy_add _ _ _ hRP hQP, kernelEnergy_const_mul]
  have hU : kernelEnergy K μ₀ = kernelEnergy R μ₀ + a * kernelEnergy Q μ₀ := by
    rw [hK, kernelEnergy_add _ _ _ hRU hQU, kernelEnergy_const_mul]
  rw [hP, hU]
  have : a * kernelEnergy Q P - a * kernelEnergy Q μ₀
      = a * (kernelEnergy Q P - kernelEnergy Q μ₀) := by ring
  linarith

/-! ### The angular instance -/

/-- The squared cosine similarity, read as a kernel. Its energy at `P` is
`‖E_P[u uᵀ]‖²_F`, the sum of the squared eigenvalues of the batch's
second-moment matrix. -/
def dotSqKernel {d : ℕ} (u u' : Sphere d) : ℝ := sphereInner u u' ^ 2

/-- The quadratic Maclaurin coefficient of `exp(c(t-1))`, namely `e^{-c} c²/2`. -/
def angularQuadCoeff (β α : ℝ) : ℝ :=
  Real.exp (-(2 * β * α ^ 2)) * (2 * β * α ^ 2) ^ 2 / 2

lemma angularQuadCoeff_nonneg (β α : ℝ) : 0 ≤ angularQuadCoeff β α := by
  unfold angularQuadCoeff; positivity

/-- The angular kernel with its quadratic term removed. Its Maclaurin
coefficients are `poissonWeight c` with the `m = 2` entry deleted, so they are
still non-negative. -/
def angularRemainder {d : ℕ} (β α : ℝ) (u u' : Sphere d) : ℝ :=
  kernelAngChordal β α u u' - angularQuadCoeff β α * dotSqKernel u u'

lemma kernelAngChordal_eq_remainder_add {d : ℕ} (β α : ℝ) (u u' : Sphere d) :
    kernelAngChordal β α u u'
      = angularRemainder β α u u' + angularQuadCoeff β α * dotSqKernel u u' := by
  unfold angularRemainder; ring

/-- **The gap is at least the second-moment excess, scaled by `e^{-c} c²/2`.**

The left-hand side is computable from a batch: `kernelEnergy dotSqKernel P` is the
sum of the squared eigenvalues of `E_P[u uᵀ]`, and at the uniform measure it is
`1/d`. So a batch measurement certifies a lower bound on the distance the loss
has to report, with no approximation and no sampling.

`hRem` is the only analytic input, and it is supplied by
`angularRemainder_energy_minimized_at_uniform`. -/
theorem angularGap_ge_secondMomentGap {d : ℕ} (β α : ℝ)
    (P μ₀ : Distribution (Sphere d))
    (hRP : HasEnergy (angularRemainder β α) P)
    (hQP : HasEnergy (fun u u' => angularQuadCoeff β α * dotSqKernel u u') P)
    (hRU : HasEnergy (angularRemainder β α) μ₀)
    (hQU : HasEnergy (fun u u' => angularQuadCoeff β α * dotSqKernel u u') μ₀)
    (hRem : kernelEnergy (angularRemainder β α) μ₀
      ≤ kernelEnergy (angularRemainder β α) P) :
    angularQuadCoeff β α
        * (kernelEnergy dotSqKernel P - kernelEnergy dotSqKernel μ₀)
      ≤ kernelEnergy (kernelAngChordal β α) P
        - kernelEnergy (kernelAngChordal β α) μ₀ :=
  energyGap_ge_of_remainder _ _ _ _ P μ₀
    (kernelAngChordal_eq_remainder_add β α) hRP hQP hRU hQU hRem

/-! ### The remainder really is a non-negative-coefficient kernel

`angularRemainder` was defined by subtraction. This identifies it with the same
Maclaurin series minus one term, which is what lets the imported minimization
fact apply to it. -/

/-- Maclaurin coefficients with the `b`-th entry deleted. -/
def maclaurinDrop (p : ℕ → ℝ) (b : ℕ) : ℕ → ℝ := fun m => if m = b then 0 else p m

lemma maclaurinDrop_nonneg {p : ℕ → ℝ} (hp : ∀ m, 0 ≤ p m) (b m : ℕ) :
    0 ≤ maclaurinDrop p b m := by
  unfold maclaurinDrop; split_ifs with h
  · exact le_refl 0
  · exact hp m

lemma maclaurinDrop_summable {p : ℕ → ℝ} (hp : ∀ m, 0 ≤ p m) (hsum : Summable p)
    (b : ℕ) : Summable (maclaurinDrop p b) := by
  refine Summable.of_norm_bounded hsum fun m => ?_
  unfold maclaurinDrop
  split_ifs with h
  · simpa using hp m
  · simp [Real.norm_eq_abs, abs_of_nonneg (hp m)]

/-- `|⟪u, u'⟫| ≤ 1` for points of the unit sphere. -/
lemma abs_sphereInner_le_one {d : ℕ} (u u' : Sphere d) :
    |sphereInner u u'| ≤ 1 := by
  unfold sphereInner
  calc |@inner ℝ (Vec d) _ u.1 u'.1| ≤ ‖u.1‖ * ‖u'.1‖ := abs_real_inner_le_norm _ _
    _ = 1 := by simp

lemma summable_dotProduct_terms {d : ℕ} {p : ℕ → ℝ} (hp : ∀ m, 0 ≤ p m)
    (hsum : Summable p) (u u' : Sphere d) :
    Summable fun m => p m * sphereInner u u' ^ m := by
  refine Summable.of_norm_bounded hsum fun m => ?_
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp m)]
  calc p m * |sphereInner u u'| ^ m ≤ p m * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (abs_nonneg _) (abs_sphereInner_le_one u u')) (hp m)
    _ = p m := by simp

/-- Peeling one term off a dot-product kernel. -/
lemma dotProductKernel_eq_drop_add {d : ℕ} {p : ℕ → ℝ} (hp : ∀ m, 0 ≤ p m)
    (hsum : Summable p) (b : ℕ) (u u' : Sphere d) :
    dotProductKernel p u u'
      = p b * sphereInner u u' ^ b + dotProductKernel (maclaurinDrop p b) u u' := by
  have hs := summable_dotProduct_terms hp hsum u u'
  rw [dotProductKernel, hs.tsum_eq_add_tsum_ite b, dotProductKernel]
  congr 1
  refine tsum_congr fun m => ?_
  unfold maclaurinDrop
  split_ifs <;> simp

lemma angularQuadCoeff_eq_poissonWeight (β α : ℝ) :
    angularQuadCoeff β α = poissonWeight (2 * β * α ^ 2) 2 := by
  unfold angularQuadCoeff poissonWeight
  norm_num

/-- The remainder is the angular kernel's own series with the `m = 2` term
deleted. -/
lemma angularRemainder_eq_dotProductKernel {d : ℕ} (β α : ℝ)
    (hβα : 0 ≤ 2 * β * α ^ 2) (u u' : Sphere d) :
    angularRemainder β α u u'
      = dotProductKernel (maclaurinDrop (poissonWeight (2 * β * α ^ 2)) 2) u u' := by
  have hp : ∀ m, 0 ≤ poissonWeight (2 * β * α ^ 2) m :=
    fun m => poissonWeight_nonneg hβα m
  have hsum := poissonWeight_summable (2 * β * α ^ 2)
  have hdrop := dotProductKernel_eq_drop_add hp hsum 2 u u'
  unfold angularRemainder
  rw [kernelAngChordal_maclaurinExpansion β α u u', hdrop,
    angularQuadCoeff_eq_poissonWeight, dotSqKernel]
  ring

/-- **The remainder's energy is minimized at the uniform measure**, so the
hypothesis of `angularGap_ge_secondMomentGap` is discharged. -/
lemma angularRemainder_energy_minimized_at_uniform {d : ℕ} (hDim : 1 ≤ d)
    (β α : ℝ) (hβα : 0 ≤ 2 * β * α ^ 2) (P : Distribution (Sphere d)) :
    kernelEnergy (angularRemainder β α) (sphereUniform d hDim)
      ≤ kernelEnergy (angularRemainder β α) P := by
  have hp : ∀ m, 0 ≤ poissonWeight (2 * β * α ^ 2) m :=
    fun m => poissonWeight_nonneg hβα m
  have hfun : angularRemainder (d := d) β α
      = dotProductKernel (maclaurinDrop (poissonWeight (2 * β * α ^ 2)) 2) := by
    funext u u'; exact angularRemainder_eq_dotProductKernel β α hβα u u'
  rw [hfun]
  exact dotProductKernel_energy_minimized_at_uniform d hDim _
    (maclaurinDrop_nonneg hp 2)
    (maclaurinDrop_summable hp (poissonWeight_summable _) 2) P

/-- **The bound, with nothing left to supply but integrability.**

`kernelEnergy dotSqKernel P` is the sum of the squared eigenvalues of the batch's
second-moment matrix, and at the uniform measure it is `1/d`. So the right-hand
side — the distance the loss has to report — is bounded below by a number a
batch hands you directly. -/
theorem angularGap_ge_secondMomentGap_of_uniform {d : ℕ} (hDim : 1 ≤ d) (β α : ℝ)
    (hβα : 0 ≤ 2 * β * α ^ 2) (P : Distribution (Sphere d))
    (hRP : HasEnergy (angularRemainder β α) P)
    (hQP : HasEnergy (fun u u' => angularQuadCoeff β α * dotSqKernel u u') P)
    (hRU : HasEnergy (angularRemainder β α) (sphereUniform d hDim))
    (hQU : HasEnergy (fun u u' => angularQuadCoeff β α * dotSqKernel u u')
      (sphereUniform d hDim)) :
    angularQuadCoeff β α
        * (kernelEnergy dotSqKernel P
            - kernelEnergy dotSqKernel (sphereUniform d hDim))
      ≤ kernelEnergy (kernelAngChordal β α) P
        - kernelEnergy (kernelAngChordal β α) (sphereUniform d hDim) :=
  angularGap_ge_secondMomentGap β α P _ hRP hQP hRU hQU
    (angularRemainder_energy_minimized_at_uniform hDim β α hβα P)

/-! ### What a certified gap buys: the two estimates come out in the right order

`featureCount_suffices` bounds one estimate's deviation. Detection needs two — at
the batch and at the target — from the *same* draw, so a union bound joins them.
The conclusion is the statement a practitioner wants: with enough features the
loss ranks a degenerate batch above the target, and the failure probability is
explicit. -/

/-- **A gap of `2ε` is reported correctly with probability at least `1 - 2δ`.**

Both estimates use the same draw vector `ω`, so this is one event on one space.
If each estimate is within `ε` of its true value, and the true values differ by
more than `2ε`, the order is right. -/
theorem realizedEnergy_separates {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β α : ℝ) {D : ℕ} (hD : 0 < D)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P Q : Distribution (Wristband d))
    (hIntP : HasIntegrableDrawEnergy S β P) (hIntQ : HasIntegrableDrawEnergy S β Q)
    (hL2P : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω))
    (hL2Q : MemLp (drawEnergy S β Q) 2 (S.law : Measure Ω))
    {V δ ε : ℝ}
    (hVP : Var[drawEnergy S β P; (S.law : Measure Ω)] ≤ V)
    (hVQ : Var[drawEnergy S β Q; (S.law : Measure Ω)] ≤ V)
    (hδ : 0 < δ) (hε : 0 < ε)
    (hcount : V / (δ * ε ^ 2) ≤ (D : ℝ))
    (hgap : 2 * ε < kernelEnergy (wristbandKernelNeumann (d := d) β α) P
      - kernelEnergy (wristbandKernelNeumann (d := d) β α) Q) :
    (drawLaw S D : Measure (Fin D → Ω))
        {ω | kernelEnergy (realizedWristbandKernel S β ω) Q
              < kernelEnergy (realizedWristbandKernel S β ω) P}ᶜ
      ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
  set EP := kernelEnergy (wristbandKernelNeumann (d := d) β α) P with hEP
  set EQ := kernelEnergy (wristbandKernelNeumann (d := d) β α) Q with hEQ
  set BadP : Set (Fin D → Ω) :=
    {ω | ε ≤ |kernelEnergy (realizedWristbandKernel S β ω) P - EP|} with hBadP
  set BadQ : Set (Fin D → Ω) :=
    {ω | ε ≤ |kernelEnergy (realizedWristbandKernel S β ω) Q - EQ|} with hBadQ
  have hsub : {ω : Fin D → Ω | kernelEnergy (realizedWristbandKernel S β ω) Q
      < kernelEnergy (realizedWristbandKernel S β ω) P}ᶜ ⊆ BadP ∪ BadQ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, hBadP, hBadQ, Set.mem_setOf_eq, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' := abs_lt.mp h1
    have h2' := abs_lt.mp h2
    exact hω (by simp only [Set.mem_setOf_eq]; linarith [h1'.1, h2'.2])
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add
    (featureCount_suffices S β α hD hUnbiased P hIntP hL2P hVP hδ hε hcount)
    (featureCount_suffices S β α hD hUnbiased Q hIntQ hL2Q hVQ hδ hε hcount)

end WristbandLossProofs
