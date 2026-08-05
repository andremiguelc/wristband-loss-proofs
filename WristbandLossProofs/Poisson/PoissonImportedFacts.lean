import WristbandLossProofs.Poisson.PoissonPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Poisson Imported Facts

External results assumed without Lean proof, plus the extracted definitions
used across the Poisson branch. One axiom only; everything else in the branch
is derived from it.

References:
- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels."
  *AISTATS* 2012, *PMLR* 22, 583–591.

CITATION PENDING VERIFICATION. The attribution is from recollection and has not
been checked against the source. Open questions: the precise result number, and
whether the source states it for the sphere or for a bounded-norm domain.
Adjacent candidates are Pham & Pagh (2013) and Hamid et al. (2014).
-/

/-! ## Axioms -/

/-- Kar-Karnick: a dot-product kernel with non-negative summable Maclaurin
    coefficients is the expected product of two `randomMaclaurinFeature`s,
    under a law drawing the exponent from the normalised coefficients and the
    vectors with independent `±1` coordinates.

    Specialization: stated for `Sphere d` and for the explicit feature map of
    `PoissonPrimitives`, so only the law is imported, not the construction.

    Fragilities:
    1. The source constructs the estimator and proves unbiasedness; assembling
       the product measure on the sigma-type `RademacherDraw` is ours.
    2. Non-negativity of the coefficients is the source hypothesis; summability
       is added here because the feature carries the factor `√(∑' p)`.
    3. Says nothing about variance, which is where the real cost sits. -/
axiom randomMaclaurin_law_exists
    (d : ℕ) (p : ℕ → ℝ) (hp : ∀ m, 0 ≤ p m) (hsum : Summable p) :
    ∃ μ : Distribution (RademacherDraw d),
      ∀ u u' : Sphere d,
        ∫ ω, randomMaclaurinFeature p ω u * randomMaclaurinFeature p ω u'
            ∂(μ : Measure (RademacherDraw d))
          = dotProductKernel p u u'

/-! ## Witness extraction -/

/-- The draw law extracted from `randomMaclaurin_law_exists`. -/
def randomMaclaurinLaw (d : ℕ) (p : ℕ → ℝ) (hp : ∀ m, 0 ≤ p m)
    (hsum : Summable p) : Distribution (RademacherDraw d) :=
  (randomMaclaurin_law_exists d p hp hsum).choose

/-- The sampler assembled from that law and the explicit feature map. -/
def randomMaclaurinSampler (d : ℕ) (p : ℕ → ℝ) (hp : ∀ m, 0 ≤ p m)
    (hsum : Summable p) : AngularSampler d (RademacherDraw d) where
  law := randomMaclaurinLaw d p hp hsum
  feat := randomMaclaurinFeature p

end WristbandLossProofs
