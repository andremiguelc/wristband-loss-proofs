import WristbandLossProofs.Poisson.PoissonPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Poisson Imported Facts

External results assumed without Lean proof, plus the extracted definitions
used across the Poisson branch. Two axioms only; everything else in the branch
is derived from them.

References:
- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels."
  *AISTATS* 2012, *PMLR* 22, 583–591.
- Sriperumbudur, B.; Fukumizu, K.; Lanckriet, G. (2011). "Universality,
  Characteristic Kernels and RKHS Embedding of Measures." *JMLR* 12,
  2389–2410.

CITATIONS PENDING VERIFICATION. Both attributions are from recollection and
have not been checked against the sources. For `randomMaclaurin_law_exists`,
the open questions are the precise result number and whether the source states
it for the sphere or for a bounded-norm domain; adjacent candidates are Pham &
Pagh (2013) and Hamid et al. (2014). For `finiteRank_hasNontrivialFibre`, the
attribution is the weaker of the two and the result may instead belong to
Sriperumbudur et al. (2010), *JMLR* 11, 1517–1561, or to Steinwart &
Christmann (2008), *Support Vector Machines*.
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

/-- Finitely many test functions cannot separate the measures on the wristband:
    for any `r` features there is a distribution other than the uniform one
    agreeing with it on all of them.

    Specialization: stated for `Wristband d` against `wristbandUniform`, the
    only instance the branch needs.

    Fragilities:
    1. Sources state this as "a characteristic kernel has infinite-dimensional
       RKHS"; the fibre form here is the contrapositive, specialised to one
       target measure.
    2. The usual proof perturbs `μ₀` by a bounded density satisfying `r + 1`
       linear constraints, which needs `L^∞(μ₀)` infinite-dimensional. That
       holds on the wristband but is not itself recorded here. Integrability
       under `P` is part of the conclusion for the same reason: the witness has
       bounded density with respect to `μ₀`, so it inherits it.
    3. Gives no control on how far the blind `P` is from `μ₀`. -/
axiom finiteRank_hasNontrivialFibre
    (d : ℕ) (hDim : 1 ≤ d) (r : ℕ) (f : Fin r → Wristband d → ℝ)
    (hf : ∀ i, Integrable (f i)
      ((wristbandUniform d hDim : Distribution (Wristband d)) :
        Measure (Wristband d))) :
    ∃ P : Distribution (Wristband d),
      P ≠ wristbandUniform d hDim ∧
        (∀ i, Integrable (f i) (P : Measure (Wristband d))) ∧
        AgreeOnFeatures f P (wristbandUniform d hDim)

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
