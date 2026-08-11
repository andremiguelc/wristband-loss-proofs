import WristbandLossProofs.Poisson.PoissonPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Poisson Imported Facts

External results assumed without Lean proof, plus the extracted definitions
used across the Poisson branch. Two axioms; everything else in the branch is
derived from them.

References:
- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels."
  *AISTATS* 2012, *PMLR* 22, 583–591.
- Schoenberg, I. J. (1942). "Positive definite functions on spheres."
  *Duke Math. J.* 9, 96–108.
- Björck, G. (1956). "Distributions of positive mass, which maximize a certain
  generalized energy integral." *Ark. Mat.* 3, 255–269.

CITATION PENDING VERIFICATION, both axioms, both from recollection.

`randomMaclaurin_law_exists` ← Kar & Karnick. Open: the result number, and
whether the source states it on the sphere or on a bounded-norm domain.
Adjacent candidates are Pham & Pagh (2013) and Hamid et al. (2014).

`dotProductKernel_energy_minimized_at_uniform` ← Schoenberg for the positive
definiteness, Björck for the energy minimum. Open: the result numbers, whether
Björck covers a general non-negative-coefficient kernel or only the Riesz
family, and whether the minimum is stated for `S^{d-1}` at every `d ≥ 1`.
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

/-- Schoenberg, Björck: the uniform measure minimizes the energy of a
    dot-product kernel whose Maclaurin coefficients are non-negative.

    Such coefficients make the kernel positive definite on the sphere; the
    kernel is zonal, so the uniform measure has constant potential, and the two
    together put the minimum there.

    Fragilities:
    1. Stated at the level of the energy, so the constant-potential step is
       imported with it rather than derived from `energy_eq_mmdSq_of_constantPotential`.
    2. Both integrals defining `kernelEnergy` are assumed to exist; the statement
       is about their values, not their existence.
    3. Gives a minimum, not a modulus. Nothing here says how fast the energy
       grows away from the uniform measure. -/
axiom dotProductKernel_energy_minimized_at_uniform
    (d : ℕ) (hDim : 1 ≤ d) (p : ℕ → ℝ) (hp : ∀ m, 0 ≤ p m) (hsum : Summable p)
    (P : Distribution (Sphere d)) :
    kernelEnergy (dotProductKernel p) (sphereUniform d hDim)
      ≤ kernelEnergy (dotProductKernel p) P

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
