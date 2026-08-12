import WristbandLossProofs.Poisson.PoissonPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Poisson Imported Facts

External results with no Lean proof, plus the definitions extracted from them.
The branch derives everything else.

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
definiteness, Björck for the energy minimum. Open: the result numbers. Also, does
Björck cover a general kernel with non-negative coefficients, or only the Riesz
family? And does the source give the minimum for `S^{d-1}` at every `d ≥ 1`?
-/

/-! ## Axioms -/

/-- Kar-Karnick. Take a dot-product kernel whose Maclaurin coefficients are
    non-negative and summable. One law draws the exponent from the normalised
    coefficients, and draws the vectors with independent `±1` coordinates. Under
    that law, the mean product of two `randomMaclaurinFeature`s equals the kernel.

    Specialization: this axiom names `Sphere d` and the explicit feature map of
    `PoissonPrimitives`. So it imports only the law, not the construction.

    Fragilities. The source builds the estimator and proves its unbiasedness. We
    assemble the product measure on the sigma-type `RademacherDraw`.
    Non-negativity of the coefficients is the hypothesis of the source. This
    axiom adds summability, because the feature carries the factor `√(∑' p)`. The
    source says nothing about variance, which holds the real cost. -/
axiom randomMaclaurin_law_exists
    (d : ℕ) (p : ℕ → ℝ) (hp : ∀ m, 0 ≤ p m) (hsum : Summable p) :
    ∃ μ : Distribution (RademacherDraw d),
      ∀ u u' : Sphere d,
        ∫ ω, randomMaclaurinFeature p ω u * randomMaclaurinFeature p ω u'
            ∂(μ : Measure (RademacherDraw d))
          = dotProductKernel p u u'

/-- Schoenberg, Björck: the uniform measure minimizes the energy of a
    dot-product kernel whose Maclaurin coefficients are non-negative.

    Such coefficients make the kernel positive definite on the sphere. The kernel
    is zonal, so the uniform measure has a constant potential. Together, those two
    facts put the minimum at the uniform measure.

    Fragilities. This axiom speaks at the level of the energy. So it imports the
    constant-potential step, in place of a derivation from
    `energy_eq_mmdSq_of_constantPotential`. It also assumes that both integrals of
    `kernelEnergy` exist. It states their values, not their existence. And it gives
    a minimum, not a modulus: nothing here says how fast the energy grows away from
    the uniform measure. -/
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
