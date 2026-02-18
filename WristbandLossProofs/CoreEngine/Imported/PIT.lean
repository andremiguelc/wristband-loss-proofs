import WristbandLossProofs.CoreEngine.Geometry
import WristbandLossProofs.CoreEngine.PITDefs

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

/-!
# Imported PIT Skeleton

The forward and reverse PIT theorems are left as theorem skeletons while CDF tooling
is finalized against Mathlib APIs.

Theorem shape tracked here:
\[
X \sim F \ \text{continuous} \implies U := F(X) \sim \mathrm{Unif}(0,1).
\]
Conversely, with generalized inverse \(F^{-1}\):
\[
U \sim \mathrm{Unif}(0,1) \implies F^{-1}(U) \sim F.
\]

External bibliography (non-Mathlib):

- Lancaster University. *MATH230 Notes*, "Probability Integral Transformation"
  (Theorem 4.3.1 on linked page).
  URL: https://www.lancaster.ac.uk/~prendivs/accessible/math230/math230_notes.tex/Ch4.S3.html
-/

/--
If `X` has continuous CDF `F`, then `F(X)` has uniform law on `[0,1]`.
-/
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hF : IsContinuousCDFFor μ F) :
    pushforward F μ = uniform01 := by
  -- Deferred in this pass: concrete CDF formalization details.
  sorry

/--
Reverse PIT used in the backward direction of Wristband Equivalence.

If `F(X)` is uniform and `F` is the strictly increasing CDF of `targetLaw`,
then `X` must follow `targetLaw`.
-/
theorem probabilityIntegralTransform_reverse
    (targetLaw observedLaw : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hCDF : IsContinuousCDFFor targetLaw F)
    (hStrict : IsStrictlyIncreasingCDFFor targetLaw F)
    (hUniform : pushforward F observedLaw = uniform01) :
    observedLaw = targetLaw := by
  -- Deferred for the same reason as `probabilityIntegralTransform`.
  sorry

end WristbandLossProofs
