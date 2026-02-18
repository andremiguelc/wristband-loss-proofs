import WristbandLossProofs.CoreEngine.Geometry
import WristbandLossProofs.CoreEngine.SphereUniform

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

/-!
# Imported Gaussian Polar Package

Mathematical content represented here as imported theorem debt:

Let \(G \sim \mathcal{N}(0, I_d)\), and define
\[
R := \|G\|, \qquad \Theta := \frac{G}{\|G\|}.
\]
Imported facts:
\[
\Theta \sim \mathrm{Unif}(S^{d-1}), \qquad R \perp \Theta, \qquad
R^2 = \sum_{i=1}^d G_i^2 \sim \chi^2_d.
\]

Chi-square CDF (also imported here):
\[
F_{\chi^2_d}(x) =
\frac{\gamma\!\left(\frac d2,\frac x2\right)}{\Gamma\!\left(\frac d2\right)}.
\]

External bibliography (non-Mathlib):

- NIST/SEMATECH (2012). *e-Handbook of Statistical Methods*, "Chi-Square Distribution".
  URL: https://www.itl.nist.gov/div898/handbook/eda/section3/eda3666.htm

- Vershynin, R. (draft, 2nd ed.).
  *High-Dimensional Probability: An Introduction with Applications in Data Science*.
  URL: https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-book.pdf
-/

/-- Standard Gaussian law, encoded on nonzero vectors for the wristband map domain. -/
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)

/-- The chi-square law for squared radius. -/
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal

/-- Chi-square CDF map used by the wristband transform, landing in `[0,1]`. -/
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval

/-- Imported Gaussian polar fact: direction is uniform. -/
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) = sphereUniform d

/-- Imported Gaussian polar fact: squared radius has chi-square law. -/
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) = chiSqRadiusLaw d

/-- Imported Gaussian polar fact: direction and radius are independent. -/
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d) (direction (d := d)) (radiusSq (d := d))

end WristbandLossProofs
