import WristbandLossProofs.KernelPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Primitives

Definitions for computing the angular kernel by sampling rather than by
enumerating a basis.

Write the angular kernel as a power series in `⟪u, u'⟫`:

  `kernelAngChordal β α u u' = ∑' m, poissonWeight (2βα²) m * (sphereInner u u')ᵐ`.

The coefficients are non-negative, and they sum to `1`. So they are a probability
distribution over the exponent `m`. Draw one `m` together with `m` sign vectors.
That gives a feature, and the mean of its product is that series. No spherical
harmonic occurs, and the method enumerates no degree block.

`RademacherDraw` is that draw, and `randomMaclaurinFeature` is that feature.
`PoissonImportedFacts` gives the law of the draw. `PoissonFoundations` derives the
expansion.
-/

/-! ### Dot-product kernels and their coefficients -/

/-- The `m`-th Poisson weight with mean `c`: `e^{-c} cᵐ / m!`. These are the
Maclaurin coefficients of `kernelAngChordal` with `c = 2βα²`. -/
def poissonWeight (c : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-c) * c ^ m / (Nat.factorial m)

/-- A kernel on the sphere depending on the two points only through their inner
product, presented by its power-series coefficients `p`. -/
def dotProductKernel {d : ℕ} (p : ℕ → ℝ) (u u' : Sphere d) : ℝ :=
  ∑' m : ℕ, p m * (sphereInner u u') ^ m

/-! ### The random feature

The construction is due to Kar-Karnick; see `PoissonImportedFacts`. One draw is
an exponent `m` together with `m` vectors, and the feature is the product of the
`m` projections of the point onto them. The scaling `√(∑' p)` is what makes the
expected product reproduce `p` rather than the normalised distribution `p / ∑' p`
actually drawn from. -/

/-- One draw: an exponent `m`, together with `m` vectors in `ℝ^d`. Under the law
of `PoissonImportedFacts` the exponent is Poisson and the vectors have
independent `±1` coordinates. -/
abbrev RademacherDraw (d : ℕ) : Type := Σ m : ℕ, Fin m → Vec d

/-- The random feature of a draw: `√(∑' p) · ∏_{i < m} ⟪wᵢ, u⟫`. -/
def randomMaclaurinFeature {d : ℕ} (p : ℕ → ℝ)
    (ω : RademacherDraw d) (u : Sphere d) : ℝ :=
  Real.sqrt (∑' m : ℕ, p m) * ∏ i : Fin ω.1, @inner ℝ (Vec d) _ (ω.2 i) u.1

/-! ### Samplers

A sampler holds a randomised feature map and the law of its draw. The mean product
of two of its features gives the kernel that it represents. The sampler is
*unbiased* for `K` when that mean equals `K` exactly. -/

/-- An angular sampler: a randomised feature map `feat ω : Sphere d → ℝ` with
draw law `law` on `Ω`. -/
structure AngularSampler (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  law : Distribution Ω
  feat : Ω → Sphere d → ℝ

/-- The kernel a sampler represents *in expectation over the draw*. -/
def sampledKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) : Sphere d → Sphere d → ℝ :=
  fun u u' => ∫ ω, S.feat ω u * S.feat ω u' ∂(S.law : Measure Ω)

/-- Unbiasedness: the sampler reproduces `K` exactly in expectation. -/
def IsUnbiasedFor {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (K : Sphere d → Sphere d → ℝ) : Prop :=
  ∀ u u', sampledKernel S u u' = K u u'

/-- Wristband kernel with a sampled angular factor. The radial factor does not
change. It is a one-dimensional coordinate, so its modes have no multiplicity. -/
def sampledWristbandKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) : Wristband d → Wristband d → ℝ :=
  fun w w' => sampledKernel S w.1 w'.1 * kernelRadNeumann β w.2 w'.2

end WristbandLossProofs
