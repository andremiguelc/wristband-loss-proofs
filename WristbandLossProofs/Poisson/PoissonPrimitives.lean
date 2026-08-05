import WristbandLossProofs.KernelPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Primitives

Definitions for the randomised replacement of the angular truncation.

The spectral fast path keeps angular degrees `ℓ ≤ L` exactly. That kernel has
finite rank, so its energy factors through finitely many numbers and cannot
separate all distributions — the defect formalised by `HasFiniteRank` and
`IsBlindAt` below.

The replacement keeps no degrees at all. Writing the angular kernel as a power
series in `⟪u, u'⟫`,

  `kernelAngChordal β α u u' = ∑' m, poissonWeight (2βα²) m * (sphereInner u u')ᵐ`,

the coefficients are non-negative and sum to `1`, so they are a probability
distribution over the exponent `m`. A single draw of `m` together with `m` sign
vectors gives a feature whose expected product is that series — no basis of the
degree-`ℓ` block is ever enumerated, which is where the `d^ℓ` cost lived.

`RademacherDraw` is that draw, and `randomMaclaurinFeature` that feature. The
law they are drawn from is supplied by `PoissonImportedFacts`; the expansion
itself is derived in `PoissonFoundations`.
-/

/-! ### Finite rank and blindness -/

/-- `K` has rank at most `r`: it is a sum of `r` feature products. Any
degree-truncated angular kernel has this with `r = N_{≤L} = ∑_{ℓ≤L} N_ℓ`. -/
def HasFiniteRank {X : Type*} (K : X → X → ℝ) (r : ℕ) : Prop :=
  ∃ f : Fin r → X → ℝ, ∀ x y, K x y = ∑ i : Fin r, f i x * f i y

/-- Two distributions agree on the features `f`. When `f` is a rank witness for
`K`, this is exactly the condition under which `K` cannot tell them apart. -/
def AgreeOnFeatures {X : Type*} [MeasurableSpace X] {r : ℕ}
    (f : Fin r → X → ℝ) (P Q : Distribution X) : Prop :=
  ∀ i : Fin r, ∫ x, f i x ∂(P : Measure X) = ∫ x, f i x ∂(Q : Measure X)

/-- `K` is blind at `μ₀` if some other distribution has the same energy.
This is the property that makes the truncated loss unable to see a deviation:
`P` sits at the minimum without being the target. -/
def IsBlindAt {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (μ₀ : Distribution X) : Prop :=
  ∃ P : Distribution X, P ≠ μ₀ ∧ kernelEnergy K P = kernelEnergy K μ₀

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

A sampler is a randomised feature map together with the law of its draw. The
kernel it represents is the expected product of two of its features; it is
*unbiased* for `K` when that expectation is `K` on the nose. -/

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

/-- Wristband kernel built from a sampled angular factor. The radial factor is
unchanged: it is a one-dimensional coordinate, so its modes carry no
multiplicity and there is nothing to truncate away. -/
def sampledWristbandKernel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β : ℝ) : Wristband d → Wristband d → ℝ :=
  fun w w' => sampledKernel S w.1 w'.1 * kernelRadNeumann β w.2 w'.2

end WristbandLossProofs
