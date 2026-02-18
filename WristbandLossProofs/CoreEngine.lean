import Mathlib

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-!
# Core Probabilistic Engine (Scaffold)

This file is the first Lean scaffold for the correctness framework in
`docs/wristband_proof_plan.md`.
It is intentionally tutorial-oriented and intentionally incremental:

- we define the geometric objects used by the wristband map,
- we use concrete Mathlib measures for distributions and pushforwards,
- we state theorem skeletons with detailed proof roadmaps in comments.

Why use concrete measures already at this stage?
This removes "plumbing axioms" and keeps the imported assumptions focused only
on genuine mathematics that we still plan to prove or cite explicitly.
-/

/-! ## Basic Geometric Types -/

/-- Ambient Euclidean space `ℝ^d`, encoded as `EuclideanSpace ℝ (Fin d)`. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The unit sphere as a subtype: vectors with norm exactly `1`. -/
def Sphere (d : ℕ) : Type := {u : Vec d // ‖u‖ = 1}

/-- Nonzero vectors, used because `z / ‖z‖` is undefined at the origin. -/
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}

/--
The closed unit interval `[0,1]` as a subtype of real numbers.

This is the same underlying type as Mathlib's `I` (from `open scoped unitInterval`),
written explicitly to keep the file self-contained and readable.
-/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-- Wristband space: direction coordinate plus radial-percentile coordinate. -/
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval

/-!
The following instances are all definitional consequences of subtype/product
constructions. We register them explicitly so later declarations stay readable
and typeclass search remains predictable in this scaffold.
-/

instance instMeasurableSpaceSphere (d : ℕ) : MeasurableSpace (Sphere d) := by
  unfold Sphere
  infer_instance

instance instMeasurableSpaceVecNZ (d : ℕ) : MeasurableSpace (VecNZ d) := by
  unfold VecNZ
  infer_instance

instance instMeasurableSpaceUnitInterval : MeasurableSpace UnitInterval := by
  unfold UnitInterval
  infer_instance

/-! ## Concrete Distribution Interface (Mathlib Measures) -/

universe u v w

/--
`Distribution α` means "a probability law on `α`".

At this stage we model laws as measures. Later we can enforce probability
normalization at the type level (`ProbabilityMeasure`) where useful.
-/
abbrev Distribution (α : Type u) [MeasurableSpace α] : Type u := Measure α

/--
Pushforward of a distribution along a random-variable map.

For a function `f : α → β` and law `μ` on `α`, this is the law of `f(X)` when `X ∼ μ`.
-/
def pushforward {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    (α → β) → Distribution α → Distribution β
  | f, μ => Measure.map f μ

/--
Product law constructor for independent couplings.

`productLaw μ ν` is the measure-theoretic product `μ.prod ν`.
-/
def productLaw {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] :
    Distribution α → Distribution β → Distribution (α × β)
  | μ, ν => μ.prod ν

/--
Independence encoded by the usual identity:
joint law equals product of marginals.
-/
def IndepLaw {Ω : Type u} {α : Type v} {β : Type w}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Distribution Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  pushforward (fun ω => (X ω, Y ω)) μ =
    productLaw (pushforward X μ) (pushforward Y μ)

/-! ## Wristband Construction Primitives -/

/-- Uniform law on the sphere (Haar probability), imported for now. -/
axiom sphereUniform (d : ℕ) : Distribution (Sphere d)

/--
Uniform law on `[0,1]`.

Mathlib already equips the unit interval subtype with its canonical probability
measure, so we can use `volume` directly here.
-/
def uniform01 : Distribution UnitInterval := (volume : Measure UnitInterval)

/-- Target wristband law `μ₀ = σ_{d-1} ⊗ λ`. -/
def wristbandUniform (d : ℕ) : Distribution (Wristband d) :=
  productLaw (sphereUniform d) uniform01

/-- Squared radius of a nonzero vector, stored in nonnegative reals. -/
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal :=
  ⟨‖z.1‖ ^ 2, by positivity⟩

/--
Direction map `z ↦ z / ‖z‖` into the sphere.

We keep this as imported data in the first scaffold to avoid distracting from
the theorem architecture.
-/
axiom direction {d : ℕ} : VecNZ d → Sphere d

/--
Chi-square CDF map used by the wristband transform:
`s ↦ P(d/2, s/2)` landing in `[0,1]`.
-/
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval

/-- The wristband map `Φ(z) = (direction(z), CDF(radiusSq(z)))`. -/
def wristbandMap (d : ℕ) (z : VecNZ d) : Wristband d :=
  (direction (d := d) z, chiSqCDFToUnit d (radiusSq z))

/-- Pushforward wristband law `P_Q = Φ_#Q`. -/
def wristbandLaw (d : ℕ) (Q : Distribution (VecNZ d)) : Distribution (Wristband d) :=
  pushforward (wristbandMap d) Q

/-! ## Imported Gaussian Facts (Gaussian Polar Decomposition Package) -/

/-!
### Axiom Ledger (Current Status)

At this stage, all *infrastructure* objects (measures, pushforwards, products, uniform
law on `[0,1]`) are concrete Mathlib definitions.

The remaining axioms are only the mathematically substantive imported facts we still need
to formalize or reference:

1. `sphereUniform` and its rotation invariance;
2. Gaussian polar decomposition facts (`direction`, chi-square radius law, independence);
3. abstract PIT hypotheses (`IsContinuousCDFFor`, `IsStrictlyIncreasingCDFFor`) used by
   theorem skeletons.

This separation keeps the scaffold honest: axioms now correspond to actual theorem debt,
not missing API plumbing.
-/

/--
Standard Gaussian law, encoded on nonzero vectors for the wristband map domain.
-/
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)

/-- The chi-square law for squared radius. -/
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal

/-- Imported Gaussian polar fact: direction is uniform. -/
axiom gaussianPolar_direction_uniform (d : ℕ) :
    pushforward (direction (d := d)) (gaussianNZ d) = sphereUniform d

/-- Imported Gaussian polar fact: squared radius has chi-square law. -/
axiom gaussianPolar_radius_chiSq (d : ℕ) :
    pushforward (radiusSq (d := d)) (gaussianNZ d) = chiSqRadiusLaw d

/-- Imported Gaussian polar fact: direction and radius are independent. -/
axiom gaussianPolar_independent (d : ℕ) :
    IndepLaw (gaussianNZ d) (direction (d := d)) (radiusSq (d := d))

/-! ## Probability Integral Transform Skeleton -/

/-- `F` is the continuous CDF associated to a target one-dimensional law. -/
axiom IsContinuousCDFFor : Distribution NNReal → (NNReal → UnitInterval) → Prop

/-- `F` is strictly increasing (needed for reverse PIT). -/
axiom IsStrictlyIncreasingCDFFor : Distribution NNReal → (NNReal → UnitInterval) → Prop

/--
**Theorem (Probability Integral Transform).**

If `X` has continuous CDF `F`, then `F(X)` has uniform law on `[0,1]`.
-/
theorem probabilityIntegralTransform
    (μ : Distribution NNReal)
    (F : NNReal → UnitInterval)
    (hF : IsContinuousCDFFor μ F) :
    pushforward F μ = uniform01 := by
  -- Tutorial roadmap:
  -- 1. Introduce the generalized inverse/quantile function.
  -- 2. Compute `P(F(X) ≤ y)` for each `y ∈ [0,1]`.
  -- 3. Use continuity of `F` to close the CDF identity.
  -- 4. Identify the transformed law with `Unif[0,1]`.
  --
  -- Deferred in this first pass: concrete CDF formalization details.
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
  -- Tutorial roadmap:
  -- 1. Translate uniformity of `F(X)` into a statement about the observed CDF.
  -- 2. Use strict monotonicity to invert `F` on its range.
  -- 3. Recover the same one-dimensional distribution function.
  -- 4. Conclude equality of laws.
  --
  -- Deferred for the same reason as `probabilityIntegralTransform`.
  sorry

/-! ## Spherical Law Determined by Radius Skeleton -/

/-- Reconstruct a vector from `(radius, direction)` by scalar multiplication. -/
def radialReconstruct (d : ℕ) : NNReal × Sphere d → Vec d
  | (r, u) => (r : ℝ) • u.1

/--
Law generated by:
1. sample radius from `radiusLaw`,
2. sample direction uniformly from the sphere,
3. set `Z = R • U`.
-/
def sphericalLaw (d : ℕ) (radiusLaw : Distribution NNReal) : Distribution (Vec d) :=
  pushforward (radialReconstruct d) (productLaw radiusLaw (sphereUniform d))

/-- Rotation-invariance predicate for laws on `ℝ^d`. -/
def IsRotationInvariant (d : ℕ) (μ : Distribution (Vec d)) : Prop :=
  ∀ O : (Vec d) ≃ₗᵢ[ℝ] Vec d, pushforward (fun z => O z) μ = μ

/-- Rotate a point on the sphere via a linear isometric equivalence. -/
def rotateSphere {d : ℕ} (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) (u : Sphere d) : Sphere d :=
  ⟨O u.1, by
    calc
      ‖O u.1‖ = ‖u.1‖ := by exact O.norm_map u.1
      _ = 1 := by simpa using u.property⟩

/-- Imported sphere invariance under orthogonal maps. -/
axiom sphereUniform_rotationInvariant
    (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateSphere O) (sphereUniform d) = sphereUniform d

/--
**Lemma (Spherical law, rotation-invariance part):**
spherical construction is rotation-invariant.
-/
theorem sphericalLaw_rotationInvariant
    (d : ℕ)
    (radiusLaw : Distribution NNReal) :
    IsRotationInvariant d (sphericalLaw d radiusLaw) := by
  intro O
  -- Tutorial roadmap:
  -- 1. Show `O (r • u) = r • (O u)` pointwise.
  -- 2. Push this identity through the distribution construction.
  -- 3. Use `sphereUniform_rotationInvariant`.
  -- 4. Conclude the final law is unchanged by `O`.
  --
  -- Deferred while we keep the distribution layer abstract.
  sorry

/--
**Lemma (Spherical law, radius-identification part):**
once direction is uniform/independent,
the law of `Z = R•U` is fully determined by the law of `R`.
-/
theorem sphericalLaw_determinedByRadius
    (d : ℕ)
    {radiusLaw₁ radiusLaw₂ : Distribution NNReal}
    (hRadius : radiusLaw₁ = radiusLaw₂) :
    sphericalLaw d radiusLaw₁ = sphericalLaw d radiusLaw₂ := by
  simp [sphericalLaw, hRadius]

/-! ## Wristband Equivalence Skeleton -/

/--
**Theorem (Wristband equivalence, forward direction: `Q = γ → P_Q = μ₀`).**

Roadmap:
1. Use Gaussian polar decomposition (imported package).
2. Apply Probability Integral Transform (PIT) to the chi-square radius.
3. Transfer independence through the CDF map.
4. Identify the wristband law as `wristbandUniform`.
-/
theorem wristbandEquivalence_forward (d : ℕ) :
    wristbandLaw d (gaussianNZ d) = wristbandUniform d := by
  -- Deferred until PIT + independence lemmas are concretized.
  sorry

/--
**Theorem (Wristband equivalence, backward direction: `P_Q = μ₀ → Q = γ`).**

Roadmap:
1. Read off uniform marginals and independence from `P_Q = μ₀`.
2. Use reverse PIT to recover the chi-square radius law.
3. Apply Spherical law determined by radius lemma.
4. Match Gaussian polar data and conclude `Q = γ`.
-/
theorem wristbandEquivalence_backward
    (d : ℕ)
    (Q : Distribution (VecNZ d))
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by
  -- Deferred until PIT reverse direction is implemented concretely.
  sorry

/--
**Theorem (full equivalence).**

This is the core logical bridge used later by kernel/energy minimization results.
-/
theorem wristbandEquivalence
    (d : ℕ)
    (Q : Distribution (VecNZ d)) :
    wristbandLaw d Q = wristbandUniform d ↔ Q = gaussianNZ d := by
  constructor
  · intro hUniform
    exact wristbandEquivalence_backward d Q hUniform
  · intro hGaussian
    simpa [hGaussian] using wristbandEquivalence_forward d

end WristbandLossProofs
