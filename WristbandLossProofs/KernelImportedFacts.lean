import WristbandLossProofs.KernelPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! # Imported Kernel Facts

External mathematical results assumed without Lean proof. Each axiom
transcribes one cited theorem. Local scaffolding belongs in
`KernelFoundations.lean`.

References:
- Bogachev, V.I.; Kroese, D.P. *Heat kernels on bounded intervals and
  Neumann reflection series*.
- Fukumizu, K. *Elements of kernel theory* (lecture notes).
- Gretton, A. et al. (2012). "A kernel two-sample test."
  *J. Mach. Learn. Res.* 13.
- Horn, R.A.; Johnson, C.R. (2013). *Matrix Analysis.* 2nd ed.
- Micchelli, C.A.; Xu, Y.; Zhang, H. (2006). "Universal Kernels."
  *J. Mach. Learn. Res.* 7, 2651–2667.
- Park, J.; Parkkonen, J. *Lecture notes on Riemannian geometry*.
- Schur, J. (1911). "Bemerkungen zur Theorie der beschränkten
  Bilinearformen mit unendlich vielen Veränderlichen."
  *J. Reine Angew. Math.* 140.
- Sriperumbudur, B.K. et al. (2011). "Universality, characteristic
  kernels and RKHS embedding of measures."
  *J. Mach. Learn. Res.* 12.
- Stein, E.M.; Shakarchi, R. (2003). *Fourier Analysis: An Introduction.*
  Princeton Lectures in Analysis, Vol. I. Princeton University Press.
- Steinwart, I. (2001). "On the influence of the kernel on the
  consistency of support vector machines." *J. Mach. Learn. Res.* 2.
- Steinwart, I.; Christmann, A. (2008). *Support Vector Machines.* Springer.
- Tropp, J.A. (2022). *Matrix Analysis Lecture Notes.* Caltech.
- arXiv:1703.10541 — *Heat kernels on Neumann interval and PSD.*
-/

/-! ## Axioms -/

/-- Angular Gaussian kernel on the sphere is PSD — Bochner + restriction. -/
axiom kernelAngChordal_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (kernelAngChordal (d := d) β α)

/-- Real-form Jacobi theta transformation, period 2 — Stein & Shakarchi (2003). -/
axiom gaussian_periodization_cosine_series_period_two
    (β z : ℝ) (hβ : 0 < β) :
    (∑' n : ℤ, Real.exp (-β * (z - 2 * n) ^ 2))
      =
    (Real.sqrt (Real.pi / β) / 2) *
      (1 + 2 * ∑' k : ℕ,
        Real.exp (-(((k + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2) / (4 * β)) *
          Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * z))

/-- Schur product theorem for symmetric PSD kernels — Schur (1911); Horn &
    Johnson (2013) §7.5. The Hadamard (entrywise) product of two
    symmetric positive semidefinite matrices is positive semidefinite.

    For finitely many points `pᵢ = (xᵢ, yᵢ)`, the product Gram matrix is
    the Hadamard product of the factor Gram matrices; symmetry of `Kx`
    and `Ky` makes those matrices self-adjoint, and `IsPosSemiDefKernel`
    supplies nonnegative quadratic forms.

    Mathlib reference: `Matrix.PosSemidef.hadamard` in
    `Mathlib/Analysis/Matrix/Order.lean`. -/
axiom productKernel_posSemiDef_imported
    {X : Type*} {Y : Type*}
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx_symm : IsSymmetricKernel Kx)
    (hKy_symm : IsSymmetricKernel Ky)
    (hKx : IsPosSemiDefKernel Kx)
    (hKy : IsPosSemiDefKernel Ky) :
    IsPosSemiDefKernel (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)

/-- Angular Gaussian kernel is universal on the sphere for `d ≥ 2`.

    Underlying source theorem:
    Steinwart, I. (2001). "On the influence of the kernel on the
    consistency of support vector machines." *J. Mach. Learn. Res.* 2.

    ## Fragilities (this axiom is NOT source-exact verbatim)

    1. **Project-specific shape.** The Lean statement asserts the
       specialization `IsUniversalKernel (kernelAngChordal ...)`
       directly, not Steinwart's more general universality theorem.

    2. **Predicate divergence.** The project's `IsUniversalKernel`
       records **kernel-section density** in `C(X, ℝ)`. The source-side
       universality story is typically phrased via feature/RKHS density;
       using the project predicate directly hides that bridge.

    3. **Hidden assumptions.** The source argument relies on the compact
       sphere domain, continuity of the feature/kernel representation,
       and uniform convergence/closure properties needed to pass from
       the representation to density. These hold for `Sphere d` with
       `d ≥ 2`, but they are not exposed in this axiom signature.

    4. **Blocking gap for derivation.** Replacing this axiom with a
       derived theorem would require a spherical-harmonics density
       theorem on `Sphere d`, which the project does not currently
       formalize. -/
axiom kernelAngChordal_universal
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsUniversalKernel (kernelAngChordal (d := d) β α)

/-- Neumann radial kernel on `[0,1]` is universal.

    Underlying source theorem:
    Micchelli, C.A.; Xu, Y.; Zhang, H. (2006). "Universal Kernels."
    *J. Mach. Learn. Res.* 7, 2651–2667, Theorem 7 — a kernel with
    uniformly convergent feature expansion `K(x,y) = ∑ⱼ φⱼ(x)·φⱼ(y)`
    on a compact `X` is universal iff the feature set `{φⱼ}` is
    universal in `C(X, ℝ)`.

    Specialized here with features `{1, cos(π·), cos(2π·), …}` on
    `[0,1]` and the cosine-expansion coefficients from
    `kernelRadNeumann_hasCosineExpansion`.

    ## Fragilities (this axiom is NOT source-exact verbatim)

    1. **Project-specific shape.** The Lean statement asserts the
       conclusion `IsUniversalKernel (kernelRadNeumann β)` directly,
       not the source's general iff statement. To match the source
       verbatim one would import the general theorem and derive the
       specialization.

    2. **Predicate divergence.** The project's `IsUniversalKernel`
       (KernelPrimitives.lean) is **kernel-section density** in
       `C(X, ℝ)`; Micchelli–Xu–Zhang's "universal" is **feature-span
       density**. These are equivalent on compact `X` via Theorem 7,
       but the project predicate is consumed in kernel-section form.

    3. **Hidden assumptions.** The source theorem requires (i) compact
       `X`, (ii) continuous features, (iii) uniform convergence of the
       expansion on `X × X`. All three hold for `[0,1]` with the
       cosine features and Gaussian-decay coefficients, but none are
       exposed in this axiom signature. A derivation would need to
       discharge them explicitly.

    4. **Blocking sorry for derivation.** Replacing this axiom with a
       derived theorem requires
       `cosine_span_uniformly_dense_on_unitInterval` (the existing
       project `sorry` in `KernelFoundations.lean`) — the
       Stone–Weierstrass / Chebyshev step that closes feature
       universality on `[0,1]`.

    Until that sorry is closed, keeping the specialization as an
    imported fact is consistent with the project's other kernel-specific
    universality imports (`kernelAngChordal_universal` and
    `productKernel_universal_compact_imported`). -/
axiom kernelRadNeumann_universal
    (β : ℝ) (hβ : 0 < β) :
    IsUniversalKernel (kernelRadNeumann β)

/-- Tensor-product universality on compact spaces — Blanchard, Lee, Scott
    (2011), "Generalizing from Several Related Classification Tasks to a
    New Unlabeled Sample," NeurIPS 24, Lemma 5.2:
    "Let `Ω, Ω'` be two compact spaces and `k, k'` be kernels on `Ω, Ω'`,
    respectively. If `k, k'` are both universal, then the product kernel
    `k̄((x,x'),(y,y')) := k(x,y)·k'(x',y')` is universal on `Ω × Ω'`."

    Source proof: the product RKHS contains tensor products of factor-RKHS
    functions; Stone–Weierstrass on the compact product `Ω × Ω'` gives
    uniform density. The compactness hypothesis is essential to the
    Stone–Weierstrass step. -/
axiom productKernel_universal_compact_imported
    {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsUniversalKernel Kx)
    (hKy : IsUniversalKernel Ky) :
    IsUniversalKernel (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)

/-- Universal kernels are characteristic.

    Underlying source theorems:
    Gretton, A. et al. (2012). "A kernel two-sample test."
    *J. Mach. Learn. Res.* 13.
    Sriperumbudur, B.K. et al. (2011). "Universality, characteristic
    kernels and RKHS embedding of measures." *J. Mach. Learn. Res.* 12.

    ## Fragilities (this axiom is NOT source-exact verbatim)

    1. **Project-specific shape.** The source results are stated in
       terms of RKHS mean embeddings of measures. The Lean axiom asserts
       the direct implication `IsUniversalKernel K →
       IsCharacteristicKernel K` on project predicates.

    2. **Predicate divergence.** The source-side "characteristic"
       property is injectivity of the kernel mean embedding. The
       project's `IsCharacteristicKernel` is the surface predicate
       consumed downstream by `wristbandKernelNeumann_characteristic`
       and related theorems.

    3. **Blocking gap for derivation.** Discharging this axiom would
       require a formalized RKHS embedding theory in Lean/Mathlib,
       which the project does not currently have. -/
axiom universal_implies_characteristic
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (K : X → X → ℝ) (hK : IsUniversalKernel K) :
    IsCharacteristicKernel K

/-- Orthogonal group acts transitively on the sphere `S^{d-1}` for `d ≥ 2`. -/
axiom orthogonal_group_transitive_on_sphere
    (d : ℕ) (hDim : 2 ≤ d) :
    ∀ u v : Sphere d,
      ∃ O : (Vec d) ≃ₗᵢ[ℝ] Vec d, rotateSphere O u = v

/-- Squared MMD is nonnegative for PSD kernels — Gretton (2012);
    Sriperumbudur (2011). -/
axiom mmdSq_nonneg
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (hK : IsPosSemiDefKernel K)
    (P Q : Distribution X) :
    mmdSq K P Q ≥ 0

end WristbandLossProofs
