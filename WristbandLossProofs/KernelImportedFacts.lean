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
- Park, J.; Parkkonen, J. *Lecture notes on Riemannian geometry*.
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

/-- Schur product theorem for kernel functions — product of PSD kernels
    is PSD on the product space. -/
axiom productKernel_posSemiDef_imported
    {X : Type*} {Y : Type*}
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsPosSemiDefKernel Kx)
    (hKy : IsPosSemiDefKernel Ky) :
    IsPosSemiDefKernel (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)

/-- Neumann radial kernel on `[0,1]` is PSD — heat-kernel eigenexpansion
    with nonnegative weights (arXiv:1703.10541). -/
axiom kernelRadNeumann_posSemiDef_imported
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β)

/-- Neumann radial kernel has constant potential under `uniform01` —
    Markov mass conservation under reflecting BC (arXiv:1703.10541). -/
axiom neumannPotential_constant_imported
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ, HasConstantPotential (kernelRadNeumann β) uniform01 c

/-- Angular Gaussian kernel is universal on the sphere for `d ≥ 2` —
    Steinwart (2001). -/
axiom kernelAngChordal_universal
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsUniversalKernel (kernelAngChordal (d := d) β α)

/-- Neumann radial kernel is universal on `[0,1]`. -/
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

/-- Universal kernels are characteristic — Gretton (2012);
    Sriperumbudur (2011). -/
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
