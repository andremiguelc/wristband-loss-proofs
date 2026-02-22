import WristbandLossProofs.KernelPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Imported Kernel Facts (External Only)

This file contains only externally imported theorem-sized facts stated as
`axiom`s. Any local theorem/lemma scaffolding belongs in
`KernelFoundations.lean`.
-/

/-! ### PSD building blocks -/

/-- Gaussian RBF (restricted to sphere) is PSD.

Source direction:
- Bochner theorem + Gaussian characteristic function.
- Restriction of PD kernels to subsets.

URL: https://www.ism.ac.jp/~fukumizu/H20_kernel/Kernel_7_theory.pdf -/
axiom kernelAngChordal_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (kernelAngChordal (d := d) β α)

/-- Neumann kernel admits a cosine-eigenfunction expansion with nonnegative
weights.

This is the imported bridge from image-sum to spectral arguments.

URL: https://people.smp.uq.edu.au/DirkKroese/ps/bogrkr.pdf -/
axiom kernelRadNeumann_hasCosineExpansion
    (β : ℝ) (hβ : 0 < β) :
    ∃ (a0 : ℝ) (a : ℕ → ℝ),
      0 ≤ a0 ∧
      (∀ k : ℕ, 0 ≤ a k) ∧
      (∀ t t' : UnitInterval,
        kernelRadNeumann β t t' =
          a0 +
            ∑' k : ℕ,
              a k *
                Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t : ℝ)) *
                Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi * (t' : ℝ)))

/-- Product closure for PSD kernels (kernel-level Schur/Hadamard route).

If `Kx` and `Ky` are PSD kernels, then their product kernel on `X × Y` is PSD.

Source direction:
- Kernel closure properties for positive definite kernels (product closure).
- Schur product theorem on Gram matrices.

URLs:
- https://www.ism.ac.jp/~fukumizu/Kyushu2008/Kernel_elements_2.pdf
- https://tropp.caltech.edu/notes/Tro22-Matrix-Analysis-LN.pdf -/
axiom productKernel_posSemiDef_imported
    {X : Type*} {Y : Type*}
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsPosSemiDefKernel Kx)
    (hKy : IsPosSemiDefKernel Ky) :
    IsPosSemiDefKernel (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)

/-- Neumann radial kernel on `[0,1]` is PSD for `β > 0`.

Source direction:
- Heat-kernel eigenfunction expansion with nonnegative weights.
- Neumann interval cosine-eigenbasis specialization.

URLs:
- https://arxiv.org/abs/1703.10541
- https://arxiv.org/pdf/1703.10541 -/
axiom kernelRadNeumann_posSemiDef_imported
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β)

/-- Neumann radial kernel has constant potential under `uniform01`.

Source direction:
- Markov/heat-kernel mass conservation under Neumann boundary conditions.
- Equivalent spectral view: only the constant mode survives integration.

URLs:
- https://arxiv.org/abs/1703.10541
- https://arxiv.org/pdf/1703.10541 -/
axiom neumannPotential_constant_imported
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ, HasConstantPotential (kernelRadNeumann β) uniform01 c

/-! ### Universality / characteristic building blocks -/

/-- Angular Gaussian kernel is universal on sphere (`d ≥ 2` guard kept to
match project theorem signatures).

URL: https://www.jmlr.org/papers/volume2/steinwart01a/steinwart01a.pdf -/
axiom kernelAngChordal_universal
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsUniversalKernel (kernelAngChordal (d := d) β α)

/-- Neumann radial kernel is universal on `[0,1]`.

URL: https://bimsa.net/doc/notes/20809.pdf -/
axiom kernelRadNeumann_universal
    (β : ℝ) (hβ : 0 < β) :
    IsUniversalKernel (kernelRadNeumann β)

/-- Tensor-product universality from factor universality.

URL: https://www.jmlr.org/papers/volume18/17-492/17-492.pdf -/
axiom productKernel_universal
    {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsUniversalKernel Kx)
    (hKy : IsUniversalKernel Ky) :
    IsUniversalKernel (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)

/-- Universality implies characteristicness.

URLs:
- https://www.jmlr.org/papers/volume13/gretton12a/gretton12a.pdf
- https://jmlr.org/papers/volume12/sriperumbudur11a/sriperumbudur11a.pdf -/
axiom universal_implies_characteristic
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (K : X → X → ℝ) (hK : IsUniversalKernel K) :
    IsCharacteristicKernel K

/-! ### Group-action building block -/

/-- Orthogonal group acts transitively on the sphere.

URL: https://users.jyu.fi/~parkkone/RG2012/RG2012.pdf -/
axiom orthogonal_group_transitive_on_sphere
    (d : ℕ) (hDim : 2 ≤ d) :
    ∀ u v : Sphere d,
      ∃ O : (Vec d) ≃ₗᵢ[ℝ] Vec d, rotateSphere O u = v

/-! ### MMD building block -/

/-- MMD² is nonnegative for PSD kernels.

URLs:
- https://www.jmlr.org/papers/volume13/gretton12a/gretton12a.pdf
- https://jmlr.org/papers/volume12/sriperumbudur11a/sriperumbudur11a.pdf -/
axiom mmdSq_nonneg
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (hK : IsPosSemiDefKernel K)
    (P Q : Distribution X) :
    mmdSq K P Q ≥ 0

end WristbandLossProofs
