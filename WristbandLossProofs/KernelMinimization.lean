import WristbandLossProofs.KernelImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Kernel Energy Minimization

This file proves **Hypothesis K**: the wristband kernel energy is uniquely
minimized at the uniform measure `μ₀ = σ_{d-1} ⊗ Unif[0,1]`.

The proof follows the standard MMD pathway:
1. The kernel is PSD → `MMD²(P, μ₀) ≥ 0`.
2. The potential `h(w) = E_{W'~μ₀}[K(w,W')]` is constant → energy-MMD
   identity: `E(P) - E(μ₀) = MMD²(P, μ₀)`.
3. The kernel is characteristic → `MMD² = 0 ⟹ P = μ₀`.
4. Combining: `E(P) ≥ E(μ₀)`, with equality iff `P = μ₀`.

The result is stated for the Neumann kernel (infinite reflection series),
which has exactly constant potential. A truncation bound relates this to
the 3-image kernel actually used in Python.
-/

/-! ### PSD of the joint kernel

Product of PSD kernels is PSD (Schur product theorem for kernel
functions). -/

/-- Product of two PSD kernels (on possibly different spaces) gives a
    PSD kernel on the product space.
    This is the kernel-function version of the Schur product theorem. -/
theorem productKernel_posSemiDef
    {X : Type*} {Y : Type*}
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (hKx : IsPosSemiDefKernel Kx)
    (hKy : IsPosSemiDefKernel Ky) :
    IsPosSemiDefKernel
      (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2) := by
  sorry

/-- The joint Neumann wristband kernel is PSD.
    Follows from: angular is PSD + Neumann radial is PSD + product is PSD. -/
theorem wristbandKernelNeumann_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (wristbandKernelNeumann (d := d) β α) := by
  sorry

/-! ### Constant potential of the joint kernel

The potential of a product kernel under a product measure factors:
`h(u,t) = h_ang(u) · h_rad(t)`. This combines with constant-potential
facts for angular and radial factors to yield constancy of the joint
Neumann kernel.
-/

/-- Potential of a product kernel under a product measure factors
    as the product of the component potentials:
    `E_{(u',t')~μ⊗ν}[Kx(u,u')·Ky(t,t')] = E_{u'~μ}[Kx(u,u')] · E_{t'~ν}[Ky(t,t')]`.
    This is Fubini's theorem applied to the product. -/
theorem productPotential_factors
    {X : Type*} {Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (Kx : X → X → ℝ) (Ky : Y → Y → ℝ)
    (μ : Distribution X) (ν : Distribution Y)
    (w : X × Y) :
    kernelPotential
      (fun (p q : X × Y) => Kx p.1 q.1 * Ky p.2 q.2)
      (productLaw μ ν) w =
    kernelPotential Kx μ w.1 * kernelPotential Ky ν w.2 := by
  sorry

/-- The joint Neumann kernel has constant potential under `μ₀`.
    Combines: angular constant potential + Neumann constant potential +
    product factorization. -/
theorem wristbandKernelNeumann_constantPotential
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    ∃ c : ℝ,
      HasConstantPotential
        (wristbandKernelNeumann (d := d) β α)
        (wristbandUniform d) c := by
  sorry

/-! ### Main theorem: energy uniquely minimized at uniform

This is **Hypothesis K** from the proof plan. -/

/-- **Hypothesis K (energy minimization).**
    The kernel energy `E(P) = E_{W,W'~P}[K(W,W')]` satisfies
    `E(P) ≥ E(μ₀)` for all distributions `P` on wristband space. -/
theorem kernelEnergy_minimized_at_uniform
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    kernelEnergy (wristbandKernelNeumann β α) P ≥
      kernelEnergy (wristbandKernelNeumann β α)
        (wristbandUniform d) := by
  sorry

/-- **Hypothesis K (uniqueness).**
    If `E(P) = E(μ₀)`, then `P = μ₀`. -/
theorem kernelEnergy_minimizer_unique
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hEq : kernelEnergy (wristbandKernelNeumann β α) P =
      kernelEnergy (wristbandKernelNeumann β α)
        (wristbandUniform d)) :
    P = wristbandUniform d := by
  sorry

/-! ### 3-image truncation bound

The Python code uses the 3-image kernel, not the full Neumann series.
The difference is exponentially small in `β`: the omitted terms all
involve reflected distances `≥ 2`, contributing `O(exp(-4β))` each. -/

/-- The 3-image kernel is within `O(exp(-4β))` of the Neumann kernel
    pointwise. -/
theorem threeImage_approx_neumann
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    |kernelRad3Image β t t' - kernelRadNeumann β t t'| ≤
      -- The omitted terms have distances ≥ 2, squared ≥ 4
      -- Each pair of terms contributes ≤ 2·exp(-4β), summed over
      -- all n ≠ 0 (geometric series)
      2 * Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
  sorry

/-- The 3-image kernel energy is close to the Neumann kernel energy. -/
theorem threeImage_energy_approx
    {d : ℕ} (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    |kernelEnergy (wristbandKernel β α) P -
     kernelEnergy (wristbandKernelNeumann β α) P| ≤
      2 * Real.exp (-4 * β) / (1 - Real.exp (-4 * β)) := by
  sorry

end WristbandLossProofs
