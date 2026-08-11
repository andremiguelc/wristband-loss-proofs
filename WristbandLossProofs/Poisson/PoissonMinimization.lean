import WristbandLossProofs.Poisson.PoissonFoundations
import WristbandLossProofs.KernelMinimization

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Poisson Minimization

An unbiased sampler does not approximate the wristband kernel — under
`IsUnbiasedFor` it *is* the wristband kernel, pointwise. So `KernelMinimization`
transfers by rewriting: `sampledEnergy_minimizer_unique` is
`kernelEnergy_minimizer_unique` with the kernel renamed.

The statements are about the sampler's *expectation*. A single fixed draw gives a
different kernel with finite rank, and none of them applies to it. So the draw
must change at each step.
-/

/-! ### Transfer -/

/-- An unbiased sampler yields the same energy as the Neumann wristband kernel.
Not an approximation: the two kernels agree at every pair of points, so this is
congruence rather than an estimate. -/
theorem sampledEnergy_eq_kernelEnergy
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (S : AngularSampler d Ω) (β α : ℝ)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) :
    kernelEnergy (sampledWristbandKernel S β) P
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P := by
  have hker : sampledWristbandKernel S β = wristbandKernelNeumann (d := d) β α := by
    funext w w'
    rw [sampledWristbandKernel, wristbandKernelNeumann, hUnbiased]
  rw [hker]

/-! ### Main theorems -/

/-- **Minimized at the uniform measure.** -/
theorem sampledEnergy_minimized_at_uniform
    (d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (S : AngularSampler d Ω)
    (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) :
    kernelEnergy (sampledWristbandKernel S β) P ≥
      kernelEnergy (sampledWristbandKernel S β) (wristbandUniform d hDim1) := by
  rw [sampledEnergy_eq_kernelEnergy S β α hUnbiased,
    sampledEnergy_eq_kernelEnergy S β α hUnbiased]
  exact kernelEnergy_minimized_at_uniform d hDim β α hβ hα P (hDim1 := hDim1)

/-- **Uniqueness survives sampling.** The uniform measure is the only
distribution sitting at the minimum. -/
theorem sampledEnergy_minimizer_unique
    (d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (S : AngularSampler d Ω)
    (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d))
    (hEq : kernelEnergy (sampledWristbandKernel S β) P
      = kernelEnergy (sampledWristbandKernel S β) (wristbandUniform d hDim1)) :
    P = wristbandUniform d hDim1 := by
  rw [sampledEnergy_eq_kernelEnergy S β α hUnbiased,
    sampledEnergy_eq_kernelEnergy S β α hUnbiased] at hEq
  exact kernelEnergy_minimizer_unique d hDim β α hβ hα P (hDim1 := hDim1) (hEq := hEq)

/-- **Gaussian characterization.** The sampled energy reaches its minimum exactly
when the input law of the encoder is standard Gaussian. The spectral branch proves
the same statement. This version holds for a loss that enumerates no basis. -/
theorem sampledEnergy_wristband_gaussian_iff
    (d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (S : AngularSampler d Ω)
    (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (Q : Distribution (VecNZ d)) :
    Q = gaussianNZ d hDim1 ↔
      kernelEnergy (sampledWristbandKernel S β) (wristbandLaw d Q)
        = kernelEnergy (sampledWristbandKernel S β) (wristbandUniform d hDim1) := by
  constructor
  · intro hQ
    subst hQ
    congr 1
    exact wristbandEquivalence_backward d hDim hDim1
  · intro hEnergy
    have hUniform : wristbandLaw d Q = wristbandUniform d hDim1 :=
      sampledEnergy_minimizer_unique d S hDim hDim1 β α hβ hα hUnbiased
        (wristbandLaw d Q) hEnergy
    exact (wristbandEquivalence d hDim hDim1 Q).mp hUniform

/-! ### The Poisson sampler in particular

Everything above holds for any unbiased sampler. `poissonAngularSampler` is one,
by `poissonAngularSampler_unbiased`, so the payoff instantiates. -/

/-- The Poisson mode sampler has the uniform measure as its unique minimizer. -/
theorem poissonSampledEnergy_minimizer_unique
    (d : ℕ) (hDim : 2 ≤ d) (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hEq : kernelEnergy (sampledWristbandKernel (poissonAngularSampler d β α hβ) β) P
      = kernelEnergy (sampledWristbandKernel (poissonAngularSampler d β α hβ) β)
          (wristbandUniform d hDim1)) :
    P = wristbandUniform d hDim1 :=
  sampledEnergy_minimizer_unique d (poissonAngularSampler d β α hβ) hDim hDim1 β α hβ hα
    (poissonAngularSampler_unbiased d β α hβ) P hEq

end WristbandLossProofs
