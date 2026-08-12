import WristbandLossProofs.Fourier.FourierFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## Fourier Estimator

What the Fourier sampler gives once the side conditions are theorems.

The estimator theorems hold for any unbiased sampler, so the statements here are
instances rather than new arguments. What is new is the hypothesis list. The
generic form of `featureCount_suffices` asks the caller for four things: the
integrability of the draw kernel, the square-integrability of one draw's energy,
a bound `V` on its variance, and unbiasedness. For this sampler the first three
are discharged, and `V` arrives as the explicit constant `4 · (sup k_rad)²`. The
only remaining input is the size of the draw.

`fourierRealizedAngularEnergy_featureForm` shows where the pairwise sum goes. The
angular energy of one draw set is a mean of squared batch means, one per feature.
No sum over pairs of points remains, so the cost is linear in the batch.

Two limits of these statements. First, they cover the mean over draws, so the
draw must change at each step: one fixed draw set gives a kernel of finite rank
whose own minimizer sits elsewhere. Second, the variance constant is the extreme
value of the draw energy, not its spread. It therefore over-provisions, and it
grows with the kernel scale although the true variance does not.
-/

/-! ### The estimate is unbiased -/

/-- The random Fourier feature sampler computes an unbiased estimate of the
energy. -/
theorem fourierRealizedEnergy_unbiased (d : ℕ) (β α : ℝ) (hβ : 0 < β) {D : ℕ}
    (hD : 0 < D) (P : Distribution (Wristband d)) :
    ∫ ω, kernelEnergy
        (realizedWristbandKernel (fourierAngularSampler d β α hβ) β ω) P
        ∂(drawLaw (fourierAngularSampler d β α hβ) D
          : Measure (Fin D → FourierDraw d))
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P :=
  realizedEnergy_unbiased _ β α hD (fourierAngularSampler_unbiased d β α hβ) P
    (fourier_hasIntegrableDrawEnergy β α hβ P)

/-! ### The feature count -/

/-- **How many features the estimate needs.**

`D ≥ 4 (sup k_rad)² / (δ ε²)` holds the estimate within `ε` of the true energy,
with probability `1 - δ` or more. Nothing else is assumed: the constant comes
from the pointwise bound on the feature, and it reads neither the dimension, nor
the angular scale, nor the distribution. -/
theorem fourierFeatureCount_suffices (d : ℕ) (β α : ℝ) (hβ : 0 < β) {D : ℕ}
    (hD : 0 < D) (P : Distribution (Wristband d)) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hcount : 4 * neumannSup β ^ 2 / (δ * ε ^ 2) ≤ (D : ℝ)) :
    (drawLaw (fourierAngularSampler d β α hβ) D
        : Measure (Fin D → FourierDraw d))
        {ω | ε ≤ |kernelEnergy
              (realizedWristbandKernel (fourierAngularSampler d β α hβ) β ω) P
              - kernelEnergy (wristbandKernelNeumann (d := d) β α) P|}
      ≤ ENNReal.ofReal δ :=
  featureCount_suffices _ β α hD (fourierAngularSampler_unbiased d β α hβ) P
    (fourier_hasIntegrableDrawEnergy β α hβ P)
    (fourier_drawEnergy_memLp_two β α hβ P)
    (fourier_drawEnergy_variance_le β α hβ P) hδ hε hcount

/-- **The same rule, with the constant a batch can measure.**

`radialEnergy` is the mean of the radial factor over the batch, and it is far
below the largest value that factor takes. So this rule asks for fewer features
than `fourierFeatureCount_suffices`, at the cost of one measured quantity. -/
theorem fourierFeatureCount_suffices_radial (d : ℕ) (β α : ℝ) (hβ : 0 < β)
    {D : ℕ} (hD : 0 < D) (P : Distribution (Wristband d)) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hcount : 4 * radialEnergy β P ^ 2 / (δ * ε ^ 2) ≤ (D : ℝ)) :
    (drawLaw (fourierAngularSampler d β α hβ) D
        : Measure (Fin D → FourierDraw d))
        {ω | ε ≤ |kernelEnergy
              (realizedWristbandKernel (fourierAngularSampler d β α hβ) β ω) P
              - kernelEnergy (wristbandKernelNeumann (d := d) β α) P|}
      ≤ ENNReal.ofReal δ :=
  featureCount_suffices _ β α hD (fourierAngularSampler_unbiased d β α hβ) P
    (fourier_hasIntegrableDrawEnergy β α hβ P)
    (fourier_drawEnergy_memLp_two β α hβ P)
    (fourier_drawEnergy_variance_le_radial β α hβ P) hδ hε hcount

/-- **The loss ranks two distributions correctly.** The same feature set reads both,
so this is one event on one space. The gap has to exceed twice the tolerance. -/
theorem fourierRealizedEnergy_separates (d : ℕ) (β α : ℝ) (hβ : 0 < β) {D : ℕ}
    (hD : 0 < D) (P Q : Distribution (Wristband d)) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hcount : 4 * neumannSup β ^ 2 / (δ * ε ^ 2) ≤ (D : ℝ))
    (hgap : 2 * ε < kernelEnergy (wristbandKernelNeumann (d := d) β α) P
      - kernelEnergy (wristbandKernelNeumann (d := d) β α) Q) :
    (drawLaw (fourierAngularSampler d β α hβ) D
        : Measure (Fin D → FourierDraw d))
        {ω | kernelEnergy
              (realizedWristbandKernel (fourierAngularSampler d β α hβ) β ω) Q
            < kernelEnergy
              (realizedWristbandKernel (fourierAngularSampler d β α hβ) β ω) P}ᶜ
      ≤ ENNReal.ofReal δ + ENNReal.ofReal δ :=
  realizedEnergy_separates _ β α hD (fourierAngularSampler_unbiased d β α hβ) P Q
    (fourier_hasIntegrableDrawEnergy β α hβ P)
    (fourier_hasIntegrableDrawEnergy β α hβ Q)
    (fourier_drawEnergy_memLp_two β α hβ P)
    (fourier_drawEnergy_memLp_two β α hβ Q)
    (fourier_drawEnergy_variance_le β α hβ P)
    (fourier_drawEnergy_variance_le β α hβ Q) hδ hε hcount hgap

/-! ### What the estimate is an estimate of -/

/-- The uniform measure is the only distribution at the minimum of the sampled
energy. -/
theorem fourierSampledEnergy_minimizer_unique (d : ℕ) (hDim : 2 ≤ d)
    (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hEq : kernelEnergy
        (sampledWristbandKernel (fourierAngularSampler d β α hβ) β) P
      = kernelEnergy (sampledWristbandKernel (fourierAngularSampler d β α hβ) β)
          (wristbandUniform d hDim1)) :
    P = wristbandUniform d hDim1 :=
  sampledEnergy_minimizer_unique d _ hDim hDim1 β α hβ hα
    (fourierAngularSampler_unbiased d β α hβ) P hEq

/-- **The sampled energy reaches its minimum exactly at the Gaussian.** No basis
is enumerated and no degree is cut. -/
theorem fourierSampledEnergy_wristband_gaussian_iff (d : ℕ) (hDim : 2 ≤ d)
    (hDim1 : 1 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (Q : Distribution (VecNZ d)) :
    Q = gaussianNZ d hDim1 ↔
      kernelEnergy (sampledWristbandKernel (fourierAngularSampler d β α hβ) β)
          (wristbandLaw d Q)
        = kernelEnergy (sampledWristbandKernel (fourierAngularSampler d β α hβ) β)
          (wristbandUniform d hDim1) :=
  sampledEnergy_wristband_gaussian_iff d _ hDim hDim1 β α hβ hα
    (fourierAngularSampler_unbiased d β α hβ) Q

/-! ### Where the pairwise sum goes -/

lemma fourier_integrable_feat {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    (z : FourierDraw d) (P : Distribution (Sphere d)) :
    Integrable (fun u => (fourierAngularSampler d β α hβ).feat z u)
      (P : Measure (Sphere d)) := by
  have hcont : Continuous (fun u : Sphere d => fourierFeature z u) := by
    unfold fourierFeature; fun_prop
  refine Integrable.mono' (integrable_const (Real.sqrt 2))
    hcont.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact abs_fourierFeature_le z u

/-- **The angular energy of one feature set is a mean of squared batch means.**
One mean per feature. No sum over pairs of points remains, so the cost is linear
in the batch. -/
theorem fourierRealizedAngularEnergy_featureForm {d : ℕ} (β α : ℝ) (hβ : 0 < β)
    {D : ℕ} (ω : Fin D → FourierDraw d) (P : Distribution (Sphere d)) :
    kernelEnergy (realizedAngularKernel (fourierAngularSampler d β α hβ) ω) P
      = (D : ℝ)⁻¹ * ∑ j : Fin D,
          (∫ u, (fourierAngularSampler d β α hβ).feat (ω j) u
            ∂(P : Measure (Sphere d))) ^ 2 :=
  realizedAngularEnergy_featureForm _ ω P
    fun j => fourier_integrable_feat β α hβ (ω j) P

end WristbandLossProofs
