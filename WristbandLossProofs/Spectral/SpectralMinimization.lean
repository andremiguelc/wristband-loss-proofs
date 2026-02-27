import WristbandLossProofs.Spectral.SpectralFoundations
import WristbandLossProofs.KernelMinimization

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Spectral Minimization

Main theorems of the spectral kernel branch.

All three theorem bodies are complete and now discharge directly from
`SpectralFoundations` + `KernelMinimization`.

### Import DAG for this file

```
KernelMinimization ─── kernelEnergy_minimizer_unique (reused)
       ↑
SpectralFoundations ── spectralEnergy_eq_kernelEnergy
                    ── spectralEnergy_nonneg_excess
SpectralMinimization
```
-/

/-! ### Main theorems -/

/-- **Spectral energy is minimized at `wristbandUniform d`**.

    `spectralEnergy φ λv a0 a P ≥ spectralEnergy φ λv a0 a μ₀`

    Proof: `spectralEnergy_nonneg_excess` from `SpectralFoundations`. -/
theorem spectralEnergy_minimized_at_uniform
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d)) :
    spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        (wristbandUniform d) ≤
      spectralEnergy
        (mercerEigenfun d β α hDim hβ hα)
        (mercerEigenval d β α hDim hβ hα)
        (neumannConstantCoeff β hβ)
        (neumannCosineCoeff β hβ)
        P :=
  spectralEnergy_nonneg_excess d β α hDim hβ hα P

/-- **Uniqueness**: `spectralEnergy P = spectralEnergy μ₀` implies `P = μ₀`.

    Proof route:
    1. By `spectralEnergy_eq_kernelEnergy`, the hypothesis translates to
       `kernelEnergy (wristbandKernelNeumann β α) P = kernelEnergy ... μ₀`.
    2. Then `kernelEnergy_minimizer_unique` (from `KernelMinimization`) gives `P = μ₀`. -/
theorem spectralEnergy_minimizer_unique
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (P : Distribution (Wristband d))
    (hEq :
      spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          P =
        spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          (wristbandUniform d)) :
    P = wristbandUniform d := by
  -- Translate spectral equality to kernel energy equality via the main identity.
  have hKernelEq :
      kernelEnergy (wristbandKernelNeumann (d := d) β α) P =
        kernelEnergy (wristbandKernelNeumann (d := d) β α) (wristbandUniform d) := by
    rw [← spectralEnergy_eq_kernelEnergy d β α hDim hβ hα P,
        ← spectralEnergy_eq_kernelEnergy d β α hDim hβ hα (wristbandUniform d)]
    exact hEq
  -- Apply uniqueness from KernelMinimization.
  exact kernelEnergy_minimizer_unique d hDim β α hβ hα P hKernelEq

/-- **Gaussian characterization (spectral form)**: `Q ~ N(0, I)` iff the spectral
    energy of the wristband law of `Q` equals the minimum `spectralEnergy μ₀`.

    Proof route:
    1. Forward (Q = gaussianNZ → wristbandLaw Q = μ₀ → spectral energy is at minimum):
       `wristbandEquivalence_forward` gives `wristbandLaw Q = μ₀`, then both
       spectral energies are equal by definition.
    2. Backward (spectral energy at minimum → Q = gaussianNZ):
       `spectralEnergy_minimizer_unique` gives `wristbandLaw Q = μ₀`, then
       `wristbandEquivalence` gives `Q = gaussianNZ`. -/
theorem spectralEnergy_wristband_gaussian_iff
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α)
    (Q : Distribution (VecNZ d)) :
    Q = gaussianNZ d ↔
      spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          (wristbandLaw d Q) =
        spectralEnergy
          (mercerEigenfun d β α hDim hβ hα)
          (mercerEigenval d β α hDim hβ hα)
          (neumannConstantCoeff β hβ)
          (neumannCosineCoeff β hβ)
          (wristbandUniform d) := by
  constructor
  · -- Forward: Q = gaussianNZ → wristbandLaw Q = μ₀ → spectral energy equal.
    intro hQ
    subst hQ
    congr 1
    exact wristbandEquivalence_forward d hDim
  · -- Backward: spectral energy equality → wristbandLaw Q = μ₀ → Q = gaussianNZ.
    intro hSpectral
    have hUniform : wristbandLaw d Q = wristbandUniform d :=
      spectralEnergy_minimizer_unique d hDim β α hβ hα (wristbandLaw d Q) hSpectral
    exact (wristbandEquivalence d hDim Q).mp hUniform

end WristbandLossProofs
