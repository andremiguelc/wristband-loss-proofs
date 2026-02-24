import WristbandLossProofs.KernelPrimitives

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Spectral Primitives

Definitions for the spectral decomposition of the wristband kernel energy.

The key identity (proved in `SpectralFoundations`) is:

  `kernelEnergy (wristbandKernelNeumann β α) P = spectralEnergy φ λv a0 a P`

where:
- `λv j ≥ 0` are the Mercer eigenvalues of `kernelAngChordal β α` on `Sphere d`
  (from axiom `kernelAngChordal_mercerExpansion` in `SpectralImportedFacts`)
- `a0` is the constant-mode coefficient and `a k` the k-th cosine coefficient
  of `kernelRadNeumann β` (from axiom `kernelRadNeumann_hasCosineExpansion`)
- `modeProj φ j k P = E_{(u,t)~P}[φ_j(u) · radialFeature k t]`
- `spectralEnergy = Σ' j k, λv j · radialCoeff a0 a k · (modeProj j k P)²`

The (j=0, k=0) term is the constant-constant mode:
`φ_0(u) = 1` and `radialFeature 0 t = 1`, so `modeProj φ 0 0 P = 1` for any
probability measure P.  This gives the minimum value `λv 0 · a0`.
All other terms vanish at `wristbandUniform d` (the reference measure).
-/

/-! ### Radial feature and radial coefficient -/

/-- Extended radial feature: constant for mode `k = 0`, cosine for modes `k ≥ 1`.

    `radialFeature 0 t = 1` (constant mode).
    `radialFeature k t = cos(k·π·t)` for `k ≥ 1` (cosine modes).

    This unifies the constant term `a0` and the cosine terms `a k` from
    `kernelRadNeumann_hasCosineExpansion` into a single indexed family.
    The `kernelRadNeumann` expansion uses cosines `cos((k+1)·π·t)` indexed
    from `k = 0`; these correspond to `radialFeature (k + 1)`. -/
noncomputable def radialFeature (k : ℕ) (t : UnitInterval) : ℝ :=
  if k = 0 then 1
  else Real.cos ((k : ℝ) * Real.pi * (t : ℝ))

/-- Extended radial coefficient: constant-mode weight for `k = 0`,
    cosine-mode weight `a (k - 1)` for `k ≥ 1`.

    This aligns `radialCoeff a0 a` with `radialFeature`:
    `kernelRadNeumann β t t' = Σ' k, radialCoeff a0 a k · radialFeature k t · radialFeature k t'`
    (see `spectralFoundations.kernelRadNeumann_spectralExpansion`). -/
noncomputable def radialCoeff (a0 : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0       => a0
  | k + 1   => a k

/-! ### Joint mode projection -/

/-- Joint mode projection: `E_{(u,t)~P}[φ_j(u) · radialFeature k t]`.

    This is `ĉ_{jk}(P)` in the spectral energy decomposition.
    - `j` indexes the angular eigenfunction (from the Mercer decomposition).
    - `k` indexes the radial mode: `k = 0` is the constant mode,
      `k ≥ 1` gives cosine modes `cos(k·π·t)`.

    Special cases used in proofs:
    - `modeProj φ 0 0 P = 1` for any probability measure `P`
      (since `φ 0 = fun _ => 1` and `radialFeature 0 = fun _ => 1`).
    - `modeProj φ j k (wristbandUniform d) = 0` for `(j, k) ≠ (0, 0)`
      (angular eigenfunctions with `j > 0` integrate to 0 under `sphereUniform`;
       cosine modes with `k ≥ 1` integrate to 0 under `uniform01`). -/
noncomputable def modeProj
    {d : ℕ} (φ : ℕ → Sphere d → ℝ) (j k : ℕ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∫ w,
    φ j w.1 * radialFeature k w.2
  ∂(P : Measure (Wristband d))

/-! ### Spectral energy -/

/-- Spectral energy: double-mode decomposition of `kernelEnergy`.

    `spectralEnergy φ λv a0 a P = Σ' j k, λv j · radialCoeff a0 a k · (modeProj φ j k P)²`

    Each term is non-negative (since `λv j ≥ 0`, `radialCoeff a0 a k ≥ 0`,
    and squares are ≥ 0). The minimum over all distributions is achieved at
    `wristbandUniform d`, where all off-diagonal modes vanish.

    The main identity `spectralEnergy_eq_kernelEnergy` (in `SpectralFoundations`)
    shows this equals `kernelEnergy (wristbandKernelNeumann β α) P`. -/
noncomputable def spectralEnergy
    {d : ℕ}
    (φ : ℕ → Sphere d → ℝ)
    (λv : ℕ → ℝ)
    (a0 : ℝ) (a : ℕ → ℝ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∑' j : ℕ, ∑' k : ℕ,
    λv j * radialCoeff a0 a k * (modeProj φ j k P) ^ 2

end WristbandLossProofs
