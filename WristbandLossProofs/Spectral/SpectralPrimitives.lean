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
  of `kernelRadNeumann β` (from `kernelRadNeumann_explicitCosineExpansion`)
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
    `kernelRadNeumann_explicitCosineExpansion` into a single indexed family.
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
    (lambdaV : ℕ → ℝ)
    (a0 : ℝ) (a : ℕ → ℝ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∑' j : ℕ, ∑' k : ℕ,
    lambdaV j * radialCoeff a0 a k * (modeProj φ j k P) ^ 2

/-- Spectral energy with the radial axis truncated to modes `k ≤ K`.

The outer angular sum stays infinite (`∑'`) because no decay rate on
`lambdaV` is assumed; only the radial axis is truncated. Used in the
truncation-error bound `spectralEnergyRadialTruncated_error_le`. -/
noncomputable def spectralEnergyRadialTruncated
    {d : ℕ}
    (φ : ℕ → Sphere d → ℝ)
    (lambdaV : ℕ → ℝ)
    (a0 : ℝ) (a : ℕ → ℝ)
    (K : ℕ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∑' j : ℕ, ∑ k ∈ Finset.range (K + 1),
    lambdaV j * radialCoeff a0 a k * (modeProj φ j k P) ^ 2

/-- Joint-(L, K) truncated spectral energy: both angular and radial axes
truncated to finite ranges.

  - `L` = highest angular Mercer mode index kept (so modes `j ∈ {0, 1, …, L}`,
    i.e. `L + 1` angular modes total).
  - `K` = highest radial mode index kept (so modes `k ∈ {0, 1, …, K}`, i.e.
    `K + 1` radial modes total).

Naming convention: in Python (`python/spectral/kernel.py`) and the math docs
(`docs/working/_spectral_what_and_why.md`) the cutoff is "number of modes kept",
so Python's `k_modes = 6, ell ≤ 1` corresponds here to `K = 5, L = 1`.

Both axes are finite sums, so no summability assumption is needed. The
truncation-error bound `spectralEnergyTruncated_error_le` decomposes
`|spectralEnergy − spectralEnergyTruncated L K|` into an angular-tail piece
(j > L) and a radial-tail piece (k > K, j ≤ L). -/
noncomputable def spectralEnergyTruncated
    {d : ℕ}
    (φ : ℕ → Sphere d → ℝ)
    (lambdaV : ℕ → ℝ)
    (a0 : ℝ) (a : ℕ → ℝ)
    (L K : ℕ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1),
    lambdaV j * radialCoeff a0 a k * (modeProj φ j k P) ^ 2

/-! ### Degree-indexed truncated spectral energy (user-facing closed-form API)

The flat-indexed `spectralEnergyTruncated` above takes `L` = "highest flat
eigenmode index kept", which is convenient for the qualitative bound but
does not align with how Python/math docs index angular truncation by
**degree**.  The degree-indexed wrapper below threads a `degAt : ℕ → ℕ`
accessor (typically `mercerDegAt d β α …`) so the user-facing `L` means
"highest angular *degree* kept" — matching the Python convention
`ℓ ≤ L_python` ↔ Lean `L = L_python`.  The radial `K` already aligns this way.

The closed-form truncation error bound is stated against this wrapper, not
the flat-indexed version. -/

/-- Degree-indexed joint truncation of `spectralEnergy`: keeps angular
eigenmodes with `degAt j ≤ L` and radial modes `k ≤ K`. -/
noncomputable def spectralEnergyTruncatedByDegree
    {d : ℕ}
    (φ : ℕ → Sphere d → ℝ)
    (lambdaV : ℕ → ℝ)
    (degAt : ℕ → ℕ)
    (a0 : ℝ) (a : ℕ → ℝ)
    (L K : ℕ)
    (P : Distribution (Wristband d)) : ℝ :=
  ∑' j : ℕ, if degAt j ≤ L then
    ∑ k ∈ Finset.range (K + 1),
      lambdaV j * radialCoeff a0 a k * (modeProj φ j k P) ^ 2
  else 0

/-! ### Spherical-harmonic multiplicity

The dimension of the space of degree-`ℓ` spherical harmonics on `S^{d-1}`
(`ℓ ≥ 0`, `d ≥ 2`).  Closed-form binomial-difference formula:
`N(d, ℓ) = C(ℓ + d − 1, d − 1) − C(ℓ + d − 3, d − 1)`.

Special case `d = 2`: `N(2, 0) = 1`, `N(2, ℓ) = 2` for `ℓ ≥ 1`
(the two `sin(ℓ θ), cos(ℓ θ)` modes).
For general `d ≥ 2` and `ℓ ≥ 1`: `N(d, ℓ) = (2ℓ + d − 2)·C(ℓ + d − 3, ℓ − 1)`,
which equals the binomial difference above. -/

/-- Number of linearly independent spherical harmonics of degree `ℓ` on `S^{d−1}`.
Used as the multiplicity factor in the Mercer block decomposition. -/
def sphericalHarmonicDim (d ℓ : ℕ) : ℕ :=
  Nat.choose (ℓ + d - 1) (d - 1) - Nat.choose (ℓ + d - 3) (d - 1)

@[simp] lemma sphericalHarmonicDim_zero (d : ℕ) (hd : 2 ≤ d) :
    sphericalHarmonicDim d 0 = 1 := by
  unfold sphericalHarmonicDim
  have h1 : (0 : ℕ) + d - 1 = d - 1 := by omega
  have h2 : (0 : ℕ) + d - 3 < d - 1 := by omega
  rw [h1, Nat.choose_self, Nat.choose_eq_zero_of_lt h2]

end WristbandLossProofs
