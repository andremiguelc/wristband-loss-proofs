import WristbandLossProofs.Spectral.SpectralPrimitives
import WristbandLossProofs.KernelImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Spectral Imported Facts

**This file contains exactly one axiom**: the Mercer decomposition of the
angular kernel.

Every other fact used in the spectral branch is either already proved
elsewhere (`cosine_mode_integral_uniform01` in `KernelFoundations`),
in Mathlib (`integral_tsum`, `tsum_comm'`, `tsum_mul_left`, `integral_prod_mul`),
or locally derivable (from orthonormality + sphere symmetry).

### Reused from existing files (no changes needed)

| Axiom | File | Used for |
|-------|------|----------|
| `kernelRadNeumann_hasCosineExpansion` | `KernelImportedFacts` | radial `a0` and `a k` witnesses |
| `kernelAngChordal_posSemiDef` | `KernelImportedFacts` | justifies `λv j ≥ 0` |
| `kernelEnergy_minimizer_unique` | `KernelMinimization` | uniqueness conclusion |
| `wristbandEquivalence` | `Equivalence` | Gaussian ↔ uniform bridge |
-/

/-! ### Mercer decomposition of the angular kernel (sole axiom) -/

/-- **Mercer decomposition of `kernelAngChordal`.**

    For any `d ≥ 2`, `β > 0`, `α > 0`, there exist angular eigenfunctions
    `φ : ℕ → Sphere d → ℝ` and eigenvalues `λv : ℕ → ℝ` satisfying:

    1. **(Nonnegativity)** `λv j ≥ 0` for all `j`.
    2. **(Orthonormality)** `{φ j}` is orthonormal in `L²(sphereUniform d)`:
       `∫ φ_j(u) · φ_j'(u) dσ(u) = δ_{jj'}`.
    3. **(Kernel expansion)** `k_ang(u, v) = Σ' j, λv j · φ_j(u) · φ_j(v)`
       (as a `tsum` equality pointwise on `Sphere d × Sphere d`).
    4. **(Constant-mode identification)** `φ 0 = fun _ => 1`:
       the zeroth eigenfunction is the constant function equal to 1
       (valid since `sphereUniform d` is a probability measure).

    **Source**: Mercer (1909); Steinwart–Christmann (2008), Theorem 4.49.
    The chain of reasoning is:
    - *Compactness of `T_K`:* `kernelAngChordal β α` is continuous on the compact
      space `Sphere d`, so `K ∈ L²(σ ⊗ σ)` and `T_K` is Hilbert–Schmidt, hence compact.
    - *Self-adjointness of `T_K`:* the kernel is symmetric (`K(u,v) = K(v,u)`).
    - *Nonnegativity of eigenvalues:* the kernel is PSD (`kernelAngChordal_posSemiDef`),
      so `⟨T_K f, f⟩ ≥ 0`, giving `λv j ≥ 0` (clause 1).
    These three properties are standard functional analysis; they yield the countable
    orthonormal eigenbasis. **Mercer's theorem** is the separate, stronger statement
    that the eigenexpansion in clause (3) converges *pointwise* (not merely in `L²`),
    which holds for continuous PSD kernels on compact metric spaces.

    **Mathlib status**: Mathlib has spectral theory for compact operators
    (`Analysis.InnerProductSpace.Spectrum`) but not the Mercer pointwise
    convergence form for integral operators. The `tsum` equality in clause (3)
    is the minimal statement needed for downstream proofs; uniform convergence
    is not asserted.

    References:
    - Mercer, J. (1909). "Functions of positive and negative type."
      *Phil. Trans. R. Soc. Lond. A*, 209, 415–446.
    - Steinwart, I. & Christmann, A. (2008). *Support Vector Machines*,
      Theorem 4.49. Springer.
    - Schoenberg, I.J. (1942). "Positive definite functions on spheres."
      *Duke Math. J.*, 9(1), 96–108. -/
axiom kernelAngChordal_mercerExpansion
    (d : ℕ) (β α : ℝ) (hDim : 2 ≤ d) (hβ : 0 < β) (hα : 0 < α) :
    ∃ (φ : ℕ → Sphere d → ℝ) (lambdaV : ℕ → ℝ),
      -- (1) Nonnegativity of eigenvalues
      (∀ j : ℕ, 0 ≤ lambdaV j) ∧
      -- (2) Orthonormality in L²(sphereUniform d)
      (∀ j j' : ℕ,
        ∫ u, φ j u * φ j' u ∂(sphereUniform d : Measure (Sphere d)) =
          if j = j' then 1 else 0) ∧
      -- (3) Pointwise kernel expansion as a tsum
      (∀ u v : Sphere d,
        kernelAngChordal β α u v =
          ∑' j : ℕ, lambdaV j * φ j u * φ j v) ∧
      -- (4) Constant-mode identification
      (∀ u : Sphere d, φ 0 u = 1)

end WristbandLossProofs
