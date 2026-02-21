import WristbandLossProofs.KernelFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Imported Kernel Theory

All declarations here are `axiom`s — external mathematical results from
the kernel methods and RKHS literature, assumed without Lean proof.

**Trust boundary.**
- All five axioms are **relational** (equations/inequalities/existentials over
  already-defined terms). They cannot introduce new objects or types.
- A validator should check per axiom: does the Lean statement faithfully
  encode the cited result at the indicated source?

**Axiom inventory (5 total).**
1. `kernelAngChordal_posSemiDef` — angular Gaussian RBF is PSD.
2. `kernelRadNeumann_posSemiDef` — Neumann radial kernel is PSD.
3. `kernelAngChordal_characteristic` — angular kernel is characteristic.
4. `kernelRadNeumann_characteristic` — Neumann kernel is characteristic.
5. `neumannPotential_constant` — Neumann potential under Lebesgue is constant.

**Dependency on definition correctness.**
Axioms 2, 4, 5 refer to `kernelRadNeumann`, which is defined via Mathlib's
`tsum` over `ℤ`. If `tsum` is not `Summable`, it returns 0 by convention.
A separate lemma `kernelRadNeumann_summable` in `KernelFoundations.lean`
establishes summability for `β > 0`, ensuring the definition computes the
intended infinite series. See `KernelFoundations.lean` for details.

**Proof architecture.**
These axioms, together with definitions in `KernelFoundations.lean` and the
equivalence axioms (`sphereUniform_rotationInvariant`), are sufficient
to prove that the wristband kernel energy is uniquely minimized at the
uniform measure `μ₀ = σ_{d-1} ⊗ Unif[0,1]`.
-/

/-! ### Positive Semi-Definiteness

A kernel `K : X → X → ℝ` is positive semi-definite (PSD) if every finite
Gram matrix `[K(xᵢ,xⱼ)]` is PSD: `Σᵢⱼ cᵢcⱼK(xᵢ,xⱼ) ≥ 0` for all `cᵢ ∈ ℝ`.
This matches the definition `IsPosSemiDefKernel` in `KernelFoundations.lean`.
-/

/-- The angular kernel `exp(-β·α²·‖u-u'‖²)` is positive semi-definite
    on the unit sphere for any `β > 0, α > 0`.

    **Validation chain (2 steps).**

    Step 1 — Bochner's theorem: a continuous function `φ : ℝⁿ → ℝ` is
    positive definite iff it is the Fourier transform of a finite nonneg
    Borel measure. The Gaussian `φ(x) = exp(-c‖x‖²)` is the Fourier
    transform of a Gaussian measure, hence PD on `ℝⁿ` for any `c > 0`.

    Open-access source: Fukumizu, *Kernel Theory* lecture notes, Thm 13.
    https://www.ism.ac.jp/~fukumizu/H20_kernel/Kernel_7_theory.pdf
    Also: Jordan Bell, *Bochner's Theorem*, Thm 5.
    https://jordanbell.info/LaTeX/mathematics/bochnertheorem/bochnertheorem.pdf
    Book: Berlinet & Thomas-Agnan (2004), *RKHS in Probability and
    Statistics*, Thm 13.

    Step 2 — Restriction to subset: if `K` is PSD on `ℝⁿ`, then `K`
    restricted to any subset `S ⊆ ℝⁿ` is PSD (the Gram matrix condition
    is tested on finitely many points, all in `S`).

    **Lean-to-math alignment.**
    `kernelAngChordal β α u u' = exp(2βα²(⟨u,u'⟩ - 1))`. For unit vectors
    `‖u-u'‖² = 2 - 2⟨u,u'⟩`, so this equals `exp(-βα²‖u-u'‖²)`, a
    Gaussian RBF with `c = βα²`. Since `β > 0, α > 0`, we have `c > 0`. ✓
    `IsPosSemiDefKernel` = finite Gram matrix PSD. ✓ -/
axiom kernelAngChordal_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (kernelAngChordal (d := d) β α)

/-- The Neumann radial kernel is positive semi-definite on `[0,1]`
    for any `β > 0`.

    **Validation chain (2 steps).**

    Step 1 — Spectral expansion: the Neumann heat kernel on `[0,1]` has
    the eigenfunction expansion (Foondun 2015, ALEA, §2):
    `K(t,t') = c₀ + Σ_{k≥1} λₖ cos(kπt) cos(kπt')`
    where `λₖ = 2·exp(-βk²π²) > 0` and `c₀ > 0`.
    Each term `cos(kπt)·cos(kπt')` is a rank-1 PSD kernel (`φ(t)·φ(t')`),
    and each coefficient is nonneg.
    Open-access: Foondun (2015), ALEA, Eq. in §2 (Neumann expansion).
    https://alea.impa.br/articles/v12/12-22.pdf

    Step 2 — Closure under sums: a convergent sum of PSD kernels with
    nonnegative coefficients is PSD. For finite Gram matrices, this is
    immediate (sum of PSD matrices is PSD). The convergence of the
    eigenfunction series is guaranteed by exponential decay of `λₖ`.
    Open-access: Fukumizu, *Operations on PD kernels*, Prop 3–4.
    https://www.ism.ac.jp/~fukumizu/TITECH2010/Kernel_elements_2.pdf
    Book: Berlinet & Thomas-Agnan (2004), §3.

    **Lean-to-math alignment.**
    `kernelRadNeumann β` is the image-sum representation of the same kernel:
    `∑' n : ℤ, [exp(-β(t-t'-2n)²) + exp(-β(t+t'-2n)²)]`.
    The image-sum and eigenfunction representations are equivalent via
    Poisson summation / Jacobi theta identity (Woit, *Poisson summation
    notes*: https://www.math.columbia.edu/~woit/fourier-analysis/theta-zeta.pdf
    NIST DLMF Ch. 20: https://dlmf.nist.gov/20).
    The Lean definition differs from the standard heat kernel by a positive
    scalar factor `√(π/β)` (the normalization constant); this does not
    affect PSD (positive constant × PSD = PSD). ✓
    `IsPosSemiDefKernel` = finite Gram matrix PSD. ✓
    Summability prerequisite: `kernelRadNeumann_summable` (KernelFoundations). -/
axiom kernelRadNeumann_posSemiDef
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β)

/-! ### Characteristicness

A kernel is *characteristic* if its MMD metric separates probability
measures: `MMD²(P, Q) = 0 ⟹ P = Q`. Our definition `IsCharacteristicKernel`
quantifies over `Distribution X` (= `ProbabilityMeasure X`), matching the
standard literature definition over Borel probability measures.

The standard proof chain for both axioms below is:
  Gaussian RBF is **universal** on compact metric spaces
  → universal ⟹ characteristic on compact spaces.
-/

/-- The angular kernel (Gaussian RBF in chordal distance) is
    characteristic on `S^{d-1}` for `d ≥ 2`.

    **Validation chain (2 steps).**

    Step 1 — Gaussian kernel is universal on compact subsets of `ℝⁿ`:
    the RKHS of `exp(-c‖x-y‖²)` for `c > 0` is dense in `C(X)` for
    any compact `X ⊂ ℝⁿ`. The sphere `S^{d-1}` is compact.
    Open-access: Steinwart (2001), *JMLR* 2:67–93, §3.
    https://www.jmlr.org/papers/volume2/steinwart01a/steinwart01a.pdf
    Also: Micchelli, Xu, Zhang (2006), *JMLR* 7:2651–2667.
    https://jmlr.csail.mit.edu/papers/volume7/micchelli06a/micchelli06a.pdf
    Book: Steinwart & Christmann (2008), Thm 4.57.

    Step 2 — Universal ⟹ characteristic on compact spaces:
    if the RKHS is dense in `C(X)`, the kernel mean embedding is
    injective on probability measures, so `MMD(P,Q) = 0 → P = Q`.
    Open-access: Sriperumbudur et al. (2010), *JMLR* 11:1517–1561,
    §3.1 + Thm 7 (integrally strictly PD ⟹ characteristic).
    https://www.jmlr.org/papers/volume11/sriperumbudur10a/sriperumbudur10a.pdf

    **Lean-to-math alignment.**
    `IsCharacteristicKernel K` = `∀ P Q, mmdSq K P Q = 0 → P = Q`.
    This matches the Sriperumbudur definition (injectivity of embedding). ✓
    The `d ≥ 2` guard: `S⁰ = {-1,1}` is discrete (2 points). For `d ≥ 2`,
    `S^{d-1}` is a compact connected manifold. The guard is conservative
    but harmless (the Gaussian is actually characteristic on `S⁰` too). ✓
    The kernel is bounded (`0 < K ≤ 1`), so the Bochner integrals in
    `mmdSq` converge for all probability measures. ✓ -/
axiom kernelAngChordal_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (kernelAngChordal (d := d) β α)

/-- The Neumann radial kernel is characteristic on `[0,1]` for `β > 0`.

    **Validation chain (3 steps).**

    Step 1 — Single Gaussian RBF `exp(-β(t-t')²)` is universal on
    `[0,1]` (compact subset of `ℝ`). Same reference as step 1 of
    `kernelAngChordal_characteristic` (Steinwart 2001, §3).

    Step 2 — RKHS containment: `H(single Gaussian) ⊆ H(Neumann)`.
    The Neumann kernel is the single Gaussian (the `n=0` term of
    `exp(-β(t-t'-2n)²)`) plus nonneg PSD terms. Adding PSD terms
    enlarges the RKHS.
    Book: Berlinet & Thomas-Agnan (2004), §5 (RKHS inclusion).

    Step 3 — If `H₁ ⊆ H₂` and the embedding via `H₁` is injective
    (characteristic), then the embedding via `H₂` is also injective.
    This is immediate: a strictly larger function space still separates
    all measures that the smaller one did.

    **Lean-to-math alignment.**
    Same `IsCharacteristicKernel` definition. ✓
    The Neumann kernel is bounded and continuous on `[0,1]²` (compact),
    so integrals in `mmdSq` converge. ✓
    Summability prerequisite: `kernelRadNeumann_summable` (KernelFoundations). -/
axiom kernelRadNeumann_characteristic
    (β : ℝ) (hβ : 0 < β) :
    IsCharacteristicKernel (kernelRadNeumann β)

/-! ### Constant Potential of Neumann Kernel

The Neumann heat kernel on `[0,1]` has the property that its integral
against the uniform (Lebesgue) measure is constant in the first argument.
This is the key property that enables the energy-MMD identity:
  `E(P) - E(μ₀) = MMD²(P, μ₀)`.
-/

/-- The Neumann radial kernel has constant potential under `Unif[0,1]`:
    `∫₀¹ k_rad^Neum(t, t') dt' = c` for all `t ∈ [0,1]`.

    **Validation chain (3 steps).**

    Step 1 — Eigenfunction expansion of the Neumann heat kernel on `[0,L]`:
    `K(t,t') = (1/L) + (2/L) Σ_{k≥1} exp(-μₖτ) cos(kπt/L) cos(kπt'/L)`.
    For `L = 1`: `K(t,t') = 1 + 2 Σ_{k≥1} exp(-βk²π²) cos(kπt) cos(kπt')`.
    (The Lean definition uses the image-sum representation, which is related
    by Poisson summation; the eigenfunction form is used for the proof.)
    Open-access: Foondun (2015), ALEA, §2 (explicit Neumann expansion).
    https://alea.impa.br/articles/v12/12-22.pdf
    Book: Evans (2010), *Partial Differential Equations*, §2.3.
    Historical: Fulks (1953), *Pacific J. Math.* 3(3) (Neumann Green's fn).
    https://msp.org/pjm/1953/3-3/pjm-v3-n3-p05-s.pdf

    Step 2 — Cosine orthogonality: `∫₀¹ cos(kπt') dt' = 0` for all
    `k ≥ 1`. This is standard calculus: `sin(kπ)/(kπ) = 0`.

    Step 3 — Exchange sum and integral: justified by dominated convergence
    (each term bounded by `2·exp(-βk²π²)`, which sums to a finite constant).
    After exchange, only the `k = 0` constant mode survives:
    `∫₀¹ K(t,t') dt' = 1` for all `t` (up to the normalization constant
    from the image-sum vs eigenfunction representations).

    **Lean-to-math alignment.**
    `HasConstantPotential K μ c` = `∀ w, kernelPotential K μ w = c`. ✓
    `uniform01` = Lebesgue measure on `[0,1]`. ✓
    The axiom asserts `∃ c` (not a specific value). This is sufficient for
    the energy-MMD identity, which only needs constancy. ✓
    The integral `∫ t', kernelRadNeumann β t t' ∂volume` is well-defined
    because the Neumann kernel is bounded and measurable on `[0,1]`. ✓ -/
axiom neumannPotential_constant
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ,
      HasConstantPotential (kernelRadNeumann β) uniform01 c

end WristbandLossProofs
