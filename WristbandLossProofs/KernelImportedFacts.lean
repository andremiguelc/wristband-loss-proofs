import WristbandLossProofs.KernelFoundations

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! ## Imported Kernel Theory

All declarations here are `axiom`s — external mathematical results from
the kernel methods and RKHS literature, assumed without Lean proof.

Trust boundary:
- All four axioms are **relational** (equations/inequalities over
  already-defined terms). They cannot introduce new objects.
- A validator should check per axiom: does the Lean statement faithfully
  encode the cited result at the indicated source?

These axioms, together with the definitions in `KernelFoundations.lean`,
are sufficient to prove that the wristband kernel energy is uniquely
minimized at the uniform measure.
-/

/-! ### Positive Semi-Definiteness of Gaussian RBF

The Gaussian RBF `exp(-c · ‖x - y‖²)` is positive semi-definite for any
`c > 0` on any inner product space. This is a classical consequence of
Bochner's theorem: the Gaussian is the Fourier transform of a (Gaussian)
probability measure, hence is a positive definite function.

We state this for the angular kernel on the sphere (which is a Gaussian
RBF in the ambient chordal distance) and for the Neumann radial kernel
(which is a sum of Gaussian RBFs, hence PSD).
-/

/-- The angular kernel `exp(-β·α²·‖u-u'‖²)` is positive semi-definite
    on the unit sphere for any `β > 0, α > 0`.

    This is an instance of: Gaussian RBF is PSD on any subset of an inner
    product space (Bochner's theorem).

    Ref: Berlinet & Thomas-Agnan (2004), *RKHS in Probability and
    Statistics*, Thm 13 (characterization of PD functions via Fourier);
    the Gaussian `exp(-c‖·‖²)` has a nonneg Fourier transform. -/
axiom kernelAngChordal_posSemiDef
    (d : ℕ) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsPosSemiDefKernel (kernelAngChordal (d := d) β α)

/-- The Neumann radial kernel is positive semi-definite on `[0,1]`
    for any `β > 0`.

    Each term `exp(-β(t - t' - 2n)²)` is a Gaussian RBF (PSD), and
    `exp(-β(t + t' - 2n)²)` is also PSD (composition with the isometry
    `t ↦ -t`). A convergent sum of PSD kernels is PSD.

    Ref: Berlinet & Thomas-Agnan (2004), §3 (closure of PD kernels
    under sums and pointwise limits). -/
axiom kernelRadNeumann_posSemiDef
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β)

/-! ### Characteristicness

A kernel is *characteristic* if its MMD metric separates probability
measures: `MMD(P, Q) = 0 ⟹ P = Q`. For Gaussian RBF kernels, this
follows from universality: the RKHS is dense in `C(X)` for compact `X`,
which implies the kernel embedding is injective on probability measures.
-/

/-- The angular kernel (Gaussian RBF in chordal distance) is
    characteristic on `S^{d-1}` for `d ≥ 2`.

    The Gaussian RBF is a *universal* kernel on any compact metric
    space (its RKHS is dense in the continuous functions). Universal
    kernels on compact spaces are characteristic.

    Ref: Sriperumbudur, Gretton, Fukumizu, Schölkopf, Lanckriet (2010),
    "Hilbert space embeddings and metrics on probability measures",
    *JMLR* 11:1517–1561, Thm 9 + Cor 3.

    Also: Steinwart & Christmann (2008), *Support Vector Machines*,
    Thm 4.57 (Gaussian kernel is universal on compact subsets of ℝⁿ). -/
axiom kernelAngChordal_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (kernelAngChordal (d := d) β α)

/-- The Neumann radial kernel is characteristic on `[0,1]` for `β > 0`.

    The Neumann kernel is a convergent sum of Gaussian RBFs evaluated at
    reflected images. Its RKHS contains the RKHS of a single Gaussian
    RBF restricted to `[0,1]`, which is already universal (hence
    characteristic) on `[0,1]`.

    Ref: Steinwart & Christmann (2008), Thm 4.57 + Cor 4.58
    (Gaussian kernel is universal on compact subsets of ℝ);
    universality is preserved when the RKHS is enlarged. -/
axiom kernelRadNeumann_characteristic
    (β : ℝ) (hβ : 0 < β) :
    IsCharacteristicKernel (kernelRadNeumann β)

/-! ### Constant Potential of Neumann Kernel

The Neumann heat kernel on `[0,1]` has the property that its integral
against the uniform (Lebesgue) measure is constant. This is because
uniform is the stationary distribution of reflected Brownian motion:
in the eigenfunction expansion `Σ_k exp(-β·k²π²) · cos(kπt) · cos(kπt')`,
integrating any `k ≥ 1` term in `t'` gives zero (cosines integrate to 0).
Only the `k = 0` constant term survives.
-/

/-- The Neumann radial kernel has constant potential under `Unif[0,1]`:
    `∫₀¹ k_rad^Neum(t, t') dt' = c` for all `t ∈ [0,1]`.

    Mathematical basis: eigenfunction expansion of the Neumann heat
    kernel. The eigenfunctions are `{cos(kπt)}_{k≥0}` and the
    eigenvalues are `{exp(-β·k²π²)}`. Integrating `cos(kπt')` over
    `[0,1]` gives 0 for `k ≥ 1`, leaving only the constant mode.

    Ref: standard PDE result; see e.g. Evans (2010), *Partial
    Differential Equations*, §2.3 (heat equation on bounded domains
    with Neumann BC). -/
axiom neumannPotential_constant
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ,
      HasConstantPotential (kernelRadNeumann β) uniform01 c

end WristbandLossProofs
