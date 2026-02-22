import WristbandLossProofs.Equivalence
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory
open scoped BigOperators

/-! ## Kernel Definitions

These definitions encode the repulsion kernel used in the wristband loss.

Python side (`ml-tidbits/.../EmbedModels.py`):
- The kernel is a product of an angular factor and a radial factor.
- Angular: Gaussian RBF in chordal distance on the sphere (lines 762–765).
- Radial: 3-image boundary-reflected Gaussian on [0,1] (lines 784–789).
- Joint repulsion loss: `(1/β) · log(mean kernel value)` (lines 791–804).

The kernel is parametric in `β > 0` (bandwidth) and `α > 0` (angular scale).
The specific `α` calibration (matching expected pairwise distances) is a
practical design choice; the uniqueness theorem holds for all `α > 0, β > 0`.
-/

/-! ### Inner product on the sphere

Python computes `g = u @ u.T` (line 762), which is `⟨u, u'⟩` for unit vectors.
We extract the inner product from the ambient Euclidean space. -/

/-- Inner product of two points on the unit sphere, computed in ambient `ℝ^d`.
    Python: `g = (u @ u.transpose(-1, -2))` (EmbedModels.py:762). -/
def sphereInner {d : ℕ} (u u' : Sphere d) : ℝ :=
  @inner ℝ (Vec d) _ u.1 u'.1

/-! ### Angular kernel (chordal distance)

Python (EmbedModels.py:764–765):
```python
e_ang = (2. * self.beta_alpha2) * (g - 1.)
# then exp(e_ang) is used in the kernel
```

Since `‖u - u'‖² = 2 - 2⟨u,u'⟩` for unit vectors,
`exp(-β·α²·‖u-u'‖²) = exp(2·β·α²·(⟨u,u'⟩ - 1))`.
-/

/-- Angular kernel factor: Gaussian RBF in chordal distance on the sphere.
    `k_ang(u, u') = exp(2·β·α²·(⟨u,u'⟩ - 1)) = exp(-β·α²·‖u-u'‖²)`.
    Python: `exp((2. * beta_alpha2) * (g - 1.))` (EmbedModels.py:764–765). -/
noncomputable def kernelAngChordal
    {d : ℕ} (β α : ℝ) (u u' : Sphere d) : ℝ :=
  Real.exp (2 * β * α ^ 2 * (sphereInner u u' - 1))

/-! ### Radial kernel (3-image boundary reflection)

Python (EmbedModels.py:785–789):
```python
diff0 = tc - tr           # t_i - t_j
diff1 = tc + tr            # t_i + t_j   (image at -t_j)
diff2 = diff1 - 2          # t_i + t_j - 2  (image at 2 - t_j)
```

Each difference is squared, scaled by `-β`, exponentiated, and summed.
This is a truncation of the infinite Neumann reflection series, keeping
the 3 closest images. It corrects boundary bias in kernel density
estimation on the bounded interval [0,1].
-/

/-- Radial kernel factor: 3-image boundary-reflected Gaussian on `[0,1]`.
    `k_rad(t, t') = exp(-β(t-t')²) + exp(-β(t+t')²) + exp(-β(t+t'-2)²)`.
    Python: three `exp(addcmul(e_ang, diff_i, diff_i, value=-beta))`
    (EmbedModels.py:792–794, 799–801). -/
noncomputable def kernelRad3Image
    (β : ℝ) (t t' : UnitInterval) : ℝ :=
  let s := (t : ℝ)
  let s' := (t' : ℝ)
  Real.exp (-β * (s - s') ^ 2) +
  Real.exp (-β * (s + s') ^ 2) +
  Real.exp (-β * (s + s' - 2) ^ 2)

/-! ### Neumann radial kernel (infinite reflection series)

The mathematical idealization of the 3-image kernel: the full infinite
sum over all reflected images. This is the heat kernel on `[0,1]` with
Neumann (reflecting) boundary conditions.

`k_rad^Neum(t, t') = Σ_{n ∈ ℤ} [exp(-β(t-t'-2n)²) + exp(-β(t+t'-2n)²)]`

The 3-image kernel keeps only the `n = 0` terms (plus `n = -1` for the
third term). The omitted terms contribute `O(exp(-4β))`.

The key property: this kernel has **exactly constant potential** under
the uniform measure, because uniform is the stationary distribution
of reflected Brownian motion on `[0,1]`.
-/

/-- Neumann radial kernel: infinite reflection series on `[0,1]`.
    This has exactly constant potential under the uniform measure.
    Truncating to 3 images gives `kernelRad3Image`. -/
noncomputable def kernelRadNeumann
    (β : ℝ) (t t' : UnitInterval) : ℝ :=
  let s := (t : ℝ)
  let s' := (t' : ℝ)
  ∑' (n : ℤ),
    (Real.exp (-β * (s - s' - 2 * n) ^ 2) +
     Real.exp (-β * (s + s' - 2 * n) ^ 2))

/-- The summand in the Neumann kernel is summable over `ℤ` for `β > 0`.

    This ensures `kernelRadNeumann` (defined via `tsum`) computes the
    intended infinite series rather than returning 0 by convention.

    Proof sketch: for `|n| ≥ 1` and `t, t' ∈ [0,1]`, each exponent
    satisfies `(t - t' - 2n)² ≥ (2|n| - 2)²`, so
    `exp(-β(t-t'-2n)²) ≤ exp(-β(2|n|-2)²)`. The tails are dominated
    by `exp(-4β(|n|-1)²) ≤ exp(-4β(|n|-1))` for `|n| ≥ 2`, a geometric
    series that converges for `β > 0`.

    Mathlib route used below: dominate each shifted Gaussian term by
    the standard Jacobi-theta bound
    `exp(-π (T·n² - 2·S·|n|))` with `T = 4β/π > 0`, then apply
    `summable_pow_mul_jacobiTheta₂_term_bound` (with `k = 0`). -/
lemma kernelRadNeumann_summable
    (β : ℝ) (hβ : 0 < β) (t t' : UnitInterval) :
    Summable (fun n : ℤ =>
      Real.exp (-β * ((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2) +
      Real.exp (-β * ((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2)) := by
  let a : ℝ := (t : ℝ) - (t' : ℝ)
  let b : ℝ := (t : ℝ) + (t' : ℝ)

  have hT : 0 < 4 * β / Real.pi := by positivity

  have hboundSummable (c : ℝ) :
      Summable (fun n : ℤ =>
        Real.exp (-Real.pi *
          ((4 * β / Real.pi) * n ^ 2 - 2 * (2 * β * |c| / Real.pi) * |n|))) := by
    simpa [pow_zero, one_mul] using
      (summable_pow_mul_jacobiTheta₂_term_bound
        (S := 2 * β * |c| / Real.pi) (T := 4 * β / Real.pi) (k := 0) hT)

  have hshiftSummable (c : ℝ) :
      Summable (fun n : ℤ => Real.exp (-β * (c - 2 * n) ^ 2)) := by
    refine (hboundSummable c).of_nonneg_of_le (fun n => Real.exp_nonneg _) ?_
    intro n
    refine (Real.exp_le_exp).2 ?_
    have hconst : -β * c ^ 2 ≤ 0 := by nlinarith [hβ, sq_nonneg c]
    have hcross : 4 * β * c * (n : ℝ) ≤ 4 * β * |c| * |(n : ℝ)| := by
      have hcn : c * (n : ℝ) ≤ |c| * |(n : ℝ)| := by
        simpa [abs_mul] using (le_abs_self (c * (n : ℝ)))
      have h4β : 0 ≤ 4 * β := by nlinarith [hβ]
      nlinarith [hcn, h4β]
    have hmain :
        -β * (c - 2 * n) ^ 2 ≤
          -4 * β * (n : ℝ) ^ 2 + 4 * β * |c| * |(n : ℝ)| := by
      have hexpand :
          -β * (c - 2 * n) ^ 2 =
            -β * c ^ 2 + 4 * β * c * (n : ℝ) - 4 * β * (n : ℝ) ^ 2 := by
        ring
      nlinarith [hexpand, hconst, hcross]
    have hrewrite :
        -Real.pi *
            ((4 * β / Real.pi) * n ^ 2 - 2 * (2 * β * |c| / Real.pi) * |n|) =
          -4 * β * (n : ℝ) ^ 2 + 4 * β * |c| * |(n : ℝ)| := by
      rw [Int.cast_abs]
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      field_simp [hpi]
      ring
    exact hmain.trans_eq hrewrite.symm

  have ha : Summable (fun n : ℤ => Real.exp (-β * (a - 2 * n) ^ 2)) := hshiftSummable a
  have hb : Summable (fun n : ℤ => Real.exp (-β * (b - 2 * n) ^ 2)) := hshiftSummable b
  exact ha.add hb

/-! ### Joint wristband kernels

The full kernel on `Wristband d = S^{d-1} × [0,1]` is the product of the
angular and radial factors. Python computes this implicitly: the exponents
`e_ang` and `-β·diff²` are added before exponentiation, which is equivalent
to multiplying the two kernel factors.
-/

/-- Joint wristband kernel (3-image radial): `K(w,w') = k_ang · k_rad`.
    This is the kernel actually computed in Python (EmbedModels.py:792–801). -/
noncomputable def wristbandKernel
    {d : ℕ} (β α : ℝ) (w w' : Wristband d) : ℝ :=
  kernelAngChordal β α w.1 w'.1 * kernelRad3Image β w.2 w'.2

/-- Joint wristband kernel (Neumann radial): mathematical idealization
    with exactly constant potential. -/
noncomputable def wristbandKernelNeumann
    {d : ℕ} (β α : ℝ) (w w' : Wristband d) : ℝ :=
  kernelAngChordal β α w.1 w'.1 * kernelRadNeumann β w.2 w'.2

/-! ## Kernel Energy and MMD

These definitions formalize the population-level loss that the Python code
approximates with finite batches.

The repulsion loss (EmbedModels.py:797/804) is:
  `rep_loss = (1/β) · log(mean_kernel_value)`
which in the population limit becomes `(1/β) · log(E_{W,W'~P}[K(W,W')])`.

Since `(1/β) · log(·)` is strictly increasing, minimizing the loss is
equivalent to minimizing the kernel energy `E_{W,W'~P}[K(W,W')]`.
-/

/-- Kernel energy: expected kernel value under `P ⊗ P`.
    `E(P) = E_{W,W' ~ P}[K(W, W')]`.
    Python: `mean_k` in the loss computation (EmbedModels.py:796/803). -/
noncomputable def kernelEnergy
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (P : Distribution X) : ℝ :=
  ∫ w, ∫ w', K w w' ∂(P : Measure X) ∂(P : Measure X)

/-- Kernel potential: expected kernel value with one argument fixed.
    `h(w) = E_{W' ~ μ}[K(w, W')]`.
    When this is constant in `w`, the energy-MMD identity holds. -/
noncomputable def kernelPotential
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (μ : Distribution X) (w : X) : ℝ :=
  ∫ w', K w w' ∂(μ : Measure X)

/-- Maximum Mean Discrepancy squared between `P` and `Q` under kernel `K`.
    `MMD²(P, Q) = E_{P⊗P}[K] - 2·E_{P⊗Q}[K] + E_{Q⊗Q}[K]`. -/
noncomputable def mmdSq
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (P Q : Distribution X) : ℝ :=
  kernelEnergy K P -
  2 * ∫ w, ∫ w', K w w' ∂(Q : Measure X) ∂(P : Measure X) +
  kernelEnergy K Q

/-! ## Kernel Predicates

These predicates state the key properties needed for the energy
minimization argument. -/

/-- A kernel `K` is positive semi-definite: for any finite collection
    of points, the Gram matrix `[K(x_i, x_j)]` is PSD. -/
def IsPosSemiDefKernel
    {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
    ∑ i, ∑ j, c i * c j * K (x i) (x j) ≥ 0

/-- A PSD kernel `K` is characteristic: `MMD²(P, Q) = 0` implies
    `P = Q`. Equivalently, the kernel embedding is injective. -/
def IsCharacteristicKernel
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) : Prop :=
  ∀ (P Q : Distribution X), mmdSq K P Q = 0 → P = Q

/-- The potential function `h(w) = E_{W'~μ}[K(w,W')]` is constant.
    This is the key property that turns energy minimization into MMD. -/
def HasConstantPotential
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (μ : Distribution X) (c : ℝ) : Prop :=
  ∀ w : X, kernelPotential K μ w = c

/-! ### Universality Scaffold

These definitions are local foundations for expressing imported universality
results and for deriving characteristicness statements.
-/

/-- A finite linear combination of kernel sections `K(x_i, ·)`. -/
def IsKernelSectionLinearCombination
    {X : Type*} (K : X → X → ℝ) (f : X → ℝ) : Prop :=
  ∃ (n : ℕ) (coeff : Fin n → ℝ) (center : Fin n → X),
    ∀ x : X, f x = ∑ i, coeff i * K (center i) x

/-- Universality scaffold on compact spaces: kernel sections are uniformly dense
in continuous real-valued functions. -/
def IsUniversalKernel
    {X : Type*} [TopologicalSpace X] (K : X → X → ℝ) : Prop :=
  ∀ f : C(X, ℝ), ∀ ε : ℝ, 0 < ε →
    ∃ g : C(X, ℝ),
      IsKernelSectionLinearCombination K g ∧
      (∀ x : X, |f x - g x| < ε)

/-! ## Basic Properties (scaffold — proofs deferred)

These are straightforward consequences of the definitions.
-/

/-- The angular kernel is symmetric. -/
lemma kernelAngChordal_symmetric
    {d : ℕ} (β α : ℝ) (u u' : Sphere d) :
    kernelAngChordal β α u u' = kernelAngChordal β α u' u := by
  simp [kernelAngChordal, sphereInner, real_inner_comm]

/-- The 3-image radial kernel is symmetric. -/
lemma kernelRad3Image_symmetric
    (β : ℝ) (t t' : UnitInterval) :
    kernelRad3Image β t t' = kernelRad3Image β t' t := by
  unfold kernelRad3Image
  ring_nf

/-- The angular kernel takes values in `[0, 1]` for `β·α² ≥ 0`. -/
lemma kernelAngChordal_nonneg
    {d : ℕ} (β α : ℝ) (_hβα : 0 ≤ β * α ^ 2)
    (u u' : Sphere d) :
    0 ≤ kernelAngChordal β α u u' := by
  simpa [kernelAngChordal] using
    (Real.exp_nonneg (2 * β * α ^ 2 * (sphereInner u u' - 1)))

/-- The 3-image radial kernel is nonneg (sum of exponentials). -/
lemma kernelRad3Image_nonneg
    (β : ℝ) (t t' : UnitInterval) :
    0 ≤ kernelRad3Image β t t' := by
  unfold kernelRad3Image
  positivity

/-- Measurability of the angular kernel (fixed parameters). -/
lemma measurable_kernelAngChordal
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Sphere d × Sphere d =>
      kernelAngChordal β α p.1 p.2) := by
  unfold kernelAngChordal sphereInner
  have hInner : Measurable (fun p : Sphere d × Sphere d => @inner ℝ (Vec d) _ p.1.1 p.2.1) := by
    exact (continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd) |>.measurable
  exact (Real.continuous_exp.measurable.comp
    ((measurable_const.mul measurable_const).mul (hInner.sub measurable_const)))

/-- Measurability of the 3-image radial kernel (fixed β). -/
lemma measurable_kernelRad3Image
    (β : ℝ) :
    Measurable (fun p : UnitInterval × UnitInterval =>
      kernelRad3Image β p.1 p.2) := by
  let s : UnitInterval × UnitInterval → ℝ := fun p => (p.1 : ℝ)
  let s' : UnitInterval × UnitInterval → ℝ := fun p => (p.2 : ℝ)
  have hs : Measurable s := by
    simpa [s] using (continuous_subtype_val.comp continuous_fst).measurable
  have hs' : Measurable s' := by
    simpa [s'] using (continuous_subtype_val.comp continuous_snd).measurable
  have h1 : Measurable (fun p => Real.exp (-(β * (s p - s' p) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul ((hs.sub hs').pow_const 2)).neg)
  have h2 : Measurable (fun p => Real.exp (-(β * (s p + s' p) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul ((hs.add hs').pow_const 2)).neg)
  have h3 : Measurable (fun p => Real.exp (-(β * (s p + s' p - 2) ^ 2))) := by
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul (((hs.add hs').sub measurable_const).pow_const 2)).neg)
  simpa [kernelRad3Image, s, s', add_assoc] using h1.add (h2.add h3)

/-- Measurability of the joint wristband kernel. -/
lemma measurable_wristbandKernel
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Wristband d × Wristband d =>
      wristbandKernel β α p.1 p.2) := by
  let gAng : Wristband d × Wristband d → Sphere d × Sphere d :=
    fun p => (p.1.1, p.2.1)
  let gRad : Wristband d × Wristband d → UnitInterval × UnitInterval :=
    fun p => (p.1.2, p.2.2)
  have hgAng : Measurable gAng := by
    exact measurable_fst.fst.prodMk measurable_snd.fst
  have hgRad : Measurable gRad := by
    exact measurable_fst.snd.prodMk measurable_snd.snd
  have hAngW : Measurable (fun p : Wristband d × Wristband d => kernelAngChordal β α p.1.1 p.2.1) := by
    simpa [gAng] using (measurable_kernelAngChordal (d := d) β α).comp hgAng
  have hRadW : Measurable (fun p : Wristband d × Wristband d => kernelRad3Image β p.1.2 p.2.2) := by
    simpa [gRad] using (measurable_kernelRad3Image β).comp hgRad
  simpa [wristbandKernel] using hAngW.mul hRadW

/-- Measurability of the Neumann wristband kernel. -/
lemma measurable_wristbandKernelNeumann
    {d : ℕ} (β α : ℝ) :
    Measurable (fun p : Wristband d × Wristband d =>
      wristbandKernelNeumann β α p.1 p.2) := by
  sorry

/-- When the potential is constant, the energy-MMD identity holds:
    `E(P) - E(μ₀) = MMD²(P, μ₀)`. -/
theorem energy_eq_mmdSq_of_constantPotential
    {X : Type*} [MeasurableSpace X]
    (K : X → X → ℝ) (μ₀ : Distribution X) (c : ℝ)
    (hConst : HasConstantPotential K μ₀ c)
    (P : Distribution X) :
    kernelEnergy K P - kernelEnergy K μ₀ = mmdSq K P μ₀ := by
  have hCross :
      (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X)) = c := by
    calc
      (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X))
          = ∫ w, kernelPotential K μ₀ w ∂(P : Measure X) := by rfl
      _ = ∫ w, c ∂(P : Measure X) := by
            refine integral_congr_ae ?_
            filter_upwards with w
            exact hConst w
      _ = c := by simp
  have hEnergyμ₀ : kernelEnergy K μ₀ = c := by
    calc
      kernelEnergy K μ₀ = ∫ w, kernelPotential K μ₀ w ∂(μ₀ : Measure X) := by rfl
      _ = ∫ w, c ∂(μ₀ : Measure X) := by
            refine integral_congr_ae ?_
            filter_upwards with w
            exact hConst w
      _ = c := by simp
  calc
    kernelEnergy K P - kernelEnergy K μ₀
        = kernelEnergy K P - c := by simp [hEnergyμ₀]
    _ = kernelEnergy K P - 2 * c + c := by ring
    _ = kernelEnergy K P -
          2 * (∫ w, ∫ w', K w w' ∂(μ₀ : Measure X) ∂(P : Measure X)) +
          kernelEnergy K μ₀ := by simp [hCross, hEnergyμ₀]
    _ = mmdSq K P μ₀ := by rfl

/-! ## Kernel-Theory Scaffolding (local/deferred proofs)

These are project-level targets intended to be proven in-repo. They are not
imported axioms.
-/

/-- PSD closure route for Neumann kernel from cosine expansion:
rank-1 PSD modes + nonnegative coefficients + convergent series. -/
lemma kernelRadNeumann_posSemiDef
    (β : ℝ) (hβ : 0 < β) :
    IsPosSemiDefKernel (kernelRadNeumann β) := by
  sorry

/-- Dominated-convergence / `integral_tsum` scaffold for Neumann potential:
swap `∫` and `∑'` for the image-series representation. -/
lemma integral_tsum_kernelRadNeumann
    (β : ℝ) (hβ : 0 < β) (t : UnitInterval) :
    (∫ t' : UnitInterval,
      kernelRadNeumann β t t' ∂(uniform01 : Measure UnitInterval))
      =
    ∑' n : ℤ,
      ∫ t' : UnitInterval,
        (Real.exp (-β * (((t : ℝ) - (t' : ℝ) - 2 * n) ^ 2)) +
         Real.exp (-β * (((t : ℝ) + (t' : ℝ) - 2 * n) ^ 2)))
          ∂(uniform01 : Measure UnitInterval) := by
  sorry

/-- Cosine mode orthogonality on `[0,1]` under uniform law:
`k ≥ 1` mode integrates to `0`. -/
lemma cosine_mode_integral_uniform01
    (k : ℕ) (hk : 0 < k) :
    ∫ t : UnitInterval,
      Real.cos ((k : ℝ) * Real.pi * (t : ℝ))
      ∂(uniform01 : Measure UnitInterval) = 0 := by
  sorry

/-- Stone-Weierstrass / Fourier-density draft:
finite cosine sums approximate any continuous function on `[0,1]`. -/
lemma cosine_span_uniformly_dense_on_unitInterval
    (f : C(UnitInterval, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ coeff : Fin n → ℝ, ∃ freq : Fin n → ℕ,
      ∀ t : UnitInterval,
        |f t - ∑ i, coeff i * Real.cos ((freq i : ℝ) * Real.pi * (t : ℝ))| < ε := by
  sorry

/-- Rotational invariance of angular kernel under orthogonal actions on
sphere arguments. -/
lemma kernelAngChordal_rotationInvariant
    (d : ℕ) (β α : ℝ)
    (O : (Vec d) ≃ₗᵢ[ℝ] Vec d)
    (u u' : Sphere d) :
    kernelAngChordal (d := d) β α (rotateSphere O u) (rotateSphere O u') =
      kernelAngChordal (d := d) β α u u' := by
  unfold kernelAngChordal sphereInner rotateSphere
  simp [LinearIsometryEquiv.inner_map_map]

/-- Characteristicness of angular kernel (deferred local theorem). -/
theorem kernelAngChordal_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (kernelAngChordal (d := d) β α) := by
  sorry

/-- Characteristicness of Neumann radial kernel (deferred local theorem). -/
theorem kernelRadNeumann_characteristic
    (β : ℝ) (hβ : 0 < β) :
    IsCharacteristicKernel (kernelRadNeumann β) := by
  sorry

/-- Characteristicness of the wristband Neumann product kernel
(deferred local theorem). -/
theorem wristbandKernelNeumann_characteristic
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    IsCharacteristicKernel (wristbandKernelNeumann (d := d) β α) := by
  sorry

/-- Angular potential is constant under spherical uniform law
(deferred local theorem). -/
theorem angularPotential_constant
    (d : ℕ) (hDim : 2 ≤ d) (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) :
    ∃ c : ℝ,
      HasConstantPotential
        (kernelAngChordal (d := d) β α) (sphereUniform d) c := by
  sorry

/-- Neumann radial potential is constant under `uniform01`
(deferred local theorem). -/
theorem neumannPotential_constant
    (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ,
      HasConstantPotential (kernelRadNeumann β) uniform01 c := by
  sorry

end WristbandLossProofs
