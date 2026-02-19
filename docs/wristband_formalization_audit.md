# Wristband Formalization Audit (Lean vs. `ml-tidbits`)

Date: 2026-02-19
Audited scope: **axioms, definitions, and lemma/theorem statements** (not proof terms).

## 1. Sources Reviewed

- Lean:
  - `WristbandLossProofs/Foundations.lean`
  - `WristbandLossProofs/ImportedFacts.lean`
  - `WristbandLossProofs/Equivalence.lean`
- Local docs in this repo:
  - `docs/wristband_post.md`
  - `docs/wristband_proof_plan.md`
- Original Python implementation (local clone):
  - `ml-tidbits/python/embed_models/EmbedModels.py`
  - `ml-tidbits/docs/wristband.md`
  - `ml-tidbits/python/tests/DeterministicGAE.py`

## 2. Mapping to Python code

The Python loss in `EmbedModels.py` implements the following idealized math:

### 2.1 Wristband map

For $x \in \mathbb{R}^d$, define

$$
s(x) = \|x\|^2, \qquad
u(x) = \frac{x}{\|x\|}, \qquad
t(x) = F_{\chi^2_d}(s(x)).
$$

In code:
- `s = x.square().sum(...)` (`line 749`)
- `u = x * rsqrt(s)` (`line 750`)
- `t = torch.special.gammainc(d/2, s/2)` (`line 752`)

with numerical clamping to avoid boundary/zero instability.

### 2.2 Joint reflected kernel term (main repulsion)

Angular factor:

$$
k_{\mathrm{ang}}(u_i,u_j)
= \exp\!\left(-\beta \alpha^2 \,\delta_{\mathrm{ang}}(u_i,u_j)^2\right)
$$

where $\delta_{\mathrm{ang}}$ is chordal or geodesic distance depending on mode.

Radial reflected factor (3 images on $[0,1]$):

$$
\begin{aligned}
k_{\mathrm{rad}}(t_i,t_j)
&= e^{-\beta(t_i-t_j)^2} \\
&\quad + e^{-\beta(t_i+t_j)^2} \\
&\quad + e^{-\beta(t_i+t_j-2)^2}.
\end{aligned}
$$

Joint kernel:

$$
K\!\big((u_i,t_i),(u_j,t_j)\big)
= k_{\mathrm{ang}}(u_i,u_j)\,k_{\mathrm{rad}}(t_i,t_j).
$$

Code lines:
- angular exponent: `764-770`
- reflected differences `diff0,diff1,diff2`: `787-789`
- aggregation: `791-804`

### 2.3 Extra terms in Python objective

Radial quantile term:

$$
L_{\mathrm{rad}}
= 12 \cdot \frac{1}{n}\sum_{i=1}^n
\left(t_{(i)} - q_i\right)^2,
\qquad
q_i = \frac{i-\tfrac12}{n}.
$$

Implemented at `line 759` (0-based equivalent $q_i=(i+0.5)/n$).

Default moment term (`w2`):

$$
W_2^2(\mathcal N(\mu,\Sigma),\mathcal N(0,I))
= \|\mu\|^2 + \sum_{k=1}^d (\sqrt{\lambda_k}-1)^2,
$$

with $\lambda_k$ eigenvalues of $\Sigma$, implemented in `451-517`, used at `712`.

Calibration:

$$
\widehat{L}_c = \frac{L_c - m_c}{s_c},
\qquad
L_{\mathrm{total}}
= \frac{
\widehat{L}_{\mathrm{rep}}
 + \lambda_{\mathrm{rad}}\widehat{L}_{\mathrm{rad}}
 + \lambda_{\mathrm{ang}}\widehat{L}_{\mathrm{ang}}
 + \lambda_{\mathrm{mom}}\widehat{L}_{\mathrm{mom}}
}{s_{\mathrm{total}}}.
$$

Implemented in `631-684` and `827-834`.

This target matches the narrative in `docs/wristband_proof_plan.md`.

## 3. Executive Assessment

Current Lean formalization is a good scaffold for Section 2 (wristband equivalence).  
The current statement-level mismatches are listed below.

### 3.1 High-priority gap A: `sphericalLaw_determinedByRadius` is only extensional rewrite

Current theorem:

$$
\text{radiusSqLaw}_1 = \text{radiusSqLaw}_2
\implies
\text{sphericalLaw}(\text{radiusSqLaw}_1)=\text{sphericalLaw}(\text{radiusSqLaw}_2).
$$

This is a definitional rewrite, not the identification theorem in the proof plan.

What the proof plan needs is logically stronger:

$$
\begin{aligned}
&U \sim \sigma_{d-1},\; U \perp S_1,\; U \perp S_2,\; S_1,S_2 \ge 0,\;
\mathcal{L}(S_1)=\mathcal{L}(S_2) \\
&\Longrightarrow
\mathcal{L}(\sqrt{S_1}U)=\mathcal{L}(\sqrt{S_2}U),
\end{aligned}
$$

and in practice one also needs a converse/uniqueness style statement to recover law equality from radial data.

Why this audit call is correct: the current header cannot be used to infer anything from independence + uniform direction assumptions; it only rewrites equal arguments.

### 3.2 High-priority gap B: missing CDF contract for `chiSqCDFToUnit`

You currently have:
- `chiSqRadiusLaw : Distribution NNReal`
- `chiSqCDFToUnit : NNReal -> UnitInterval`

but no axiom connecting them as CDF.

Needed bridge (at least):

$$
(F_d(x):\mathbb{R}) = F_{\chi^2_d}(x)
= \mathbb{P}_{S\sim \chi^2_d}(S \le x),
$$

where $F_d := \operatorname{chiSqCDFToUnit}_d$.

plus continuity and strict monotonicity assumptions for PIT reverse use.

Without this, PIT cannot be instantiated:

$$
S \sim \chi^2_d
\;\not\!\!\Rightarrow\;
F_d(S)\sim \mathrm{Unif}(0,1)
$$

for an arbitrary function into $[0,1]$.

Why this audit call is correct: PIT is a theorem about a specific CDF $F$, not any bounded map.

### 3.3 High-priority gap C: `Distribution := Measure` is too weak for theorem headers

Many declarations quantify over arbitrary measures. But all target statements are probability-law statements.

Core fact:

$$
(f_\#\mu)(\text{target space}) = \mu(\text{source space}).
$$

So if $\mu(\Omega)\neq 1$, the pushforward cannot equal a probability distribution like uniform law.

Why this audit call is correct: equivalence theorems compare to probability targets ($\mu_0$, Gaussian law), so total mass constraints are semantically required.

### 3.4 Medium-priority gap D: missing dimension assumptions

Proof plan is stated for $d \ge 2$. Current headers use unrestricted `d : Nat`.

Geometric target is

$$
S^{d-1} = \{u\in \mathbb{R}^d : \|u\|=1\}.
$$

Degenerate dimensions can change measure/geometry behavior (e.g., $d=0$ gives empty sphere in this model; $d=1$ gives two-point sphere).

Why this audit call is correct: even if some Lean terms typecheck at small $d$, the intended theorem meaning in docs is higher-dimensional spherical geometry.

### 3.5 Medium-priority gap E: `gaussianNZ` abstraction is practical but under-bridged

`gaussianNZ` lives directly on nonzero vectors, which is fine operationally. But there is no formal bridge to an ambient Gaussian law $\gamma_d$ on $\mathbb{R}^d$, e.g.

$$
\mathbb{P}_{Z\sim \gamma_d}(Z=0)=0,
\qquad
(\mathrm{subtype\_val})_\#(\gamma_d|_{\mathbb{R}^d\setminus\{0\}})
= \gamma_d.
$$

Why this audit call is correct: without this bridge, statements involving `gaussianNZ` are internally consistent but less reusable/transparent against standard Gaussian theorems.

## 4. Declaration-by-Declaration Mapping (Expanded)

## 4.1 Geometry and wristband space

Lean:

```lean
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}
```

Math target:

$$
\mathcal{W}_d = S^{d-1}\times[0,1],\qquad
\Phi:\mathbb{R}^d\setminus\{0\}\to\mathcal{W}_d.
$$

Verdict: **Correct abstraction**.

Why: type-level model matches the idealized domain/codomain of the wristband map.

## 4.2 Direction and squared radius

Lean:

```lean
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal := ⟨‖z.1‖ ^ 2, by positivity⟩
noncomputable def direction {d : ℕ} (z : VecNZ d) : Sphere d := ...
```

Math target:

$$
S(z)=\|z\|^2,\qquad U(z)=\frac{z}{\|z\|}.
$$

Verdict: **Correct**.

Why: this is exactly the Python decomposition before numerical clamping.

## 4.3 Target uniform law on wristband

Lean:

```lean
def uniform01 : Distribution UnitInterval := (volume : Measure UnitInterval)
noncomputable def sphereUniform (d : ℕ) : Distribution (Sphere d) := ...
def wristbandUniform (d : ℕ) : Distribution (Wristband d) :=
  productLaw (sphereUniform d) uniform01
```

Math target:

$$
\mu_0 = \sigma_{d-1}\otimes \lambda_{[0,1]}.
$$

Verdict: **Mostly correct**.

Why: product structure is right. Remaining concern is assumption hygiene (probability + dimension) in theorem headers that use this law.

## 4.4 Imported Gaussian polar package

Lean:

```lean
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval
axiom gaussianPolar_direction_uniform (d : ℕ) : ...
axiom gaussianPolar_radius_chiSq (d : ℕ) : ...
axiom gaussianPolar_independent (d : ℕ) : ...
```

Math target:

$$
Z\sim\gamma_d
\;\Rightarrow\;
U=\frac{Z}{\|Z\|}\sim \sigma_{d-1},\;
S=\|Z\|^2\sim\chi^2_d,\;
U\perp S.
$$

Verdict: **Conceptually correct, contract incomplete**.

Why: the structural facts are present, but CDF linkage and probability assumptions are not explicit.

## 4.5 PIT theorem shape

Lean:

```lean
theorem probabilityIntegralTransform ... :
  pushforward F μ = uniform01 := by sorry

theorem probabilityIntegralTransform_reverse ... :
  observedLaw = targetLaw := by sorry
```

Math target:

$$
X\sim \mu,\; F=F_\mu \text{ continuous}
\;\Rightarrow\;
F(X)\sim \mathrm{Unif}(0,1),
$$

$$
U\sim \mathrm{Unif}(0,1),\; F \text{ strictly increasing CDF}
\;\Rightarrow\;
F^{-1}(U)\sim \mu.
$$

Verdict: **Right theorem shape, missing instantiation hooks**.

Why: for wristband equivalence, one must prove/assume that `chiSqCDFToUnit d` is exactly the CDF of `chiSqRadiusLaw d` with required regularity.

## 4.6 Wristband map and pushforward law

Lean:

```lean
def wristbandMap (d : ℕ) (z : VecNZ d) : Wristband d :=
  (direction (d := d) z, chiSqCDFToUnit d (radiusSq z))

def wristbandLaw (d : ℕ) (Q : Distribution (VecNZ d)) : Distribution (Wristband d) :=
  pushforward (wristbandMap d) Q
```

Math target:

$$
\Phi(z)=\left(\frac{z}{\|z\|},\,F_{\chi^2_d}(\|z\|^2)\right),\qquad
P_Q = \Phi_\# Q.
$$

Verdict: **Correct abstraction**.

Why: declaration-level map is exactly the target map modulo missing CDF-link axiom.

## 4.7 `sphericalLaw_determinedByRadius`

Current Lean theorem:

$$
\text{radiusSqLaw}_1=\text{radiusSqLaw}_2
\implies
\text{sphericalLaw}(\text{radiusSqLaw}_1)=\text{sphericalLaw}(\text{radiusSqLaw}_2).
$$

Proof-plan need:

$$
P_{(U,S)} = \sigma_{d-1}\otimes \nu
\Longrightarrow
\mathcal{L}(\sqrt{S}U) \text{ is uniquely determined by } \nu.
$$

Equivalent practical form:

$$
\mathcal{L}(S_1)=\mathcal{L}(S_2)
\Longrightarrow
\mathcal{L}(\sqrt{S_1}U)=\mathcal{L}(\sqrt{S_2}U)
$$

for $U\sim \sigma_{d-1}$, independent from each $S_i$.

Verdict: **Placeholder only**.

Why: current statement has no independence/uniform-direction hypotheses.

## 4.8 Wristband equivalence headers

Lean:

```lean
theorem wristbandEquivalence_forward (d : ℕ) :
  wristbandLaw d (gaussianNZ d) = wristbandUniform d := by sorry

theorem wristbandEquivalence_backward
    (d : ℕ) (Q : Distribution (VecNZ d))
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by sorry
```

Math target:

$$
\Phi_\# Q = \mu_0
\iff
Q=\gamma_d
\quad(\text{on } \mathbb{R}^d\setminus\{0\} \text{ model}).
$$

Verdict: **Correct high-level shape**.

Why not fully correct yet:
- depends on CDF-link axioms and PIT instantiation,
- should carry probability/dimension assumptions explicitly.

## 5. Coverage vs Python Objective (What Is and Is Not Formalized Yet)

Statement-level currently represented in Lean:
- Wristband map $\Phi$.
- Target wristband uniform law $\mu_0$.
- Imported Gaussian polar ingredients.
- PIT theorem shapes.
- Equivalence theorem skeleton.

Statement-level not yet represented from Python objective:

1. Reflected kernel definition:

$$
K((u,t),(u',t'))
= e^{-\beta\alpha^2\delta(u,u')^2}
\left[
e^{-\beta(t-t')^2}
+e^{-\beta(t+t')^2}
+e^{-\beta(t+t'-2)^2}
\right].
$$

2. Population repulsion energy/objective:

$$
\mathcal{E}(P)=\mathbb{E}_{W,W'\sim P}[K(W,W')],
\qquad
\mathcal{L}_{\mathrm{rep}}(P)=\frac1\beta\log\mathcal{E}(P).
$$

3. Radial quantile penalty:

$$
\mathcal{L}_{\mathrm{rad}}
=12\cdot\frac1n\sum_{i=1}^n(t_{(i)}-q_i)^2.
$$

4. Moment penalty (default $W_2$ term), and alternatives.

5. Calibration/z-score composition formulas.

This is consistent with the project status table in `docs/wristband_proof_plan.md`.

## 6. Recommended Header-Level Corrections (Before Proof Terms)

1. Add explicit CDF bridge axioms for chi-square map:
   - `IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d)`
   - `IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d)`

2. Strengthen probability assumptions in theorem headers:
   - Either make `Distribution` a probability-law type.
   - Or add `[IsProbabilityMeasure ...]` systematically.

3. Add dimension assumptions where intended by theory:
   - at least `2 <= d` for spherical-uniform geometric statements.

4. Replace placeholder identification theorem with a statement matching proof-plan logic:
   - uniform direction + independence + radius law determine spherical law.

5. Optionally add bridge between ambient Gaussian and `gaussianNZ`:
   - improves interoperability with standard Gaussian theorems.

## 7. Bottom Line

The remaining blockers for exact statement-level alignment with the Python target are:

1. placeholder identification lemma too weak for backward equivalence,
2. missing CDF/probability assumption bridges needed for PIT-based reasoning.

Once those are corrected at the header/axiom level, the formalization will be in the right shape to proceed to proof implementation.
