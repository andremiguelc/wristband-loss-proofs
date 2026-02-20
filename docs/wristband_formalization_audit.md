# Wristband Formalization Audit (Lean vs. `ml-tidbits`)

Date: 2026-02-20 (updated)

## 1. Scope and Sources

Audit boundary:
- Axioms
- Definitions
- Lemma/theorem headers
- No proof-term review

Lean files:
- `WristbandLossProofs/Foundations.lean`
- `WristbandLossProofs/ImportedFacts.lean`
- `WristbandLossProofs/Equivalence.lean`

Docs:
- `docs/wristband_post.md`
- `docs/wristband_proof_plan.md`

Python source:
- `ml-tidbits/python/embed_models/EmbedModels.py`
- `ml-tidbits/docs/wristband.md`
- `ml-tidbits/python/tests/DeterministicGAE.py`

## 2. Python Mathematical Specification

### 2.1 Wristband map

For $x \in \mathbb{R}^d$:

$$
s(x) = \|x\|^2,
\qquad
u(x) = \frac{x}{\|x\|},
\qquad
t(x) = F_{\chi^2_d}(s(x)).
$$

Python anchors:
- `s = x.square().sum(...)` in `ml-tidbits/python/embed_models/EmbedModels.py:749`
- `u = x * rsqrt(s)` in `ml-tidbits/python/embed_models/EmbedModels.py:750`
- `t = torch.special.gammainc(d/2, s/2)` in `ml-tidbits/python/embed_models/EmbedModels.py:752`

### 2.2 Joint reflected kernel

Angular term:

$$
k_{\mathrm{ang}}(u_i,u_j)
= \exp\!\left(-\beta\alpha^2\,\delta_{\mathrm{ang}}(u_i,u_j)^2\right),
$$

with $\delta_{\mathrm{ang}}$ chordal or geodesic.

Reflected radial term:

$$
\begin{aligned}
k_{\mathrm{rad}}(t_i,t_j)
&= e^{-\beta(t_i-t_j)^2} +
e^{-\beta(t_i+t_j)^2} +
e^{-\beta(t_i+t_j-2)^2}.
\end{aligned}
$$

Joint kernel:

$$
K\big((u_i,t_i),(u_j,t_j)\big)
= k_{\mathrm{ang}}(u_i,u_j)\,k_{\mathrm{rad}}(t_i,t_j).
$$

Python anchors:
- Angular exponent in `ml-tidbits/python/embed_models/EmbedModels.py:762`
- Reflected differences `diff0,diff1,diff2` in `ml-tidbits/python/embed_models/EmbedModels.py:787`
- Kernel aggregation in `ml-tidbits/python/embed_models/EmbedModels.py:792`

### 2.3 Additional objective terms

Radial quantile penalty:

$$
L_{\mathrm{rad}}
= 12\cdot\frac{1}{n}\sum_{i=1}^n\left(t_{(i)}-q_i\right)^2,
\qquad
q_i = \frac{i-\tfrac12}{n}.
$$

Default moment penalty (`w2` path):

$$
W_2^2(\mathcal N(\mu,\Sigma),\mathcal N(0,I))
= \|\mu\|^2 + \sum_k(\sqrt{\lambda_k}-1)^2.
$$

Calibration/aggregation:

$$
\widehat{L}_c = \frac{L_c-m_c}{s_c},
\qquad
L_{\mathrm{total}}
= \frac{\widehat{L}_{\mathrm{rep}} +
\lambda_{\mathrm{rad}}\widehat{L}_{\mathrm{rad}} +
\lambda_{\mathrm{ang}}\widehat{L}_{\mathrm{ang}} +
\lambda_{\mathrm{mom}}\widehat{L}_{\mathrm{mom}}}{s_{\mathrm{total}}}.
$$

Python anchors:
- Radial term in `ml-tidbits/python/embed_models/EmbedModels.py:759`
- `w2` formula path in `ml-tidbits/python/embed_models/EmbedModels.py:483`
- Calibration sampling in `ml-tidbits/python/embed_models/EmbedModels.py:642`
- Final weighted normalized sum in `ml-tidbits/python/embed_models/EmbedModels.py:833`

## 3. Lean Declaration Mapping

### 3.1 Geometry and types

Lean (`Foundations.lean`):

```lean
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)
abbrev Sphere (d : ℕ) : Type := Metric.sphere (0 : Vec d) (1 : ℝ)
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1
abbrev Wristband (d : ℕ) : Type := Sphere d × UnitInterval
def VecNZ (d : ℕ) : Type := {z : Vec d // z ≠ 0}
```

Math target:

$$
\mathcal{W}_d = S^{d-1}\times[0,1],
\qquad
\Phi:\mathbb{R}^d\setminus\{0\}\to\mathcal{W}_d.
$$

Verdict: Match.

### 3.2 Radius and direction

Lean (`Foundations.lean`):

```lean
def radiusSq {d : ℕ} (z : VecNZ d) : NNReal := ⟨‖z.1‖ ^ 2, by positivity⟩
noncomputable def direction {d : ℕ} (z : VecNZ d) : Sphere d := ...
```

Math target:

$$
S(z)=\|z\|^2,
\qquad
U(z)=\frac{z}{\|z\|}.
$$

Verdict: Match.

### 3.3 Chi-square radius law and CDF (Resolved — previously axioms, now definitions)

**Previous state**: `chiSqRadiusLaw`, `chiSqCDFToUnit`, and `chiSqCDFToUnit_measurable` were axioms in `ImportedFacts.lean`.

**Current state**: All three are now concrete definitions/lemmas in `Foundations.lean`, backed by Mathlib's `gammaMeasure`:

```lean
-- Chi-square as Gamma(d/2, 1/2):
noncomputable def chiSqMeasureR (d : ℕ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (chiSqShape d) chiSqRate

-- Pushed forward to ℝ≥0 and wrapped as ProbabilityMeasure:
noncomputable def chiSqRadiusLaw (d : ℕ) : Distribution NNReal := ...

-- CDF map using Mathlib's ProbabilityTheory.cdf:
noncomputable def chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval := ...

-- Measurability proven from CDF continuity:
lemma chiSqCDFToUnit_measurable (d : ℕ) : Measurable (chiSqCDFToUnit d) := ...
```

Math target:

$$
\chi^2_d = \operatorname{Gamma}(d/2,\, 1/2),
\qquad
F_{\chi^2_d}(x) = \operatorname{gammainc}(d/2,\, x/2).
$$

Python correspondence: `torch.special.gammainc(d/2, s/2)` in `EmbedModels.py:752`.

Verdict: **Match.** Previously partial; now fully resolved.

### 3.4 CDF contracts for PIT (Resolved — previously missing, now proven)

**Previous state**: No declaration linking `chiSqCDFToUnit` to `chiSqRadiusLaw` through the CDF predicates. The audit flagged this as the primary missing piece.

**Current state**: Both CDF contracts are now proven theorems in `Foundations.lean`:

```lean
-- Continuity contract (needed for forward PIT):
theorem chiSqCDFToUnit_isContinuousCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...

-- Strict monotonicity contract (needed for reverse PIT):
theorem chiSqCDFToUnit_isStrictlyIncreasingCDF (d : ℕ) (hDim : 1 ≤ d) :
    IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d) := ...
```

These are backed by proven supporting lemmas:
- `continuous_cdf_gammaMeasure` — CDF continuity via no-atoms property of gamma measures.
- `strictMono_cdf_gammaMeasure` — strict monotonicity via positive density on all intervals.
- `gammaMeasure_Ioc_pos` — positive mass on `(x, y]` for `0 ≤ x < y`.

Verdict: **Match.** Previously missing; now fully resolved with Mathlib-backed proofs.

### 3.5 Gaussian polar decomposition (axioms in `ImportedFacts.lean`)

Lean (`ImportedFacts.lean`):

```lean
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)
axiom gaussianPolar_direction_uniform (d : ℕ) : ...
axiom gaussianPolar_radius_chiSq (d : ℕ) : ...
axiom gaussianPolar_independent (d : ℕ) : ...
axiom sphereUniform_rotationInvariant (d : ℕ) (O : ...) : ...
```

Math target:

$$
Z\sim\gamma_d
\Rightarrow
U=\frac{Z}{\|Z\|}\sim\sigma_{d-1},
\quad
S=\|Z\|^2\sim\chi_d^2,
\quad
U\perp S.
$$

Verdict: Partial (these remain axioms — theorem debt).

### 3.6 PIT theorem headers

Lean (`Foundations.lean`):

```lean
theorem probabilityIntegralTransform ... :
  pushforward F μ hFMeas = uniform01 := by sorry

theorem probabilityIntegralTransform_reverse ... :
  observedLaw = targetLaw := by sorry
```

Math target:

$$
X\sim\mu,\ F=F_\mu\ \text{continuous}
\Rightarrow
F(X)\sim \mathrm{Unif}(0,1),
$$

$$
U\sim \mathrm{Unif}(0,1),\ F\ \text{strictly increasing CDF}
\Rightarrow
F^{-1}(U)\sim\mu.
$$

Verdict: Partial — headers match, proofs deferred (`sorry`). But the CDF hypotheses can now be instantiated via the proven contracts in section 3.4.

### 3.7 Equivalence headers

Lean (`Equivalence.lean`):

```lean
theorem wristbandEquivalence_forward (d : ℕ) :
  wristbandLaw d (gaussianNZ d) = wristbandUniform d := by sorry

theorem wristbandEquivalence_backward (d : ℕ) (Q : Distribution (VecNZ d))
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by sorry

theorem wristbandEquivalence (d : ℕ) (Q : Distribution (VecNZ d)) :
    wristbandLaw d Q = wristbandUniform d ↔ Q = gaussianNZ d := ...
```

Math target:

$$
\Phi_\# Q = \mu_0
\iff
Q = \gamma_d
\quad
(\text{modelled on }\mathbb{R}^d\setminus\{0\}).
$$

Verdict: Partial — headers match, forward/backward proofs deferred.

## 4. Active Mismatches and Status

### 4.1 CDF contract for `chiSqCDFToUnit` (Resolved)

**Previous status**: Missing. No declaration that `chiSqCDFToUnit` is the CDF of `chiSqRadiusLaw`.

**Current status**: Fully resolved. Both `IsContinuousCDFFor` and `IsStrictlyIncreasingCDFFor` contracts are proven theorems in `Foundations.lean`, backed by Mathlib's `gammaMeasure` infrastructure. Additionally, `chiSqRadiusLaw` and `chiSqCDFToUnit` are no longer axioms — they are concrete definitions.

### 4.2 `Distribution := Measure` design gap (Resolved)

Current status:
- `Distribution` is now a type alias to `ProbabilityMeasure`, so probability is type-driven.
- Core theorem boundaries no longer carry redundant `[IsProbabilityMeasure ...]` assumptions.
- `pushforward` and `productLaw` are built from probability-measure constructors.

Remaining mismatch:
- None for this item.

### 4.3 Missing explicit dimension assumptions

Current status:
- Core headers use unrestricted `d : ℕ`.
- The chi-square CDF contracts correctly require `hDim : 1 ≤ d`.

Mismatch:
- The intended geometry in the proof plan is for nondegenerate spherical setting (at least `2 <= d`).
- The equivalence theorem headers do not yet carry dimension constraints.

Minimal Lean fix:
- Add `hDim : 2 <= d` to geometric and equivalence theorem headers where the argument semantically needs nondegenerate sphere behavior.

### 4.4 Missing ambient-Gaussian bridge for `gaussianNZ`

Current status:
- `gaussianNZ` is a direct axiom on nonzero vectors.

Mismatch:
- No explicit bridge from an ambient Gaussian on `Vec d` restricted away from zero.

Minimal Lean fix:
- Add an imported bridge statement expressing that restricting ambient Gaussian to `VecNZ` yields `gaussianNZ`.

### 4.5 Remaining axiom: `sphereUniform_isProbability`

Current status:
- `Foundations.lean` contains one axiom: `sphereUniform_isProbability`, asserting that the normalized sphere surface measure has total mass 1.

Assessment:
- This requires showing that the sphere has finite nonzero surface area, which is nontrivial in Mathlib currently.
- Acceptable to keep as axiom for now.

## 5. Axiom Inventory

Complete list of axioms across all files:

| Axiom | File | Status |
|-------|------|--------|
| `sphereUniform_isProbability` | `Foundations.lean` | Axiom (sphere has finite nonzero area) |
| `gaussianNZ` | `ImportedFacts.lean` | Axiom (standard Gaussian on nonzero vectors) |
| `gaussianPolar_direction_uniform` | `ImportedFacts.lean` | Axiom (direction is uniform on sphere) |
| `gaussianPolar_radius_chiSq` | `ImportedFacts.lean` | Axiom (squared radius is chi-square) |
| `gaussianPolar_independent` | `ImportedFacts.lean` | Axiom (direction ⊥ squared radius) |
| `sphereUniform_rotationInvariant` | `ImportedFacts.lean` | Axiom (sphere law is rotation-invariant) |

**No longer axioms** (now concrete definitions/lemmas in `Foundations.lean`):
- `chiSqRadiusLaw` → definition via `gammaMeasure`
- `chiSqCDFToUnit` → definition via `ProbabilityTheory.cdf`
- `chiSqCDFToUnit_measurable` → proven lemma

## 6. Implementation Queue

1. ~~Add chi-square CDF bridge axioms for `chiSqRadiusLaw` and `chiSqCDFToUnit`.~~ **Done** — replaced axioms with Mathlib-backed definitions and proven CDF contracts.
2. Add explicit `2 <= d` assumptions where geometric equivalence statements rely on nondegenerate sphere geometry.
3. Add optional ambient-Gaussian bridge for `gaussianNZ`.
4. ~~Migrate base law type from `Measure` alias to `ProbabilityMeasure`.~~ **Done.**
5. Prove PIT theorems (`probabilityIntegralTransform` and `probabilityIntegralTransform_reverse`) — currently `sorry`.
6. Prove equivalence theorems (`wristbandEquivalence_forward`, `wristbandEquivalence_backward`) — currently `sorry`.

## 7. Current Bottom Line

Header-level formalization captures the wristband map, Gaussian polar structure, and equivalence theorem shape with type-driven probability laws (`Distribution := ProbabilityMeasure`). The chi-square CDF bridge — previously the primary gap — is now fully resolved with Mathlib-backed definitions and proven continuity/strict-monotonicity contracts. Remaining alignment work is in two places: explicit dimension assumptions for equivalence theorems, and an optional ambient-Gaussian bridge for `gaussianNZ`. The main deferred proofs are the PIT theorems and the equivalence forward/backward directions.
