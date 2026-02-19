# Wristband Formalization Audit (Lean vs. `ml-tidbits`)

Date: 2026-02-19

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
&= e^{-\beta(t_i-t_j)^2}
+ e^{-\beta(t_i+t_j)^2}
+ e^{-\beta(t_i+t_j-2)^2}.
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
= \frac{\widehat{L}_{\mathrm{rep}}
+ \lambda_{\mathrm{rad}}\widehat{L}_{\mathrm{rad}}
+ \lambda_{\mathrm{ang}}\widehat{L}_{\mathrm{ang}}
+ \lambda_{\mathrm{mom}}\widehat{L}_{\mathrm{mom}}}{s_{\mathrm{total}}}.
$$

Python anchors:
- Radial term in `ml-tidbits/python/embed_models/EmbedModels.py:759`
- `w2` formula path in `ml-tidbits/python/embed_models/EmbedModels.py:483`
- Calibration sampling in `ml-tidbits/python/embed_models/EmbedModels.py:642`
- Final weighted normalized sum in `ml-tidbits/python/embed_models/EmbedModels.py:833`

## 3. Lean Declaration Mapping

### 3.1 Geometry and types

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
\mathcal{W}_d = S^{d-1}\times[0,1],
\qquad
\Phi:\mathbb{R}^d\setminus\{0\}\to\mathcal{W}_d.
$$

Verdict: Match.

### 3.2 Radius and direction

Lean:

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

### 3.3 Imported Gaussian-polar package

Lean:

```lean
axiom gaussianNZ (d : ℕ) : Distribution (VecNZ d)
axiom gaussianNZ_isProbability (d : ℕ) :
  IsProbabilityMeasure (gaussianNZ d)
axiom chiSqRadiusLaw (d : ℕ) : Distribution NNReal
axiom chiSqRadiusLaw_isProbability (d : ℕ) :
  IsProbabilityMeasure (chiSqRadiusLaw d)
axiom chiSqCDFToUnit (d : ℕ) : NNReal → UnitInterval
axiom gaussianPolar_direction_uniform (d : ℕ) : ...
axiom gaussianPolar_radius_chiSq (d : ℕ) : ...
axiom gaussianPolar_independent (d : ℕ) : ...
axiom sphereUniform_isProbability (d : ℕ) :
  IsProbabilityMeasure (sphereUniform d)
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

Verdict: Partial.

Missing piece: no declaration that `chiSqCDFToUnit` is the CDF of `chiSqRadiusLaw`.

### 3.4 PIT declarations

Lean:

```lean
def IsContinuousCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop := ...
def IsStrictlyIncreasingCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop := ...

theorem probabilityIntegralTransform ... :
  pushforward F μ = uniform01 := by sorry

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

Verdict: Partial.

Missing piece: no instantiated bridge connecting `chiSqRadiusLaw` and `chiSqCDFToUnit` through these predicates.

### 3.5 Equivalence headers

Lean:

```lean
theorem sphericalLaw_determinedByRadius
    (d : ℕ)
    {Ω : Type _}
    [MeasurableSpace Ω]
    (μ : Distribution Ω)
    [IsProbabilityMeasure μ]
    (S : Ω → NNReal)
    (U : Ω → Sphere d)
    (hU : pushforward U μ = sphereUniform d)
    (hIndep : IndepLaw μ S U) :
    pushforward (fun ω => (Real.sqrt (S ω : ℝ)) • (U ω).1) μ =
      sphericalLaw d (pushforward S μ) := by
  sorry

theorem wristbandEquivalence_forward (d : ℕ) :
  wristbandLaw d (gaussianNZ d) = wristbandUniform d := by sorry

theorem wristbandEquivalence_backward
    (d : ℕ) (Q : Distribution (VecNZ d))
    [IsProbabilityMeasure Q]
    (hUniform : wristbandLaw d Q = wristbandUniform d) :
    Q = gaussianNZ d := by sorry

theorem wristbandEquivalence
    (d : ℕ) (Q : Distribution (VecNZ d))
    [IsProbabilityMeasure Q] :
    wristbandLaw d Q = wristbandUniform d ↔ Q = gaussianNZ d := by
  sorry
```

Math target:

$$
\Phi_\# Q = \mu_0
\iff
Q = \gamma_d
\quad
(\text{modelled on }\mathbb{R}^d\setminus\{0\}).
$$

Verdict: Partial.

Open conditions: CDF bridge for PIT specialization and explicit dimension assumptions.

## 4. Active Mismatches (Unresolved)

### 4.1 Missing CDF contract for `chiSqCDFToUnit`

Missing declarations:
- `IsContinuousCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d)`
- `IsStrictlyIncreasingCDFFor (chiSqRadiusLaw d) (chiSqCDFToUnit d)`

Why Python requires this:
- Python uses
  $$
  t = \operatorname{gammainc}\!\left(\frac d2,\frac s2\right)
  $$
  as the chi-square CDF value in `ml-tidbits/python/embed_models/EmbedModels.py:752`.
- Radial loss compares sorted `t` to uniform quantiles in `ml-tidbits/python/embed_models/EmbedModels.py:757`.

Minimal Lean fix:
- Add imported axioms linking `chiSqCDFToUnit` to `chiSqRadiusLaw` through `IsContinuousCDFFor` and `IsStrictlyIncreasingCDFFor`.

### 4.2 `Distribution := Measure` design gap

Current status:
- Key statements now require probability assumptions via `[IsProbabilityMeasure ...]`.
- Imported Gaussian/sphere/chi-square laws now have probability instances.

Remaining mismatch:
- `Distribution` is still a `Measure` alias, so probability is assumption-driven, not type-driven.

Minimal Lean fix:
- Keep current approach and continue adding `[IsProbabilityMeasure ...]` on new theorem boundaries.

Optional stronger fix:
- Migrate to `ProbabilityMeasure` as the base law type.

### 4.3 Missing explicit dimension assumptions

Current status:
- Core headers use unrestricted `d : ℕ`.

Mismatch:
- The intended geometry in the proof plan is for nondegenerate spherical setting (at least `2 <= d`).

Minimal Lean fix:
- Add `hDim : 2 <= d` to geometric and equivalence theorem headers where the argument semantically needs nondegenerate sphere behavior.

### 4.4 Missing ambient-Gaussian bridge for `gaussianNZ`

Current status:
- `gaussianNZ` is a direct axiom on nonzero vectors.

Mismatch:
- No explicit bridge from an ambient Gaussian on `Vec d` restricted away from zero.

Minimal Lean fix:
- Add an imported bridge statement expressing that restricting ambient Gaussian to `VecNZ` yields `gaussianNZ`.

## 5. Implementation Queue

1. Add chi-square CDF bridge axioms for `chiSqRadiusLaw` and `chiSqCDFToUnit`.
2. Add explicit `2 <= d` assumptions where geometric equivalence statements rely on nondegenerate sphere geometry.
3. Add optional ambient-Gaussian bridge for `gaussianNZ`.
4. Keep `[IsProbabilityMeasure ...]` discipline for all new theorem boundaries.

## 6. Current Bottom Line

Header-level formalization now captures the wristband map, Gaussian polar structure, and equivalence theorem shape with explicit probability assumptions on core statements. Remaining alignment work is concentrated in three places: chi-square CDF linkage for PIT specialization, explicit dimension assumptions, and an optional ambient-Gaussian bridge for `gaussianNZ`.
