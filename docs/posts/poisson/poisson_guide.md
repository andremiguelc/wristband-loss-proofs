# Wristband loss — Poisson mode sampling guide

Companion to [`docs/proof_guide.md`](../../proof_guide.md) for the
`WristbandLossProofs/Poisson/` branch. It gives four things: the construction, its connection
to the kernel proofs, the location of each piece, and the list of imported facts.

**Related documents:**
- Full mathematical development, with figures: [poisson_mode_sampling.md](poisson_mode_sampling.md)
- The branch whose cost problem this addresses: [spectral_guide.md](../spectral/spectral_guide.md)

---

## 1. What the branch says

The angular kernel is a Poisson mixture over powers of `⟪u, u'⟫`. You can *sample* a mixture
in place of an expansion into a basis. A sampler with the correct expectation does not
approximate the wristband kernel. At every pair of points, it **is** the wristband kernel.

So the minimization and uniqueness theorems transfer by a rewrite. The dimension of the sphere
never enters. The method enumerates no degree block, so the `d^ℓ` cost never appears.

## 2. How it fits the rest of the proof

```
KernelPrimitives ─ PoissonPrimitives ─ PoissonImportedFacts ─ PoissonFoundations
                                                                     │
KernelMinimization ──────────────────────────────────────── PoissonMinimization
                                                                     │
                                                             PoissonEstimator
                                                                     │
                                                             PoissonVariance
                                                                     │
                                                            PoissonSecondMoment
```

This is a strict chain. `PoissonFoundations` needs only `KernelPrimitives`. The dependence on
the kernel minimization theorems starts at `PoissonMinimization`. Nothing in the branch uses
`Spectral/`, and no kernel or spectral module uses `Poisson/`.

`PoissonPrimitives` through `PoissonMinimization` say the sampler targets the right minimum.
`PoissonEstimator` moves that statement onto the kernel a run actually draws.
`PoissonVariance` says how many features `D` it takes to *see* that minimum, and
`PoissonSecondMoment` says what a given distance from the minimum costs in rank.

## 3. Lean file map

| File | Contents |
|---|---|
| `PoissonPrimitives.lean` | `poissonWeight`, `dotProductKernel`, `RademacherDraw`, `randomMaclaurinFeature`, `AngularSampler`, `sampledKernel`, `IsUnbiasedFor`, `sampledWristbandKernel` |
| `PoissonImportedFacts.lean` | The axioms of §5, and `randomMaclaurinLaw` / `randomMaclaurinSampler` extracted from the first of them |
| `PoissonFoundations.lean` | Exponential series, Poisson weight facts, the Maclaurin expansion, the sampler and its unbiasedness |
| `PoissonMinimization.lean` | `sampledEnergy_eq_kernelEnergy`, minimization, uniqueness, Gaussian characterization, and `poissonSampledEnergy_minimizer_unique` |
| `PoissonEstimator.lean` | `realizedWristbandKernel` and its `drawLaw`, `HasIntegrableDrawEnergy`, unbiasedness of the realized energy, the minimization theorems restated on it, and the sum-of-squares feature form |
| `PoissonVariance.lean` | `drawEnergy`, the `1/D` variance identity, Chebyshev, and the feature-count bounds |
| `PoissonSecondMoment.lean` | Energy is linear in the kernel; the splitting bound; the angular instance `a·(E_P[t²] − 1/d) ≤ MMD²`; and `realizedEnergy_separates` |

## 4. Math × Lean correspondence

Section numbers refer to [poisson_mode_sampling.md](poisson_mode_sampling.md).

| Math | Lean |
|---|---|
| §1, the power series `∑ p_m t^m` | `dotProductKernel` |
| §1, `k_ang = E_{m~Poisson(c)}[t^m]` | `kernelAngChordal_maclaurinExpansion` |
| §1, `Σ p_m = 1` | `poissonWeight_tsum_eq_one` |
| §3, drawing the severity `m` | `RademacherDraw` (its first component) |
| §3, the product of `m` projections | `randomMaclaurinFeature` |
| §3, the law those are drawn from | `randomMaclaurin_law_exists` |
| §3, the boxed unbiasedness identity | `poissonAngularSampler_unbiased` |
| §3, sampling targets the right energy | `sampledEnergy_eq_kernelEnergy` |
| §3, uniqueness survives sampling | `sampledEnergy_minimizer_unique` |
| §3, a sum over pairs becomes a sum over features | `kernelEnergy_featureForm` |
| §4, a *fixed* draw is finite-rank | `realizedWristbandKernel` is that kernel; its rank is not stated |
| §4, `D = (e^c − 1)/ε²` | `featureCount_suffices`, given a variance bound as hypothesis |
| the estimate the code computes, averaged over draws | `realizedEnergy_unbiased` |
| the licence for the exchange of integrals | `HasIntegrableDrawEnergy`, sufficient by `hasIntegrableDrawEnergy_of_sq` |

## 5. Imported facts

There are two axioms, both in `PoissonImportedFacts.lean`. **Both attributions come from
recollection. Nobody checked either one against the source.** The axiom docstrings state the
open questions. This section gives the citations.

**`randomMaclaurin_law_exists`** — a law on `RademacherDraw d` exists for any non-negative
summable `p`. Under that law, the expected product of two `randomMaclaurinFeature`s equals the
dot-product kernel with coefficients `p`.

Attributed to **Kar & Karnick (2012)**, *Random Feature Maps for Dot Product Kernels*,
AISTATS, PMLR 22:583–591. The construction and its unbiasedness are theirs; assembling the
measure on the sigma-type is not, and neither is any variance control.

> Open: the result number, and whether the source states it on the sphere or on a
> bounded-norm domain. Pham & Pagh (2013) and Hamid et al. (2014) are adjacent candidates.

**`dotProductKernel_energy_minimized_at_uniform`** — the uniform measure minimizes the energy
of any dot-product kernel whose Maclaurin coefficients are non-negative.

Attributed to **Schoenberg (1942)**, *Positive definite functions on spheres*, Duke Math. J.
9:96–108, for the positive definiteness, and **Björck (1956)**, *Distributions of positive
mass, which maximize a certain generalized energy integral*, Ark. Mat. 3:255–269, for the
energy minimum. `PoissonSecondMoment` needs this axiom. It splits `k_ang` at the quadratic
term, and the axiom shows that `μ₀` still minimizes the energy of the remainder.

> Open: the result numbers. Also, does Björck cover a general kernel with non-negative
> coefficients, or only the Riesz family? And does the source give the minimum for `S^{d-1}` at
> every `d ≥ 1`?

## 6. What is derived, not imported

The Maclaurin expansion. `kernelAngChordal_maclaurinExpansion` is the exponential series.
`Real.exp_eq_exp_ℝ` and `NormedSpace.exp_eq_tsum_div` give it in fewer than 15 lines, so it
does not need an axiom. The same computation gives `poissonWeight_tsum_eq_one`, which states
that the coefficients are a probability distribution.

## 7. Axiom status

`#print axioms` gives this table, for every public declaration of the branch. **No `sorryAx`
occurs anywhere.** No path here reaches the open kernel `sorry`s. The table omits Lean's own
`propext`, `Classical.choice` and `Quot.sound`.

Three groups of project axioms occur. The table uses these abbreviations:

- **PSD**, 5 axioms: `kernelAngChordal_posSemiDef`, `productKernel_posSemiDef_imported`,
  `mmdSq_nonneg`, `gaussian_periodization_cosine_series_period_two`,
  `orthogonal_group_transitive_on_sphere`.
- **UNIV**, 6 axioms: `kernelAngChordal_universal`, `kernelRadNeumann_universal`,
  `productKernel_universal_compact_imported`, `universal_implies_characteristic`,
  `gaussian_periodization_cosine_series_period_two`,
  `orthogonal_group_transitive_on_sphere`.
- **EQUIV**, 3 axioms: `gaussianFull_witness`, `spherical_polar_decomposition`,
  `gaussianFull_normSq_chiSq`.

| Theorem | Project axioms used |
|---|---|
| `poissonWeight_tsum_eq_one` | none |
| `kernelAngChordal_maclaurinExpansion` | none |
| `poissonAngularSampler_unbiased` | `randomMaclaurin_law_exists` |
| `sampledEnergy_eq_kernelEnergy` | none |
| `sampledEnergy_minimized_at_uniform` | PSD |
| `sampledEnergy_minimizer_unique` | UNIV |
| `sampledEnergy_wristband_gaussian_iff` | UNIV + EQUIV |
| `poissonSampledEnergy_minimizer_unique` | UNIV + `randomMaclaurin_law_exists` |
| `kernelEnergy_eq_integral_prod` | none |
| `realizedEnergy_eq_average` | none |
| `drawEnergy_average_eq_kernelEnergy` | none |
| `realizedEnergy_unbiased` | none |
| `poissonRealizedEnergy_unbiased` | `randomMaclaurin_law_exists` |
| `realizedEnergy_minimized_at_uniform` | PSD |
| `realizedEnergy_minimizer_unique` | UNIV |
| `hasIntegrableDrawEnergy_of_sq` | none |
| `kernelEnergy_featureForm` | none |
| `realizedAngularEnergy_featureForm` | none |
| `realizedEnergy_ae_eq_mean` | none |
| `realizedEnergy_variance` | none |
| `realizedEnergy_memLp_two` | none |
| `realizedEnergy_chebyshev` | none |
| `featureCount_suffices` | none |
| `featureCount_suffices_relative` | none |
| `energyGap_ge_of_remainder` | none |
| `angularRemainder_energy_minimized_at_uniform` | `dotProductKernel_energy_minimized_at_uniform` |
| `angularGap_ge_secondMomentGap` | none |
| `angularGap_ge_secondMomentGap_of_uniform` | `dotProductKernel_energy_minimized_at_uniform` |
| `realizedEnergy_separates` | none |

The shape of that table matters. Minimization needs only PSD; uniqueness is what pulls in
UNIV. `PoissonVariance` is axiom-free throughout, so the whole feature-count argument rests
on nothing imported. Inside `PoissonSecondMoment`, only the step that needs the uniform
measure to minimize the remainder touches the new axiom. `realizedEnergy_separates` joins the
two halves and stays axiom-free, because it takes the true gap as a hypothesis rather than
deriving it.

To check the table again, run `lake env lean` on a scratch file of `#print axioms` lines.

`lake build` alone does **not** reach this branch. The root module imports only `Equivalence`,
and the `lean_lib` declares no globs, so you must build each module by name. Use
`lake build WristbandLossProofs.Poisson.PoissonSecondMoment`. The import chain then pulls in
all seven files.

## 8. What is not formalized

- **The variance itself.** §4 of the math note gives the real constraint on the method. The
  relative variance for one draw is `e^c − 1` at the target. Away from the target, the tails
  are heavy. `featureCount_suffices` takes a variance bound as a **hypothesis**, then converts
  it into a feature count. No theorem here proves that bound. So `D = (e^c − 1)/ε²` is
  analytic, not machine-checked.
- **The cost of the truncation.** §2 of the math note shows that `ℓ ≤ 1` is exactly blind.
  That statement is about the kernel of the spectral branch, not this one. It exists only in
  prose.
- **Resampling.** The draw must change at each step. The module header of
  `PoissonMinimization` states this. No theorem states it.
- **The cost claim.** `O(N(Sd + Dc))` is not formalized. There is no model of the operation
  count here.
- **The hypotheses of `hasIntegrableDrawEnergy_of_sq`.** Three things stay hypotheses: the
  second moment of the feature, the bound on `kernelRadNeumann`, and joint measurability of
  `feat`. The second moment is finite for this sampler, and the radial bound is a
  theta-function estimate, but no theorem proves either one. `AngularSampler` carries no
  measurability, so the third hypothesis cannot be discharged as it stands.
- **The logarithm.** The unbiasedness results are about the energy. The code descends
  `(1/β) log Ê`. Jensen's inequality makes that estimate low by `−(e^c − 1)/(2D) = −ε²/2`.
  Nothing here bounds it.
- **Concentration.** The estimator is close to binomial at the target, and heavy-tailed away
  from it. So a bound for a neighbourhood of `μ₀` is tractable, and a uniform bound is not.
  This branch attempts neither.

## 9. References

- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels." *AISTATS* 2012,
  *PMLR* 22, 583–591.
- Schoenberg, I. J. (1942). "Positive definite functions on spheres." *Duke Math. J.* 9,
  96–108.
- Björck, G. (1956). "Distributions of positive mass, which maximize a certain generalized
  energy integral." *Ark. Mat.* 3, 255–269.
