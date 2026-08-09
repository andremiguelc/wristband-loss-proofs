# Wristband Loss — Poisson Mode Sampling Guide

Companion to `docs/proof_guide.md` for the `WristbandLossProofs/Poisson/` branch. It covers
three questions:

1. **What** the construction is.
2. **How** it connects to the existing kernel proofs.
3. **Where** each piece lives, and which are imported rather than proved.

**Related documents:**
- Full mathematical development, with figures: [poisson_mode_sampling.md](poisson_mode_sampling.md)
- The branch whose cost problem this addresses: `docs/posts/spectral/spectral_guide.md`

---

## 1. What the branch says

The angular kernel is a Poisson mixture over powers of `⟪u, u'⟫`, and a mixture is something you
can *sample* rather than expand into a basis. A sampler that is unbiased in expectation does not
approximate the wristband kernel — it **is** the wristband kernel, pointwise. So the existing
minimization and uniqueness theorems transfer by rewriting, and the sphere's dimension never
enters: no degree block is enumerated, so the `d^ℓ` cost never appears.

## 2. How it fits the rest of the proof

```
KernelPrimitives ─ PoissonPrimitives ─ PoissonImportedFacts ─ PoissonFoundations
                                                                     │
KernelMinimization ──────────────────────────────────────── PoissonMinimization
                                                                     │
                                                             PoissonEstimator
```

A strict chain. `PoissonFoundations` needs only `KernelPrimitives`; the dependence on the kernel
minimization theorems enters at the last two files, where the payoff is claimed. Nothing in the
branch depends on `Spectral/`, and nothing in `Kernel/` or `Spectral/` depends on `Poisson/`.

## 3. Lean file map

| File | Contents |
|---|---|
| `PoissonPrimitives.lean` | `poissonWeight`, `dotProductKernel`, `RademacherDraw`, `randomMaclaurinFeature`, `AngularSampler`, `sampledKernel`, `IsUnbiasedFor`, `sampledWristbandKernel` |
| `PoissonImportedFacts.lean` | 1 axiom + 2 witness-extraction defs |
| `PoissonFoundations.lean` | Exponential series, Poisson weight facts, the Maclaurin expansion, the sampler and its unbiasedness |
| `PoissonMinimization.lean` | 5 theorems: transfer, minimization, uniqueness, Gaussian characterization, and the Poisson instance |
| `PoissonEstimator.lean` | `realizedWristbandKernel` and its `drawLaw`, `HasIntegrableDrawEnergy`, unbiasedness of the realized energy, the minimization theorems restated on it, and the sum-of-squares feature form |

## 4. Math × Lean correspondence

| Math (`poisson_mode_sampling.md`) | Lean |
|---|---|
| §1 Step 7, the power series `∑ p_m t^m` | `dotProductKernel` |
| §1 Step 8, `k_ang = E_{m~Poisson(c)}[t^m]` | `kernelAngChordal_maclaurinExpansion` |
| §1 Step 8, `Σ p_m = 1` | `poissonWeight_tsum_eq_one` |
| §3 Move 1, drawing the severity | `RademacherDraw` (its first component) |
| §3 Moves 2–3, the product of projections | `randomMaclaurinFeature` |
| §3, the law those are drawn from | `randomMaclaurin_law_exists` |
| §3, the boxed unbiasedness identity | `poissonAngularSampler_unbiased` |
| §3, sampling targets the right energy | `sampledEnergy_eq_kernelEnergy` |
| §4, uniqueness survives | `sampledEnergy_minimizer_unique` |
| §5 L2, a *fixed* draw is finite-rank | `realizedWristbandKernel` is that kernel; its rank is not stated |
| the estimate the code computes, averaged over draws | `realizedEnergy_unbiased` |
| the licence for the exchange of integrals | `HasIntegrableDrawEnergy`, sufficient by `hasIntegrableDrawEnergy_of_sq` |
| a sum over pairs becomes a sum over features | `kernelEnergy_featureForm` |

## 5. Imported facts

One axiom, `randomMaclaurin_law_exists`: there is a law on `RademacherDraw d` under which the
expected product of two `randomMaclaurinFeature`s is the dot-product kernel with coefficients
`p`, for any non-negative summable `p`.

Attributed to **Kar & Karnick (2012)**, *Random Feature Maps for Dot Product Kernels*, AISTATS,
PMLR 22:583–591. The construction and its unbiasedness are theirs; assembling the measure on the
sigma-type is not, and neither is any variance control.

> The attribution is written from recollection and not yet checked against the source. Open
> questions: the result number, and whether the source states it on the sphere or on a
> bounded-norm domain. Pham & Pagh (2013) and Hamid et al. (2014) are adjacent candidates.

## 6. What is derived, not imported

The Maclaurin expansion. `kernelAngChordal_maclaurinExpansion` is the exponential series,
assembled from `Real.exp_eq_exp_ℝ` and `NormedSpace.exp_eq_tsum_div` — under 15 lines, so it did
not warrant an axiom. `poissonWeight_tsum_eq_one`, the statement that the coefficients really are
a probability distribution, comes out of the same computation.

## 7. Axiom status

Verified with `#print axioms`. **No `sorryAx` anywhere in the branch** — the four open kernel
sorry's are not on any path used here.

| Theorem | Project axioms used |
|---|---|
| `poissonWeight_tsum_eq_one` | none |
| `kernelAngChordal_maclaurinExpansion` | none |
| `sampledEnergy_eq_kernelEnergy` | none |
| `poissonAngularSampler_unbiased` | `randomMaclaurin_law_exists` |
| `sampledEnergy_minimizer_unique` | the 5 kernel-universality axioms |
| `poissonSampledEnergy_minimizer_unique` | the above + `randomMaclaurin_law_exists` |
| `realizedEnergy_unbiased` | none |
| `kernelEnergy_featureForm` | none |
| `hasIntegrableDrawEnergy_of_sq` | none |
| `poissonRealizedEnergy_unbiased` | `randomMaclaurin_law_exists` |
| `realizedEnergy_minimizer_unique` | the 5 kernel-universality axioms |

To re-check: `lake env lean` on a scratch file of `#print axioms` lines. Note that `lake build`
alone does **not** reach this branch — the root module imports only `Equivalence` and the
`lean_lib` declares no globs, so modules must be built by name.

## 8. What is not formalized

- **The variance bound.** §5 of the math note is the real constraint on the method — variance
  grows exponentially in `c`, and the tails are heavy. None of it is in Lean, and the theorems
  above are silent about it.
- **What the truncation costs.** §2 of the math note argues that `ℓ ≤ 1` is exactly blind. That
  is a statement about the spectral branch's kernel, not this one, and it lives only in prose.
- **Resampling.** The design constraint that the draw must be refreshed each step is stated in
  the `PoissonMinimization` module header, not as a theorem.
- **The cost claim.** `O(N(Sd + Dc))` is not formalized; there is no complexity model here.
- **The three hypotheses of `hasIntegrableDrawEnergy_of_sq`.** The feature's second moment, the bound
  on `kernelRadNeumann`, and joint measurability of `feat` are all hypotheses. The second moment is
  finite for this sampler and the radial bound is a theta-function estimate, but neither is proved;
  `AngularSampler` carries no measurability at all, so the third cannot be discharged as stated.
- **Concentration, and the logarithm.** Unbiasedness is about the energy. The code descends
  `(1/β) log Ê`, and Jensen makes that estimate biased low by a gap that averaging does not remove.
  Nothing here bounds it.

## 9. References

- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels." *AISTATS* 2012,
  *PMLR* 22, 583–591.
