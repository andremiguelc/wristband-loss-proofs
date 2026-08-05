# Wristband Loss — Poisson Mode Sampling Guide

Companion to `docs/proof_guide.md` for the `WristbandLossProofs/Poisson/` branch. It covers
three questions:

1. **What** the construction is and what it replaces.
2. **How** it connects to the existing kernel and spectral proofs.
3. **Where** each piece lives, and which are imported rather than proved.

**Related documents:**
- Full mathematical development, with figures: [poisson_mode_sampling.md](poisson_mode_sampling.md)
- The branch it repairs: `docs/posts/spectral/spectral_guide.md`

---

## 1. What the branch says

Two theorems, pulling in opposite directions.

**The negative one.** A finite-rank kernel on the wristband is *blind*: some distribution other
than the uniform target sits at the same energy, with the same (zero) gradient. Since the
spectral fast path truncates the angular expansion at degree `L`, its kernel has rank
`∑_{ℓ≤L} N_ℓ < ∞`, so this applies to it. The defect is structural — no batch size, number of
steps, or tightening of an error bound removes it, because there is no inequality involved: the
two energies are *equal*.

**The positive one.** The angular kernel is a Poisson mixture over powers of `⟪u, u'⟫`, and a
mixture is something you can sample rather than truncate. A sampler that is unbiased in
expectation does not approximate the wristband kernel — it *is* the wristband kernel, pointwise.
So `KernelMinimization` transfers verbatim and uniqueness of the minimizer survives.

The contrast is the point: truncation changes the kernel, sampling does not.

## 2. How it fits the rest of the proof

```
Equivalence ─────────────────────────── wristbandEquivalence
     ↑
KernelPrimitives ── PoissonPrimitives ── PoissonImportedFacts ── PoissonFoundations
     ↓                                                                  ↓
KernelFoundations ── KernelMinimization ─────────────────────── PoissonMinimization
```

`PoissonFoundations` needs only `KernelPrimitives`; the dependence on the kernel minimization
theorems enters at the last file, where the payoff is claimed. Nothing in the branch depends on
`Spectral/`.

## 3. Lean file map

| File | Contents |
|---|---|
| `PoissonPrimitives.lean` | `HasFiniteRank`, `IsBlindAt`, `AgreeOnFeatures`, `poissonWeight`, `dotProductKernel`, `RademacherDraw`, `randomMaclaurinFeature`, `AngularSampler`, `sampledKernel`, `IsUnbiasedFor`, `sampledWristbandKernel` |
| `PoissonImportedFacts.lean` | 2 axioms + 2 witness-extraction defs |
| `PoissonFoundations.lean` | Exponential series, Poisson weights, the Maclaurin expansion, finite-rank energy, blindness |
| `PoissonMinimization.lean` | 5 theorems: transfer, minimization, uniqueness, Gaussian characterization, and the Poisson instance |

## 4. Math × Lean correspondence

| Math (`poisson_mode_sampling.md`) | Lean |
|---|---|
| §1 Step 8, `k_ang = E_{m~Poisson(c)}[t^m]` | `kernelAngChordal_maclaurinExpansion` |
| §1 Step 8, `Σ p_m = 1` | `poissonWeight_tsum_eq_one` |
| §2, `E_{≤1}(P) = A₀ + A₁‖μ‖²` | `kernelEnergy_eq_sum_sq_of_rankWitness` (general rank `r`) |
| §2, zero-mean arrangements are global minima | `isBlindAt_of_rankWitness`, `isBlindAt_of_hasFiniteRank` |
| §3 Moves 2–3, the Rademacher feature | `randomMaclaurinFeature`, `randomMaclaurin_law_exists` |
| §3, the boxed unbiasedness identity | `poissonAngularSampler_unbiased` |
| §3, sampling targets the right energy | `sampledEnergy_eq_kernelEnergy` |
| §4, uniqueness survives | `sampledEnergy_minimizer_unique` |
| §5 L2, a *fixed* draw is finite-rank | not a theorem; `isBlindAt_of_hasFiniteRank` applies to it, noted in the `PoissonMinimization` header |

The generalisation is deliberate: §2 works out the `ℓ ≤ 1` case by hand, where the energy reduces
to the length of the average arrow. Lean proves the statement for any rank-`r` kernel, of which
`ℓ ≤ 1` is the case `r = 1 + d`.

## 5. Imported facts

Two axioms. Both are stated in `PoissonImportedFacts.lean` with their fragilities.

### `randomMaclaurin_law_exists`

There is a law on `RademacherDraw d` under which the expected product of two
`randomMaclaurinFeature`s is the dot-product kernel with coefficients `p`, for any non-negative
summable `p`.

Attributed to **Kar & Karnick (2012)**, *Random Feature Maps for Dot Product Kernels*, AISTATS,
PMLR 22:583–591. The construction and its unbiasedness are theirs; assembling the measure on the
sigma-type is not, and neither is any variance control.

### `finiteRank_hasNontrivialFibre`

For any `r` features on the wristband there is a distribution other than uniform agreeing with it
on all of them, with integrability inherited.

Attributed to **Sriperumbudur, Fukumizu & Lanckriet (2011)**, *Universality, Characteristic
Kernels and RKHS Embedding of Measures*, JMLR 12:2389–2410. Stated there as "characteristic
implies infinite-dimensional RKHS"; the form here is the contrapositive specialised to one target
measure.

> **Both attributions are unverified.** They were written from recollection and have not been
> checked against the sources. For the first, the open questions are the result number and whether
> the source states it on the sphere or on a bounded-norm domain; Pham & Pagh (2013) and Hamid et
> al. (2014) are adjacent candidates. The second is the weaker of the two and may instead belong
> to Sriperumbudur et al. (2010), JMLR 11:1517–1561, or to Steinwart & Christmann (2008).

## 6. What is derived, not imported

Everything else, including the two things one might expect to be axioms:

- **The Maclaurin expansion.** `kernelAngChordal_maclaurinExpansion` is the exponential series,
  assembled from `Real.exp_eq_exp_ℝ` and `NormedSpace.exp_eq_tsum_div`. Under 15 lines.
- **The energy of a finite-rank kernel.** `kernelEnergy_eq_sum_sq_of_rankWitness` pushes a
  `Finset.sum` through a double integral, given integrability of each feature. This is the
  load-bearing lemma: blindness follows from it in four lines.

## 7. Axiom status

Verified with `#print axioms`. **No `sorryAx` anywhere in the branch** — the four open kernel
sorry's are not on any path used here.

| Theorem | Project axioms used |
|---|---|
| `poissonWeight_tsum_eq_one` | none |
| `kernelAngChordal_maclaurinExpansion` | none |
| `kernelEnergy_eq_sum_sq_of_rankWitness` | none |
| `isBlindAt_of_rankWitness` | none |
| `sampledEnergy_eq_kernelEnergy` | none |
| `isBlindAt_of_hasFiniteRank` | `finiteRank_hasNontrivialFibre` |
| `poissonAngularSampler_unbiased` | `randomMaclaurin_law_exists` |
| `sampledEnergy_minimizer_unique` | the 5 kernel-universality axioms |
| `poissonSampledEnergy_minimizer_unique` | the above + `randomMaclaurin_law_exists` |

To re-check: `lake env lean` on a scratch file of `#print axioms` lines. Note that `lake build`
alone does **not** reach this branch — the root module imports only `Equivalence` and the
`lean_lib` declares no globs, so modules must be built by name.

## 8. What is not formalized

- **The variance bound.** §5 of the math note is the real constraint on the method — variance
  grows exponentially in `c`, and the tails are heavy. None of it is in Lean, and the theorems
  above are silent about it.
- **The `ℓ ≤ 1` energy identity in closed form.** Lean has the general rank-`r` statement; the
  concrete `A₀ + A₁‖μ‖²` form, and the numbers in §2's figure, are numerical only.
- **Resampling.** The design constraint that the draw must be refreshed each step is stated in
  prose in the `PoissonMinimization` module header, not as a theorem.
- **The cost claim.** `O(N(Sd + Dc))` is not formalized; there is no complexity model here.

## 9. References

- Kar, P.; Karnick, H. (2012). "Random Feature Maps for Dot Product Kernels." *AISTATS* 2012,
  *PMLR* 22, 583–591.
- Sriperumbudur, B.; Fukumizu, K.; Lanckriet, G. (2011). "Universality, Characteristic Kernels
  and RKHS Embedding of Measures." *JMLR* 12, 2389–2410.
