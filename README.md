# wristband-loss-proofs

Machine-checked Lean 4 proofs for the mathematical foundations of the
[Wristband Gaussian Loss](https://github.com/mvparakhin/ml-tidbits)
(`C_WristbandGaussianLoss` in `EmbedModels.py`).

## What is proven

The **Wristband Equivalence Theorem**: for any distribution Q on
nonzero vectors in R^d (d >= 2), the wristband-transformed law equals the
uniform product measure on S^{d-1} x [0,1] **if and only if** Q is the
standard Gaussian.

In other words, the wristband map is a *lossless characterization* of
Gaussianity — no distribution can "fake" being Gaussian through the wristband
lens.

The formalization is **sorry-free** (zero deferred proofs). All results
type-check against Mathlib. The only axioms are classical facts about the
Gaussian (polar decomposition, rotation invariance of sphere measure) that are
not yet in Mathlib, isolated in a single file.

### Proven results

| Result | File | Line |
|--------|------|------|
| Forward: Gaussian implies uniform wristband | `Equivalence.lean` | 515 |
| Backward: uniform wristband implies Gaussian | `Equivalence.lean` | 695 |
| Biconditional (iff) | `Equivalence.lean` | 999 |
| Probability integral transform (forward) | `EquivalenceFoundations.lean` | 535 |
| Probability integral transform (reverse) | `EquivalenceFoundations.lean` | 660 |
| Chi-square CDF continuity and strict monotonicity | `EquivalenceFoundations.lean` | 482, 495 |
| Spherical law determined by radius | `Equivalence.lean` | 154 |

## Proof status

This covers Step 1 (wristband equivalence) of a 4-step correctness argument
for the full loss function. See [docs/wristband_proof_plan.md](docs/wristband_proof_plan.md)
for the complete roadmap.

| Step | Status |
|------|--------|
| 1. Wristband equivalence | **Complete** |
| 2. Kernel energy identifies uniformity | Not started |
| 3. Main correctness theorem | Not started |
| 4. Extra terms preserve minimizer | Not started |

## Documentation

- [docs/wristband_proof_plan.md](docs/wristband_proof_plan.md) — Proof roadmap
  covering all four steps, written for readers without Lean background.
- [docs/wristband_formalization_audit.md](docs/wristband_formalization_audit.md) —
  Line-by-line mapping between `EmbedModels.py` and the Lean definitions.

## Build

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get
lake build
```

## Layout

| File | Contents |
|------|----------|
| `WristbandLossProofs/EquivalenceFoundations.lean` | Core types (Vec, Sphere, Wristband), distributions, chi-square CDF, probability integral transform |
| `WristbandLossProofs/EquivalenceImportedFacts.lean` | Classical axioms (Gaussian polar decomposition, sphere measure properties) |
| `WristbandLossProofs/Equivalence.lean` | Wristband map, spherical-law lemmas, equivalence theorem |
| `WristbandLossProofs/KernelFoundations.lean` | Kernel definitions, energy, MMD, PSD/characteristic/constant-potential predicates |
| `WristbandLossProofs/KernelImportedFacts.lean` | Imported kernel theory axioms (PSD, characteristic, constant potential) |
| `WristbandLossProofs/KernelMinimization.lean` | Step-2 theorem statements (energy minimized at uniform) |
| `WristbandLossProofs.lean` | Library root |

`ml-tidbits/` is an optional local reference clone and is not part of this
repository.
