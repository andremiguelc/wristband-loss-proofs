# wristband-loss-proofs

Lean 4 + Mathlib formalization of the wristband-Gaussian arguments used in
[`ml-tidbits`](https://github.com/mvparakhin/ml-tidbits).

## Build

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get
lake build
```

## Layout

- `WristbandLossProofs/Foundations.lean`: core types, measures/distributions, chi-square CDF/PIT infrastructure.
- `WristbandLossProofs/ImportedFacts.lean`: imported theorem debt isolated as axioms.
- `WristbandLossProofs/Equivalence.lean`: wristband map, spherical-law lemmas, and equivalence theorem statements.
- `WristbandLossProofs.lean`: library root.
- `docs/wristband_proof_plan.md`: proof roadmap.
- `docs/wristband_formalization_audit.md`: Python-to-Lean mapping audit.

`ml-tidbits/` is an optional local reference clone and is not part of this repository.
