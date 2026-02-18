# wristband-loss-proofs

Lean 4 + Mathlib formal proofs for results developed in [ml-tidbits](https://github.com/mvparakhin/ml-tidbits).

## Structure

```
.
├── WristbandLossProofs/
│   ├── Foundations.lean      # Types, distributions, sphere measure, CDF defs, imported theorem debt
│   └── CoreEngine.lean       # Wristband map, spherical law, wristband equivalence theorem
├── WristbandLossProofs.lean  # Library root (imports CoreEngine)
├── docs/
│   ├── wristband_proof_plan.md          # Formal proof framework (definitions → kernels → objectives)
│   └── wristband_tutorial_core_engine.md # Step-by-step tutorial on the probabilistic engine
├── lakefile.toml             # Lake build config
├── lean-toolchain            # Lean version pin
├── lake-manifest.json        # Dependency lock file
└── ml-tidbits/               # Reference implementation (local only, not tracked)
```

## Proof status

| Result | File | Status |
|--------|------|--------|
| `sphericalLaw_determinedByRadius` | CoreEngine | proved |
| `wristbandEquivalence` | CoreEngine | proved (via forward + backward) |
| `sphericalLaw_rotationInvariant` | CoreEngine | sorry |
| `wristbandEquivalence_forward` | CoreEngine | sorry |
| `wristbandEquivalence_backward` | CoreEngine | sorry |
| `probabilityIntegralTransform` | Foundations | sorry |
| `probabilityIntegralTransform_reverse` | Foundations | sorry |
| Gaussian polar facts | Foundations | axiom (imported) |
| `sphereUniform_rotationInvariant` | Foundations | axiom (imported) |

## Setup

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake exe cache get   # download Mathlib cache (first time)
lake build
```

## ml-tidbits reference

The `ml-tidbits/` folder contains a local clone of the Python repository whose
results we are formalising. It is listed in `.gitignore` and is not part of
this repo. Re-clone if missing:

```bash
git clone https://github.com/mvparakhin/ml-tidbits --depth=1
```
