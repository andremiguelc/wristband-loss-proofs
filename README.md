# wristband-loss-proofs

Lean 4 + Mathlib formal proofs for results developed in [ml-tidbits](https://github.com/mvparakhin/ml-tidbits).

## Structure

```
.
├── WristbandLossProofs/      # Lean source files
│   └── Basic.lean
├── WristbandLossProofs.lean  # Library root (imports)
├── lakefile.toml             # Lake build config
├── lean-toolchain            # Lean version pin
├── lake-manifest.json        # Dependency lock file
├── ml-tidbits/               # Reference impl (local only, not tracked)
└── docs/                     # Notes, references, materials
```

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
