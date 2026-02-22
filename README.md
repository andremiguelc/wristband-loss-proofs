# Wristband Loss — Lean 4 Proofs

Machine-checked proofs for the mathematical foundations of the
[Wristband Gaussian Loss](https://github.com/mvparakhin/ml-tidbits)
(`C_WristbandGaussianLoss` in `EmbedModels.py`).

## The Central Theorem

For any distribution $Q$ on $\mathbb{R}^d \setminus \{0\}$ with $d \ge 2$:

$$\Phi_\# Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \quad\iff\quad Q = \mathcal{N}(0, I_d)$$

where $\Phi(z) = \bigl(z/\|z\|,\; F_{\chi^2_d}(\|z\|^2)\bigr)$ is the wristband map.

**In plain terms:** the wristband map produces uniform output *if and only if*
the input is standard Gaussian. No distribution can fake Gaussianity through
the wristband lens.

## Proof Status

| Step | What it proves | Status |
|------|---------------|--------|
| 1. Wristband equivalence | Uniform wristband output $\iff$ Gaussian input | **Complete** (sorry-free) |
| 2. Kernel energy minimization | Repulsion kernel uniquely minimized at uniform | **Complete** for Neumann kernel |
| 3. Main correctness | Repulsion loss uniquely identifies the Gaussian | Planned (combines Steps 1+2) |
| 4. Auxiliary terms | Radial, moment, angular penalties preserve the minimizer | Planned |

See [docs/proof_guide.md](docs/proof_guide.md) for the full Python-to-Lean
correspondence, axiom inventory, and remaining work.

## Build

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get
lake build
```

## Lean Files

| File | Contents |
|------|----------|
| `EquivalenceFoundations.lean` | Types, chi-square CDF, probability integral transform |
| `EquivalenceImportedFacts.lean` | Gaussian polar decomposition axioms |
| `Equivalence.lean` | Wristband map and equivalence theorem |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic predicates |
| `KernelImportedFacts.lean` | Kernel theory axioms (PSD, universality, constant potential) |
| `KernelFoundations.lean` | Kernel properties, symmetry, characteristic and constant-potential proofs |
| `KernelMinimization.lean` | Energy minimization and uniqueness; Neumann-to-3-image bridge |

## Further Reading

- [Proof guide](docs/proof_guide.md) — Python-to-Lean mapping, theorem status, axiom list
- [Wristband loss explained](docs/posts/wristband_loss.md) — What the loss does and why, by [Mikhail Parakhin](https://x.com/MParakhin)
- [Conditional sampling](docs/posts/conditional_sampling.md) — Dependent-factor extension (MNIST inpainting), by [Mikhail Parakhin](https://x.com/MParakhin)
