# Wristband Loss — Lean 4 Proofs

Machine-checked proofs for the mathematical foundations of the
**Wristband Gaussian Loss**, designed by [@mvparakhin](https://github.com/mvparakhin)
and implemented in [`ml-tidbits`](https://github.com/mvparakhin/ml-tidbits)
(`C_WristbandGaussianLoss` in `EmbedModels.py`).

This repository formalizes the correctness of @mvparakhin's algorithm in Lean 4,
and extends it with a spectral kernel characterization.

## The Central Theorem

For any distribution $Q$ on $\mathbb{R}^d \setminus \{0\}$ with $d \ge 2$:

$$\Phi_{\\#} Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \quad\iff\quad Q = \mathcal{N}(0, I_d)$$

where $\Phi(z) = \bigl(z/\|z\|,\; F_{\chi^2_d}(\|z\|^2)\bigr)$ is the wristband map.

The wristband map produces uniform output *if and only if* the input is standard Gaussian.

## Proof Status

| Branch | What it proves | Status |
|--------|---------------|--------|
| **Equivalence** | Uniform wristband output $\iff$ Gaussian input | **Complete** (sorry-free) |
| **Kernel minimization** | Neumann wristband kernel energy uniquely minimized at $\mu_0$ | **Complete** modulo 4 sorry's |
| **Spectral** | $\text{spectralEnergy} = \text{kernelEnergy}$ + minimization + Gaussian iff | **Complete** (sorry-free in spectral files; transitively blocked by kernel sorry's) |
| Steps 3–4 | Full correctness of the Python loss | Not started |

### Open sorry's (4, all in kernel branch)

| Sorry | File | Kind |
|-------|------|------|
| `measurable_wristbandKernelNeumann` | `KernelFoundations` | Routine measurability |
| `integral_tsum_kernelRadNeumann` | `KernelFoundations` | Fubini for tsum |
| `cosine_span_uniformly_dense_on_unitInterval` | `KernelFoundations` | Cosine density (Stone-Weierstrass) |
| `threeImage_energy_approx` | `KernelMinimization` | 3-image / Neumann bridge bound |

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
| `EquivalenceImportedFacts.lean` | Gaussian polar decomposition axioms (5) |
| `Equivalence.lean` | Wristband map and equivalence theorem |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic predicates |
| `KernelImportedFacts.lean` | Kernel theory axioms (11): PSD, universality, constant potential |
| `KernelFoundations.lean` | Kernel properties, Neumann radial expansion, cosine orthogonality |
| `KernelMinimization.lean` | Energy minimization, uniqueness, 3-image bridge |
| `Spectral/SpectralPrimitives.lean` | `radialFeature`, `radialCoeff`, `modeProj`, `spectralEnergy` |
| `Spectral/SpectralImportedFacts.lean` | Mercer decomposition axiom for angular kernel |
| `Spectral/SpectralFoundations.lean` | Witness extraction, mode projections, spectral–kernel identity |
| `Spectral/SpectralMinimization.lean` | Spectral minimization, uniqueness, Gaussian characterization |

## Further Reading

- [Proof guide](docs/proof_guide.md) — theorem map, axiom inventory, Python-to-Lean correspondence
- [Spectral kernel derivation](docs/posts/spectral/spectral_harmonics.md) — spherical harmonics, Gegenbauer, Bessel eigenvalues
- [Spectral narrative](docs/posts/spectral/spectral_narrative.md) — from wristband loss to spectral kernel
- [Wristband loss explained](docs/posts/og_wristband/wristband_loss.md) — by [Mikhail Parakhin](https://x.com/MParakhin)
- [Conditional sampling](docs/posts/og_wristband/conditional_sampling.md) — dependent-factor extension, by [Mikhail Parakhin](https://x.com/MParakhin)
