# Wristband Loss — Lean 4 Proofs

*Lean 4 formalization of the wristband-uniformity ⇔ Gaussian-input theorem, plus a kernel/spectral characterization of the loss minimum.*

Target algorithm: **Wristband Gaussian Loss** at [mvparakhin/ml-tidbits](https://github.com/mvparakhin/ml-tidbits).

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
| **Poisson mode sampling** | The angular kernel is a Poisson mixture; an unbiased sampler preserves the minimizer | **Complete** (sorry-free, and no `sorryAx` on any path) |

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

Note that `WristbandLossProofs.lean` imports only `Equivalence` and the `lean_lib` declares no
globs, so `lake build` does **not** reach the kernel, spectral, or Poisson branches. Build those
by module name, e.g. `lake build WristbandLossProofs.Poisson.PoissonMinimization`.

## Lean Files

| File | Contents |
|------|----------|
| `EquivalencePrimitives.lean` | Types (`Vec`, `VecNZ`, `Distribution`), sphere uniform measure, $\chi^2$ CDF, probability integral transform |
| `EquivalenceImportedFacts.lean` | 3 axioms transcribing Muirhead (1982) Thm 1.2.9, 1.5.6, 1.4.1(a) |
| `EquivalenceFoundations.lean` | Derivations: `gaussianNZ`, polar direction uniform, polar independence, polar radius $\chi^2$ |
| `Equivalence.lean` | Wristband map $\Phi$ and the central theorem |
| `KernelPrimitives.lean` | Kernel definitions, energy, MMD, PSD/characteristic predicates |
| `KernelImportedFacts.lean` | 9 axioms: PSD, universality, characteristic, transitivity, constant potential |
| `KernelFoundations.lean` | Kernel properties, Neumann radial expansion, cosine orthogonality |
| `KernelMinimization.lean` | Energy minimization, uniqueness, 3-image bridge |
| `Spectral/SpectralPrimitives.lean` | `radialFeature`, `radialCoeff`, `modeProj`, `spectralEnergy` |
| `Spectral/SpectralImportedFacts.lean` | 5 axioms: Mercer expansion, addition theorem, degree mass, per-degree bound |
| `Spectral/SpectralFoundations.lean` | Witness extraction, mode projections, spectral–kernel identity |
| `Spectral/SpectralMinimization.lean` | Spectral minimization, uniqueness, Gaussian characterization |
| `Spectral/SpectralTruncation.lean` | Closed-form truncation error bounds in the angular degree and radial mode count |
| `Poisson/PoissonPrimitives.lean` | `poissonWeight`, `dotProductKernel`, `RademacherDraw`, `randomMaclaurinFeature`, `AngularSampler` |
| `Poisson/PoissonImportedFacts.lean` | 1 axiom: the random-feature law |
| `Poisson/PoissonFoundations.lean` | Maclaurin expansion of the angular kernel, the sampler and its unbiasedness |
| `Poisson/PoissonMinimization.lean` | Sampled energy transfer, minimization, uniqueness, Gaussian characterization |

## Further Reading

- [Proof guide](docs/proof_guide.md) — theorem map, axiom inventory, Python-to-Lean correspondence
- [Spectral kernel derivation](docs/posts/spectral/spectral_harmonics.md) — spherical harmonics, Gegenbauer, Bessel eigenvalues
- [Spectral narrative](docs/posts/spectral/spectral_narrative.md) — from wristband loss to spectral kernel
- [Poisson mode sampling](docs/posts/poisson/poisson_mode_sampling.md) — why angular truncation is blind, and the sampler that is not
- [Poisson guide](docs/posts/poisson/poisson_guide.md) — Lean companion: file map, axioms, correspondence
- [Wristband loss explained](docs/posts/og_wristband/wristband_loss.md) 
- [Conditional sampling](docs/posts/og_wristband/conditional_sampling.md) 
