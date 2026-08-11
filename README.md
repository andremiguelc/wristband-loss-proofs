# Wristband Loss — Lean 4 Proofs

*Lean 4 formalization of the wristband-uniformity ⇔ Gaussian-input theorem, plus a kernel/spectral characterization of the loss minimum.*

Target algorithm: **Wristband Gaussian Loss** at [mvparakhin/ml-tidbits](https://github.com/mvparakhin/ml-tidbits).

## The Central Theorem

For any distribution $Q$ on $\mathbb{R}^d \setminus \{0\}$ with $d \ge 2$:

$$\Phi_{\\#} Q \;=\; \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \quad\iff\quad Q = \mathcal{N}(0, I_d)$$

where $\Phi(z) = \bigl(z/\|z\|,\; F_{\chi^2_d}(\|z\|^2)\bigr)$ is the wristband map.

The wristband map produces uniform output *if and only if* the input is standard Gaussian.

## Branches

| Branch | What it proves |
|--------|---------------|
| **Equivalence** | Uniform wristband output $\iff$ Gaussian input |
| **Kernel minimization** | Neumann wristband kernel energy uniquely minimized at $\mu_0$ |
| **Spectral** | $\text{spectralEnergy} = \text{kernelEnergy}$, minimization, and the Gaussian iff |
| **Poisson mode sampling** | The angular kernel is a Poisson mixture; an unbiased sampler preserves the minimizer |

Per-branch proof status, the open `sorry`s, and the axiom inventory live in the
[proof guide](docs/proof_guide.md).

## Build

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get
lake build
```

Note that `WristbandLossProofs.lean` imports only `Equivalence` and the `lean_lib` declares no
globs, so `lake build` does **not** reach the kernel, spectral, or Poisson branches. Build those
by module name:

```bash
lake build WristbandLossProofs.KernelMinimization
lake build WristbandLossProofs.Poisson.PoissonSecondMoment   # pulls in all seven Poisson files
lake build WristbandLossProofs.Spectral.SpectralTruncation
```

The third currently fails: `Spectral/SpectralFoundations.lean` needs repair against the
pinned Mathlib. See the [proof guide](docs/proof_guide.md) §1.

## Lean Files

Each branch is layered the same way: `*Primitives` holds definitions, `*ImportedFacts`
holds the axioms taken from the literature, and the remaining modules derive from them.

```
WristbandLossProofs/
  EquivalencePrimitives · EquivalenceImportedFacts · EquivalenceFoundations · Equivalence
  KernelPrimitives      · KernelImportedFacts      · KernelFoundations      · KernelMinimization
  Spectral/  SpectralPrimitives · SpectralImportedFacts · SpectralFoundations
             SpectralMinimization · SpectralTruncation
  Poisson/   PoissonPrimitives · PoissonImportedFacts · PoissonFoundations
             PoissonMinimization · PoissonEstimator · PoissonVariance · PoissonSecondMoment
```

The [proof guide](docs/proof_guide.md) gives the contents and the axiom count of each
module.

## Further Reading

- [Proof guide](docs/proof_guide.md) — theorem map, axiom inventory, Python-to-Lean correspondence
- [Spectral kernel derivation](docs/posts/spectral/spectral_harmonics.md) — spherical harmonics, Gegenbauer, Bessel eigenvalues
- [Spectral narrative](docs/posts/spectral/spectral_narrative.md) — from wristband loss to spectral kernel
- [Spectral guide](docs/posts/spectral/spectral_guide.md) — Lean companion for the spectral branch
- [Poisson mode sampling](docs/posts/poisson/poisson_mode_sampling.md) — why angular truncation is blind, and the sampler that is not
- [Poisson guide](docs/posts/poisson/poisson_guide.md) — Lean companion for the Poisson branch
- [Wristband loss explained](docs/posts/og_wristband/wristband_loss.md) — what the loss does and why
- [Conditional sampling](docs/posts/og_wristband/conditional_sampling.md) — sampling from a trained encoder
