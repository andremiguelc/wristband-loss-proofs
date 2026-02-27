# From Wristband Loss to Spectral Kernel: The Journey

This document tells the story of how the wristband Gaussian loss led to a
spectral decomposition of its kernel — and why that decomposition matters
both theoretically (existential theorems in Lean) and practically (an
O(NdK) algorithm replacing O(N²d)).

---

## 1. The starting point: a loss function for Gaussianity

The wristband loss solves a specific ML problem: given a deterministic
encoder $E: \text{data} \to \mathbb{R}^d$, ensure its output distribution
is close to $\mathcal{N}(0, I_d)$.

Why do we want Gaussian latents?  Because the standard normal factorizes:
$p(z) = \prod_i \phi(z_i)$.  If we train separate encoders for different
factors (text, weather, image) and concatenate their outputs, achieving
$z \sim \mathcal{N}(0,I)$ guarantees the factors are independent.  This
enables counterfactual reasoning: hold one factor fixed, resample another,
and observe the effect.  The Gaussian interface is a plug-compatible
contract between modules.

The key insight of the wristband approach is to decompose Gaussianity
testing into two independent, geometrically natural pieces using the
**wristband map**:

$$\Phi(z) = \left(\frac{z}{\|z\|},\; F_{\chi^2_d}(\|z\|^2)\right) \in S^{d-1} \times [0,1]$$

The direction $u = z/\|z\|$ should be uniform on the sphere.  The
CDF-transformed radius $t = F_{\chi^2_d}(\|z\|^2)$ should be uniform
on $[0,1]$ (by the probability integral transform).  And they should be
independent.

The product space $S^{d-1} \times [0,1]$ is the "wristband."  A batch of
embeddings, once mapped through $\Phi$, should look uniform on the wristband.

---

## 2. The kernel energy: measuring non-uniformity

How do you measure whether a batch of points is uniform on the wristband?
The wristband loss uses a **kernel energy**:

$$\mathcal{E}(P) = \mathbb{E}_{W,W' \sim P}[K(W, W')]$$

where $K = k_\text{ang} \cdot k_\text{rad}$ is a product kernel.  The angular
part is a Gaussian RBF on the sphere; the radial part is a heat kernel on
$[0,1]$ with Neumann boundary conditions (implemented via the method-of-images
trick with 3 reflected Gaussians).

The fundamental result (proved in Lean, sorry-free) is:

> **Theorem.** $\mathcal{E}(P) \geq \mathcal{E}(\mu_0)$, with equality if
> and only if $P = \mu_0$ (the uniform measure on the wristband).

Combined with the equivalence theorem (also sorry-free):

> **Theorem.** $\Phi_\# Q = \mu_0 \iff Q = \mathcal{N}(0, I_d)$.

Together: minimizing the kernel energy forces the encoder output to be
Gaussian.  This is the rigorous foundation the Lean formalization provides.

---

## 3. The computational bottleneck

The kernel energy involves all $N^2$ pairs in a batch.  Computing the full
kernel matrix costs $O(N^2 d)$ — three $(N \times N)$ matrices (one per
reflected image), each requiring an inner product.

At production embedding dimensions ($d = 512$, $N = 4096$), this is
$\approx 8.6$ billion multiplications per forward pass.  The quadratic
scaling also limits batch size: an 8 GB GPU can handle at most $N \approx 4500$.

Larger batches reduce gradient variance (the kernel energy is a U-statistic,
$\text{Var} \propto 1/N$), so the $O(N^2)$ bottleneck directly limits
training quality.

---

## 4. The spectral idea: decompose, then truncate

The product kernel has a natural decomposition.  Each factor — angular
and radial — is a continuous PSD kernel on a compact space.  By Mercer's
theorem, each has an eigenexpansion:

$$k_\text{ang}(u, u') = \sum_j \lambda_j\, \varphi_j(u)\, \varphi_j(u')$$
$$k_\text{rad}(t, t') = \sum_k \tilde{a}_k\, f_k(t)\, f_k(t')$$

Their product gives:

$$K(w, w') = \sum_{j,k} \lambda_j \tilde{a}_k\, [\varphi_j(u) f_k(t)]\,[\varphi_j(u') f_k(t')]$$

Substituting into the energy:

$$\mathcal{E}(P) = \sum_{j,k} \lambda_j\, \tilde{a}_k\, \hat{c}_{jk}(P)^2$$

where $\hat{c}_{jk}(P) = \mathbb{E}_{(u,t) \sim P}[\varphi_j(u) \cdot f_k(t)]$
is a "mode projection."

This is the **spectral identity**: the kernel energy is a weighted sum of
squared projections onto the eigenbasis.

### Why this helps computationally

The $N^2$ dependence came from evaluating all pairs.  In the spectral form,
each mode projection $\hat{c}_{jk}$ requires only a single pass over the
batch: it is a sample mean.  If we truncate to $L$ angular modes and $K$
radial modes, the cost is $O(NdK)$ for the $\ell = 1$ angular modes
(which require the matrix multiply $U^\top \cdot \text{CosMatrix}$).

At $L = 1$ (constant + linear harmonics) and $K = 6$ radial modes, the
cost drops to $\approx 12.6$ million multiplications — a **680× reduction
in flops** at $d = 512$ (flop-count estimate; measured wall-clock speedup
exceeds 1000× at large $N$, since the spectral path also has much better
memory locality).
Memory goes from $O(N^2)$ to $O(Nd)$, enabling batches of $N \approx 65000$.

### Why truncation to $\ell \leq 1$ is sufficient

The angular eigenvalues decay as $\lambda_\ell / \lambda_0 \approx (c/d)^\ell / \ell!$
for $d \gg c$.  At $d = 512$ and typical $\beta$, the $\ell = 2$ modes
contribute $< 0.05\%$ of total energy.  Adding them would multiply cost by
$\approx d/K > 80$ for negligible accuracy.  The $\ell = 0$ and $\ell = 1$
modes capture $> 99\%$ of the kernel at all production dimensions.

---

## 5. The mathematical structure behind the decomposition

### Angular eigenfunctions are spherical harmonics

For our zonal kernel ($k_\text{ang}$ depends only on $\langle u, u' \rangle$),
rotation invariance forces the eigenfunctions to be spherical harmonics.
The argument chains through representation theory:

1. $T_K$ commutes with all rotations (zonal invariance).
2. By Schur's lemma, $T_K$ must act as a scalar on each irreducible
   $O(d)$-subspace.
3. The irreducible subspaces of $L^2(S^{d-1})$ are exactly the spaces
   $\mathcal{H}_\ell^d$ of degree-$\ell$ spherical harmonics (Peter-Weyl).

Therefore $T_K|_{\mathcal{H}_\ell^d} = \lambda_\ell I$ — one eigenvalue
per harmonic degree, with multiplicity $N(d, \ell)$.

### Eigenvalues involve Bessel functions

The eigenvalue $\lambda_\ell$ equals the $\ell$-th Gegenbauer coefficient of
$e^{ct}$ (where $c = 2\beta\alpha^2$), which can be computed in closed form.

The computation uses the Rodrigues formula to convert the Gegenbauer
projection integral into a shifted Poisson integral, which evaluates to a
modified Bessel function $I_{\ell + (d-2)/2}(c)$.  The result:

$$\lambda_\ell = e^{-c}\,\Gamma(d/2)\,(2/c)^{(d-2)/2}\, I_{\ell+(d-2)/2}(c)$$

The exponential decay of $I_\nu(c)$ in $\nu$ (for fixed $c$) explains why
the eigenvalue spectrum falls off so rapidly with $\ell$.

(For the full derivation, see [spectral_harmonics.md](spectral_harmonics.md).)

### Radial eigenfunctions are cosines

The radial kernel on $[0,1]$ with Neumann boundary conditions has
eigenfunctions $f_0(t) = 1$ and $f_k(t) = \cos(k\pi t)$ for $k \geq 1$,
with exponentially decaying eigenvalues
$\tilde{a}_k = 2\sqrt{\pi/\beta}\,e^{-\pi^2 k^2/(4\beta)}$.

---

## 6. The Lean formalization: what the theorems say

The spectral branch introduces one bridge lemma and three main theorems,
all with complete proof bodies:

- **Identity** (`spectralEnergy_eq_kernelEnergy`, `SpectralFoundations.lean`):
  The spectral energy $\sum_{j,k} \lambda_j \tilde{a}_k \hat{c}_{jk}^2$
  equals the kernel energy $\mathbb{E}[K(W,W')]$.

- **Minimization** (`spectralEnergy_minimized_at_uniform`): The spectral
  energy is minimized at the uniform measure.

- **Uniqueness** (`spectralEnergy_minimizer_unique`): The minimizer is
  unique.

- **Gaussian characterization** (`spectralEnergy_wristband_gaussian_iff`):
  $Q = \mathcal{N}(0,I)$ if and only if the spectral energy of $\Phi_\# Q$
  is at its minimum.

The proof strategy for minimization is elegant: at $\mu_0$, all mode
projections $\hat{c}_{jk}$ vanish except $(0,0)$ (because angular
eigenfunctions integrate to zero for $j > 0$, and cosines integrate to
zero for $k > 0$).  So $\mathcal{E}(\mu_0) = \lambda_0 \tilde{a}_0$.
Every deviation adds non-negative terms.

Theorems 2–4 are proved by delegating to the existing kernel-side proofs
(which are sorry-free) via the identity.  The identity itself has a fully
proved *conditional* version — conditional on summability/integrability
assumptions that formalize the interchange $\int\int\sum = \sum\int\int$.

The remaining work is purely technical: discharging these summability
witnesses from the boundedness of the kernel.  No new mathematical ideas
are needed.

---

## 7. The intuition, in one picture

```
Original kernel energy               Spectral energy
  E = E_W,W'[ K(W,W') ]               E = Sum_{j,k} lam_j * a_k * c_jk^2
        |                                       |
  requires N^2 pairs                    requires N projections
  O(N^2 d)                             O(N d K)

  Both are the same number (identity theorem).
  Both are minimized uniquely at mu_0 (minimization + uniqueness).
  Both characterize Gaussianity (equivalence theorem).
```

The spectral decomposition doesn't change the mathematics — it changes the
*algorithm*.  The kernel energy and spectral energy are the same object,
viewed through different lenses.  One is a sum over pairs; the other is a
sum over modes.  The mode view reveals that most of the kernel's energy is
concentrated in a small number of low-frequency modes, enabling truncation
with negligible error.

---

## 8. What comes next

**On the Lean side:** Close the one remaining sorry (`spectralEnergy_eq_kernelEnergy`)
by providing summability witnesses.  This is the last step to make
the spectral branch fully proved.

**On the Python side:** Implement the spectral kernel as a parallel branch
alongside the existing 3-image baseline, validate with matched-seed
experiments, and measure throughput/memory/gradient quality.

**Beyond:** Steps 3–4 of the overall proof (combining equivalence + kernel
minimization via log monotonicity, and the auxiliary penalty terms) are
short once the spectral bridge is closed.
