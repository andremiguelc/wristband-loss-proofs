# Wristband Gaussian Loss — Proof Plan

This document is the **roadmap** for the full correctness proof of the
Wristband Gaussian Loss (`C_WristbandGaussianLoss` in `EmbedModels.py`).

**The central claim:**

> In the idealized (population) setting, the wristband loss has a **unique
> minimizer**: the standard Gaussian distribution.

The proof has four steps. Step 1 is complete; Steps 2–4 remain.

For the detailed Python-to-Lean mapping of completed work, see
[wristband_formalization_audit.md](wristband_formalization_audit.md).

---

## Proof structure at a glance

| Step | What it says | Status |
|------|-------------|--------|
| 1. Wristband equivalence | Uniform wristband output iff Gaussian input | **Complete** |
| 2. Kernel energy identifies uniformity | The repulsion kernel is uniquely minimized at uniform | Not started |
| 3. Main correctness theorem | Repulsion loss uniquely identifies the Gaussian | Not started (immediate from 1+2) |
| 4. Extra terms preserve minimizer | Radial, moment, angular penalties and calibration don't change the minimizer | Not started (straightforward) |

The logical dependency is: **Step 1** and **Step 2** are independent of each other.
**Step 3** combines them. **Step 4** extends Step 3.

---

## Step 1: Wristband equivalence (complete)

For any distribution Q on nonzero vectors in R^d (d >= 2):

$$\Phi_\# Q = \sigma_{d-1} \otimes \mathrm{Unif}[0,1] \iff Q = \mathcal{N}(0, I_d).$$

This is fully proven in Lean (sorry-free). The forward direction uses Gaussian
polar decomposition + probability integral transform. The backward direction
uses the reverse PIT (requiring strict monotonicity of the chi-square CDF) +
spherical law reconstruction.

Key insight from formalization: the reverse direction critically depends on
**strict monotonicity** of the chi-square CDF — this is what makes `gammainc`
the uniquely correct radial transform, not just a convenient choice.

See [wristband_formalization_audit.md](wristband_formalization_audit.md) for
full details.

---

## Step 2: Kernel energy identifies uniformity (not started)

This is the **hardest remaining step**. It connects the loss function to the
equivalence theorem by showing the repulsion kernel used in the code is
uniquely minimized at the uniform measure on wristband space.

### What needs to be proven

**Hypothesis K (Uniform-energy identification).** For the product kernel
K(w, w') = k_ang(u, u') * k_rad(t, t'):

1. K is **positive semi-definite** and bounded.
2. The uniform measure minimizes the kernel energy:
   E(P) >= E(mu_0) for all distributions P.
3. The minimizer is **unique**: E(P) = E(mu_0) implies P = mu_0.

### The kernel (from Python)

The kernel has two factors, controlled by bandwidth beta > 0 and coupling
alpha > 0.

**Angular factor** (chordal distance on the sphere):

$$k_{\mathrm{ang}}(u, u') = \exp\!\big(-\beta\alpha^2 \|u - u'\|^2\big).$$

**Radial factor** (3-image boundary reflection on [0,1]):

$$k_{\mathrm{rad}}(t, t') = e^{-\beta(t-t')^2} + e^{-\beta(t+t')^2} + e^{-\beta(t+t'-2)^2}.$$

**Joint kernel:** K(w, w') = k_ang(u, u') * k_rad(t, t').

Python refs: `EmbedModels.py:762` (angular exponent), `EmbedModels.py:787–789`
(reflected differences).

> **Geodesic variant.** The code also supports geodesic angular distance
> (arccos). The chordal version is the natural starting point for formalization.

### Proof strategy

There is a standard pathway via two ideas from the kernel methods literature:

**1. Maximum Mean Discrepancy (MMD).** For a positive semi-definite kernel K,
the MMD defines a distance between distributions. If K is **characteristic**
(rich enough to distinguish any two distinct distributions), then MMD = 0 iff
the distributions are identical [8, 9, 16].

**2. Constant-potential argument.** Define the potential function
h(w) = E_{W' ~ mu_0}[K(w, W')]. If h is constant (the kernel "treats all
locations equally" under the uniform measure), then:

$$\mathcal{E}(P) - \mathcal{E}(\mu_0) = \mathrm{MMD}^2(P, \mu_0) \ge 0,$$

with equality iff P = mu_0 (when K is characteristic). This directly
establishes Hypothesis K.

### The 3-image subtlety

The 3-image radial kernel is a truncation of the infinite Neumann reflection
series. For the infinite series, the constant-potential property follows from
symmetry. For the 3-image version, the omitted terms are exponentially small
in beta, so Hypothesis K is either:

- **(a)** proven exactly for the 3-image kernel (harder), or
- **(b)** proven for the infinite series, with a bound showing the 3-image
  truncation error doesn't break uniqueness (more natural).

This is the most technically delicate point in the remaining work.

### What to formalize

1. Define K on `Wristband d × Wristband d → ℝ`.
2. Prove K is positive semi-definite (Gaussian RBF on sphere × reflected
   Gaussian on interval — products of PSD kernels are PSD).
3. Prove the constant-potential property (or an approximation bound).
4. Import or prove that Gaussian RBF on the sphere is characteristic.
5. Conclude Hypothesis K.

---

## Step 3: Main correctness theorem (not started)

**Theorem.** Assuming Hypothesis K, the population repulsion loss
L_rep(Q) = (1/beta) * log E[K(W, W')] is uniquely minimized at Q = gamma.

**Proof.** Three lines:
1. Hypothesis K: kernel energy uniquely minimized at P = mu_0.
2. log is strictly increasing: same minimizer for the log-wrapped loss.
3. Step 1 (wristband equivalence): P_Q = mu_0 iff Q = gamma.

This step is immediate once Step 2 is done.

---

## Step 4: Extra terms preserve the minimizer (not started)

The code's total loss is a weighted sum of four components with z-score
calibration. We need to confirm these don't change the unique minimizer.

### The extra terms

| Term | Python ref | What it measures | Value at Q = gamma |
|------|-----------|-----------------|-------------------|
| Radial penalty (Cramér–von Mises) | `EmbedModels.py:755–759` | Distance of radial marginal from uniform | 0 |
| Moment penalty (Bures–Wasserstein) | `EmbedModels.py:711` | Distance of (mean, cov) from (0, I) | 0 |
| Angular penalty | `EmbedModels.py:772–782` | Angular-only kernel energy | minimized at uniform |

### Why they don't break the minimizer

Two elementary observations:

1. **Nonneg add-ons preserve a unique minimizer.** If f has unique minimizer
   at x*, and g >= 0 with g(x*) = 0, then f + lambda*g has the same unique
   minimizer for any lambda >= 0.

2. **Affine rescaling preserves minimizers.** The z-score calibration
   (L_c - m_c) / s_c with s_c > 0 is an affine transform that doesn't change
   where minima occur.

Since all extra terms are nonneg and vanish at Q = gamma, and calibration is
affine with positive scale, the composite loss has the same unique minimizer.

### What to formalize

This is a short, self-contained argument. Define a general "nonneg-addon"
lemma and apply it to each term. The Bures–Wasserstein closed-form
(W_2^2 = ||mu||^2 + sum(sqrt(lambda_k) - 1)^2) is optional — the only
property needed is nonnegativity and vanishing at gamma.

---

## Step 5: Empirical consistency (optional)

The results above are about the population (infinite-data) loss. Connecting to
finite batches: the batch repulsion statistic is a U-statistic (average of a
bounded symmetric kernel over all pairs). By the law of large numbers for
U-statistics [15], it converges almost surely to the population energy.

This step is standard and low priority for the formalization.

---

## References

[1] K.T. Fang, S. Kotz, K.W. Ng. *Symmetric Multivariate and Related Distributions.* Chapman & Hall, 1990.

[2] G. Casella, R.L. Berger. *Statistical Inference.* 2nd edition, Duxbury, 2002.

[8] B.K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Schölkopf, G.R.G. Lanckriet.
"Hilbert space embeddings and metrics on probability measures." *JMLR*, 11:1517–1561, 2010.

[9] I. Steinwart, A. Christmann. *Support Vector Machines.* Springer, 2008.

[11] E. del Barrio, E. Giné, C. Matrán. "Central limit theorems for the Wasserstein distance between the empirical and the true distributions."
*Ann. Probab.*, 27(2):1009–1071, 1999.

[12] S.G. Bobkov, M. Ledoux. "One-dimensional empirical measures, order statistics, and Kantorovich transport distances."
*Mem. AMS*, 261(1259), 2019.

[15] R.J. Serfling. *Approximation Theorems of Mathematical Statistics.* Wiley, 1980.

[16] A. Berlinet, C. Thomas-Agnan. *Reproducing Kernel Hilbert Spaces in Probability and Statistics.* Springer, 2004.
