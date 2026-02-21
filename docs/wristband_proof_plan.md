# Wristband Gaussian Loss — Proof Plan

This document lays out a **correctness proof** for the Wristband Gaussian Loss (implemented in `C_WristbandGaussianLoss`, see `EmbedModels.py`), written as a guide for formalization in Lean.

**The central claim** is:

> In the idealized (infinite-data) setting, the wristband loss has a **unique minimizer**: the standard Gaussian distribution. No other distribution can achieve the same minimum.

The proof proceeds in four steps:

1. **Wristband equivalence** — Show that a distribution is Gaussian if and only if its wristband-transformed version is uniform. This reduces the problem from "detect Gaussianity" to "detect uniformity."
2. **Kernel energy identifies uniformity** — Show that the repulsion kernel used in the loss is uniquely minimized by the uniform distribution on the wristband space.
3. **Combine (1) and (2)** — Conclude that the repulsion loss uniquely identifies the Gaussian.
4. **Extra terms don't break things** — Show that the additional penalty terms (radial, moment, angular) and calibration preserve the unique minimizer.

The document marks **imported results** (classical theorems we take as given, encoded as axioms in Lean) separately from what we prove ourselves.

---

## Lean proof status

| Proof step | Status | Files |
|------------|--------|-------|
| 1. **Wristband equivalence** (Section 2) | Completed — forward/backward directions and biconditional are proven; imported theorem debt remains isolated | `Foundations.lean`, `ImportedFacts.lean`, `Equivalence.lean` |
| 2. **Kernel energy identifies uniformity** (Sections 3–4) | Not started | — |
| 3. **Main correctness theorem** (Section 5) | Not started | — |
| 4. **Extra terms and calibration** (Section 6) | Not started | — |

---

## 1. Setup: the wristband map and its target space

### What we're working with

We work in \(d\)-dimensional Euclidean space (with \(d \ge 2\)). The key objects are:

- **Standard Gaussian** \(\gamma = \mathcal N(0, I_d)\): the distribution on \(\mathbb R^d\) (d-dimensional real space) with zero mean and identity covariance. This is the distribution we want to prove is the unique minimizer.

- **Unit sphere** \(S^{d-1}\): the set of all unit vectors in \(\mathbb R^d\), i.e., vectors \(u\) with \(\|u\| = 1\) (where \(\|u\|\) denotes the Euclidean length of \(u\)).

- **Wristband space** \(\mathcal W = S^{d-1} \times [0,1]\): the product of the unit sphere and the unit interval. Each point in this space is a pair \((u, t)\) where \(u\) is a direction on the sphere and \(t\) is a number between 0 and 1. Think of it as a cylinder: direction times a radial coordinate.

- **Uniform measure on the wristband space** \(\mu_0\): the probability distribution on \(\mathcal W\) that is uniform in both coordinates independently — uniform over directions on the sphere (denoted \(\sigma_{d-1}\)) and uniform over the interval \([0,1]\). Formally, \(\mu_0 = \sigma_{d-1} \otimes \lambda\) (the product of the two uniform measures).

### The wristband map

The wristband map \(\Phi\) takes a point \(z \in \mathbb R^d\) (with \(z \ne 0\)) and produces a pair \((u, t)\) in the wristband space:

- **Direction**: \(u = z / \|z\|\), the unit vector pointing in the direction of \(z\).
- **Radial CDF value**: \(t = F_{\chi^2_d}(\|z\|^2)\), where \(F_{\chi^2_d}\) is the cumulative distribution function (CDF) of the chi-squared distribution with \(d\) degrees of freedom. The CDF at a value \(x\) gives the probability that a random draw is at most \(x\). So \(t\) answers: "what fraction of a standard Gaussian's probability mass has a squared norm at most \(\|z\|^2\)?" The CDF is computed using the regularized lower incomplete gamma function: \(F_{\chi^2_d}(x) = P(d/2, x/2)\).

The code applies numerical clamps (to avoid division by zero and boundary issues), but the theoretical analysis uses the unclamped, idealized version.

**Pushforward.** Given a distribution \(Q\), we write \(P_Q = \Phi_\# Q\) for the distribution you get by applying \(\Phi\) to every point drawn from \(Q\). Concretely: draw \(z \sim Q\), compute \(\Phi(z)\), and look at the resulting distribution over the wristband space. The notation \(\Phi_\# Q\) (read "pushforward of \(Q\) through \(\Phi\)") is standard: for any region \(A\) in the target space, \((\Phi_\# Q)(A) = Q(\Phi^{-1}(A))\), i.e., the probability that \(\Phi(z)\) lands in \(A\) equals the probability that \(z\) lands in the preimage of \(A\).

---

## 2. Wristband equivalence

This is the core structural result. It says that testing whether \(Q\) is Gaussian is the same as testing whether its wristband image \(P_Q\) is uniform:

**Theorem (Wristband equivalence).** For any distribution \(Q\) on \(\mathbb R^d\) that puts no mass on the origin:
\[
P_Q = \mu_0 \quad\Longleftrightarrow\quad Q = \gamma.
\]

The proof relies on two classical imported results and one lemma.

### Imported results

**Theorem (Gaussian polar decomposition; imported [1]).**
If \(Z\) is drawn from the standard Gaussian, decompose it into direction and magnitude: let \(U = Z/\|Z\|\) (the direction) and \(S = \|Z\|^2\) (the squared norm). Then:
- \(U\) is uniformly distributed on the sphere \(S^{d-1}\),
- \(S\) follows a chi-squared distribution with \(d\) degrees of freedom (the distribution of the sum of \(d\) independent squared standard normals),
- \(U\) and \(S\) are independent (knowing the direction tells you nothing about the magnitude, and vice versa).

**Theorem (Probability integral transform; imported [2]).**
If a random variable \(X\) has a continuous CDF \(F\), then \(F(X)\) is uniformly distributed on \([0,1]\). Conversely, if \(T\) is uniform on \([0,1]\), then \(F^{-1}(T)\) has CDF \(F\). (Recall: the CDF of \(X\) is the function \(F(x) = \mathrm{Prob}(X \le x)\).)

### Reconstruction from direction and radius

**Lemma (Spherical construction is determined by radius).**
If \(U\) is uniform on the sphere and \(R \ge 0\) is independent of \(U\), then the vector \(Z = RU\) is spherically symmetric (its distribution looks the same after any rotation), and the distribution of \(Z\) is completely determined by the distribution of \(R\).

*Proof sketch.* Rotating \(Z = RU\) by any rotation \(O\) gives \(ORU\), but \(OU\) has the same distribution as \(U\) (by uniformity on the sphere), so the distribution of \(Z\) is unchanged. Since the law of \(Z\) is a mixture over radii of uniform shells, knowing the radial distribution pins down everything.

### Proof of the equivalence

**Forward direction** (\(Q = \gamma \Rightarrow P_Q = \mu_0\)):
Start with \(Z \sim \gamma\). By Gaussian polar decomposition, the direction \(U\) is uniform on the sphere and \(S = \|Z\|^2\) is chi-squared, with \(U\) and \(S\) independent. Apply the probability integral transform: \(T = F_{\chi^2_d}(S)\) is uniform on \([0,1]\), and since \(T\) is a function of \(S\) alone, it remains independent of \(U\). So \((U, T)\) is uniform on the wristband space, meaning \(P_\gamma = \mu_0\).

**Reverse direction** (\(P_Q = \mu_0 \Rightarrow Q = \gamma\)):
Suppose the wristband image is uniform. Then the direction \(U\) is uniform on the sphere, \(T\) is uniform on \([0,1]\), and they are independent. Since \(T = F_{\chi^2_d}(S)\) and \(T\) is uniform, the reverse probability integral transform tells us \(S\) has a chi-squared distribution. Because the chi-squared CDF is strictly increasing, \(S\) is a deterministic function of \(T\), so independence of \(U\) and \(T\) implies independence of \(U\) and \(S\). By the reconstruction lemma, \(Z\) is spherically symmetric and determined by the distribution of \(R = \sqrt{S}\). But the standard Gaussian has the same direction-radius distribution (by Gaussian polar decomposition), so \(Q = \gamma\).

---

## 3. The repulsion kernel

With the equivalence established, the remaining task is to show that the loss function used in the code is uniquely minimized when the wristband distribution is uniform — and therefore when the original distribution is Gaussian.

### Why a kernel?

We need a concrete way to measure "how far from uniform" a distribution on the wristband space is. The method uses a **repulsion kernel**: a function \(K(w, w')\) that takes two points in the wristband space and returns a non-negative number measuring their similarity. The idea is that if points are spread uniformly, the average pairwise similarity (the "kernel energy") is minimized. If points cluster together, the energy increases.

### Structure of the kernel

The kernel on the wristband space has two factors — one for direction, one for the radial coordinate — multiplied together. Both are controlled by bandwidth parameters \(\beta > 0\) and \(\alpha > 0\).

**Angular factor.** This measures similarity between directions \(u, u'\) on the sphere using chordal distance (the straight-line distance \(\|u - u'\|\) between two points on the sphere, cutting through the interior):
\[
k_{\mathrm{ang}}(u, u') = \exp\!\big(-\beta\alpha^2 \|u - u'\|^2\big).
\]
This is a Gaussian-shaped kernel restricted to the sphere. Two directions that are close get a value near 1; distant (e.g. antipodal) directions get a value near 0.

**Radial factor (with boundary reflection).** For radial coordinates \(t, t' \in [0,1]\), the code uses a **three-image** trick to handle boundary effects. Instead of a single Gaussian kernel comparing \(t\) and \(t'\), it sums three terms using reflected copies:
\[
k_{\mathrm{rad}}(t, t') = \exp\!\big(-\beta(t-t')^2\big) + \exp\!\big(-\beta(t+t')^2\big) + \exp\!\big(-\beta(t+t'-2)^2\big).
\]
The first term is the standard comparison. The second and third are "reflections" at the boundaries 0 and 1, which prevent the kernel from treating points near the edges differently from points in the interior. (Without reflection, a point at \(t = 0\) would appear to have no neighbors on one side, biasing the energy.)

**Joint kernel.** The full wristband kernel is the product of the angular and radial factors:
\[
K(w, w') = k_{\mathrm{ang}}(u, u') \cdot k_{\mathrm{rad}}(t, t').
\]

> **Note on the geodesic variant.** The code also supports measuring angular distance via the geodesic (arc length along the sphere surface) instead of chordal distance. Proving the required properties for the geodesic variant is more delicate, so we focus the correctness proof on the chordal version.

---

## 4. Population energy and the identification property

### The population objective

In the infinite-data (population) setting, the repulsion loss measures the expected pairwise kernel similarity. For a distribution \(P\) on the wristband space, the **kernel energy** is:
\[
\mathcal E(P) = \mathbb E_{W, W' \sim P}\!\big[K(W, W')\big],
\]
meaning: draw two independent points \(W, W'\) from \(P\) and compute the expected value of their kernel similarity. If \(P\) concentrates its mass, many pairs will be close and the energy will be high. If \(P\) is spread out (uniform), the energy is low.

The population repulsion loss used in the code wraps this in a logarithm: \(\mathcal L_{\mathrm{rep}}(Q) = \frac{1}{\beta}\log \mathcal E(P_Q)\). Since \(\log\) is a strictly increasing function, minimizing the loss is the same as minimizing the energy — they have the same minimizer.

### The key hypothesis

The central property we need from the kernel is:

**Hypothesis K (Uniform-energy identification).**
1. The kernel \(K\) is **positive semi-definite**: for any finite collection of wristband points, the matrix of pairwise kernel values has no negative eigenvalues. (This is a standard regularity condition ensuring the kernel defines a valid notion of similarity.) The kernel is also bounded (its values don't blow up).
2. The uniform measure \(\mu_0\) minimizes the energy: \(\mathcal E(P) \ge \mathcal E(\mu_0)\) for all distributions \(P\).
3. The minimizer is **unique**: if \(\mathcal E(P) = \mathcal E(\mu_0)\), then \(P = \mu_0\).

This hypothesis encapsulates exactly what we need from the kernel. The rest of the proof does not depend on the specific form of the kernel — only on this identification property.

### How to establish Hypothesis K

There is a standard pathway using two ideas from the kernel methods literature:

**Maximum Mean Discrepancy.** For a positive semi-definite kernel \(K\), there is a natural notion of distance between probability distributions called the Maximum Mean Discrepancy (MMD). It measures how much two distributions differ, as seen through the lens of the kernel. The key imported result ([8], [9], [16]) is: if the kernel is **characteristic** — meaning it is rich enough to distinguish any two distinct distributions — then MMD equals zero if and only if the two distributions are identical.

**Constant-potential argument.** Define the **potential function** of the uniform measure: \(h(w) = \mathbb E_{W' \sim \mu_0}[K(w, W')]\), the average kernel value between a fixed point \(w\) and a random uniform point. If this function is the same for every \(w\) (the kernel "treats all locations equally" under the uniform measure), then one can show:
\[
\mathcal E(P) - \mathcal E(\mu_0) = \mathrm{MMD}^2(P, \mu_0) \ge 0,
\]
with equality if and only if \(P = \mu_0\) (when the kernel is characteristic). This directly establishes Hypothesis K.

The three-image kernel is a truncation of an ideal kernel that uses infinitely many reflections (called a "Neumann reflection series"). For the ideal version, the constant-potential property follows from symmetry. For the three-image version, the omitted reflection terms are exponentially small when the bandwidth parameter \(\beta\) is large, so Hypothesis K can be treated as an approximation that becomes exact in the large-\(\beta\) limit.

---

## 5. Main correctness theorem

This is the punchline of the whole proof.

**Theorem (Population correctness of wristband repulsion).**
Assuming Hypothesis K, the population repulsion loss \(\mathcal L_{\mathrm{rep}}(Q)\) has a unique minimizer over all distributions on \(\mathbb R^d\) that put no mass on the origin: the standard Gaussian \(\gamma = \mathcal N(0, I_d)\).

**Proof.** By Hypothesis K, the kernel energy is uniquely minimized at \(P = \mu_0\). Since \(\log\) is strictly increasing, the repulsion loss \(\mathcal L_{\mathrm{rep}}\) is also uniquely minimized when \(P_Q = \mu_0\). By the wristband equivalence theorem (Section 2), \(P_Q = \mu_0\) if and only if \(Q = \gamma\).

---

## 6. Additional loss terms and calibration

The code's loss function is not just the repulsion term — it includes additional penalties and calibration. We need to confirm these do not change the population minimizer.

### Why extra terms?

The repulsion kernel alone is theoretically sufficient to identify the Gaussian. In practice, additional terms help the optimizer converge faster by providing gradient signal for specific aspects of the distribution (its mean, covariance, radial profile).

### Radial uniformity penalty

This term measures how far the radial marginal (the distribution of \(t\) values alone, ignoring direction) is from uniform, using a squared Wasserstein distance (a standard way to measure distance between distributions on the real line, based on how much probability mass needs to be moved to transform one distribution into another; see [11], [12]). The penalty equals zero when the radial marginal is exactly uniform — which is the case when \(Q = \gamma\).

### Moment penalty

This term measures how far the mean and covariance of \(Q\) are from those of the standard Gaussian (zero mean, identity covariance matrix), using a squared Wasserstein distance between Gaussian approximations. It equals zero when \(Q\) has the correct first two moments — which the standard Gaussian does.

### Why they don't break the minimizer

Two simple observations:

1. **Nonnegative add-ons preserve a unique minimizer.** If a function \(f\) has a unique minimizer at some point \(x^\star\), and we add another function \(g\) that is always nonnegative and equals zero at \(x^\star\), then \(f + \lambda g\) (for any weight \(\lambda \ge 0\)) still has the same unique minimizer.
2. **Affine rescaling preserves minimizers.** Multiplying a function by a positive constant and adding a constant does not change where its minimum occurs.

Since all the extra terms are nonnegative and equal zero at \(Q = \gamma\), and the code's calibration (centering and rescaling each term by its mean and standard deviation under the null distribution, using positive scale factors) is an affine transformation, the composite loss has the same unique minimizer as the repulsion term alone.

**Corollary (Population correctness of the full wristband loss).**
Under Hypothesis K, any positive-weight combination of the repulsion, radial, moment, and angular penalty terms — with any affine calibration using positive scale — is uniquely minimized at \(Q = \gamma\).

---

## 7. Empirical consistency (optional)

The results above are about the **population** (infinite-data) loss. To connect this to what the code actually computes with finite batches, we need the finite-sample estimate to converge to the population value.

The batch repulsion statistic is an average over all pairs of points in the batch. This is a standard statistical object called a **U-statistic**: an unbiased estimator computed by averaging a symmetric function (here, the kernel) over all distinct pairs from a sample. By the law of large numbers for U-statistics (imported from [15]), if the kernel is bounded, the batch average converges almost surely to the population energy as the batch size grows. This justifies that minimizing the empirical loss approximates minimizing the population loss.

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
