# Wristband Gaussian Loss — Correctness Framework (Lean-friendly)

This note provides a **formal, proof-oriented framework** for the “Wristband Gaussian Loss” used in `C_WristbandGaussianLoss` (see `EmbedModels.py`).
It is written as a **theorem/lemma/definition** chain suitable as a basis for later formalization (e.g., in Lean).

The focus is the **population correctness objective**:

> In the infinite-data / population limit, the Wristband loss should have a **unique minimizer** at the standard Gaussian  
> \(\gamma := \mathcal N(0,I_d)\), and no non-Gaussian distribution should achieve the same optimum.

We aim for a balance:
- Strong enough statements to support a correctness proof;
- Not over-generalizing beyond what the method uses;
- Explicitly marking **imported external results** (which a formal proof assistant may treat as axioms or later formalize).

---

## 0. High-level plan

Let \(Q\) be a distribution on \(\mathbb R^d\). The method computes a “wristband representation”
\((u,t)=\Phi(z)\) where \(u\) is direction and \(t\) is a CDF-transformed radius.

Correctness is proved by the chain:

1. **Wristband equivalence**:  
   \[
   \Phi_\# Q = \mu_0 \quad\Longleftrightarrow\quad Q = \gamma
   \]
   where \(\mu_0\) is uniform on the wristband space \(\mathcal W = S^{d-1}\times[0,1]\).
2. **Kernel energy identifies uniformity**: the repulsion kernel has a population objective uniquely minimized by \(\mu_0\).
3. Combine (1) and (2) to conclude the repulsion loss uniquely identifies \(\gamma\).
4. Show additional nonnegative penalty terms and calibration do **not** change the population minimizer.

---

## 1. Measure-theoretic setup and notation

Fix an integer \(d\ge 2\).

- Let \(\mathcal B(\mathbb R^d)\) be the Borel \(\sigma\)-algebra, and \(\mathcal P(\mathbb R^d)\) the set of Borel probability measures.
- Let \(S^{d-1} := \{u\in\mathbb R^d : \|u\|=1\}\) with Borel \(\sigma\)-algebra.
- Let \([0,1]\) have its Borel \(\sigma\)-algebra.

**Definition (Pushforward).**  
If \(f:X\to Y\) is measurable and \(Q\in \mathcal P(X)\), define the pushforward \(f_\#Q\in\mathcal P(Y)\) by
\((f_\#Q)(A):=Q(f^{-1}(A))\).

**Definition (Wristband space and uniform measure).**
Define the wristband space and its uniform measure:
\[
\mathcal W := S^{d-1}\times[0,1],\qquad
\mu_0 := \sigma_{d-1}\otimes\lambda,
\]
where:
- \(\sigma_{d-1}\) is the Haar (uniform) probability measure on \(S^{d-1}\);
- \(\lambda\) is the uniform probability measure on \([0,1]\).

**Definition (Target distribution).**  
\(\gamma := \mathcal N(0,I_d)\).

---

## 2. Wristband map

The code computes:
- \(s=\|z\|^2\),
- \(u=z/\|z\|\),
- \(t=\mathrm{gammainc}(d/2,\; s/2)\), clamped to \((\varepsilon,1-\varepsilon)\) for numerical stability.

Theoretical statements ignore the clamp (it changes nothing at population level under absolutely continuous laws).

Let \(P(a,x)\) denote the **regularized lower incomplete gamma** function. For \(S\sim\chi^2_d\),
\(\mathbb P(S\le s) = P(d/2,\; s/2)\).

**Definition (Wristband map \(\Phi\)).**  
For \(z\in\mathbb R^d\setminus\{0\}\), define
\[
\Phi(z):=(u,t)
:=\left(\frac{z}{\|z\|},\; P\!\left(\frac d2,\frac{\|z\|^2}{2}\right)\right)\in \mathcal W.
\]
For \(Q\in\mathcal P(\mathbb R^d)\) satisfying \(Q(\{0\})=0\), define the induced wristband distribution
\[
P_Q := \Phi_\# Q\in\mathcal P(\mathcal W).
\]

---

## 3. Wristband equivalence: \(\Phi_\#Q=\mu_0\iff Q=\gamma\)

This section is the “information preservation” result: testing Gaussianity of \(Q\) is equivalent to testing uniformity of \(P_Q\).

### 3.1 Imported facts about Gaussians and the probability integral transform

**Theorem (Gaussian polar decomposition; imported).**  
Let \(Z\sim \mathcal N(0,I_d)\). Define \(R:=\|Z\|\) and \(U:=Z/\|Z\|\). Then:
1. \(U\sim \sigma_{d-1}\),
2. \(R^2\sim \chi^2_d\),
3. \(U\) is independent of \(R\) (equivalently \(R^2\)).

*(Reference: [1], Ch. 2; see also standard multivariate analysis texts.)*

**Theorem (Probability integral transform; imported).**  
If \(X\) has a continuous CDF \(F\), then \(F(X)\sim\mathrm{Unif}[0,1]\).

*(Reference: [2], Ch. 2.)*

### 3.2 Direction–radius reconstruction

**Lemma (Spherical construction is determined by radius).**  
Let \(U\sim \sigma_{d-1}\) and \(R\ge 0\) be a real random variable independent of \(U\).
Define \(Z:=RU\in\mathbb R^d\). Then:
1. \(Z\) is rotation-invariant (spherically symmetric);
2. the law of \(Z\) is uniquely determined by the law of \(R\).

**Proof (sketch).**  
(1) For any orthogonal matrix \(O\), \(OU\stackrel d=U\), so \(ORU\stackrel d=RU\).  
(2) For any Borel \(A\subset\mathbb R^d\),
\(\mathbb P(RU\in A)=\int_0^\infty \sigma_{d-1}(\{u:ru\in A\})\,d\mathbb P_R(r)\),
so the mixture over radii determines the law. \(\square\)

### 3.3 Main wristband equivalence theorem

**Theorem (Wristband equivalence).**  
Let \(Q\in\mathcal P(\mathbb R^d)\) satisfy \(Q(\{0\})=0\). Then
\[
P_Q=\mu_0
\quad\Longleftrightarrow\quad
Q=\gamma.
\]

**Proof.**

**(\(\Rightarrow\))** Suppose \(Q=\gamma\). By the Gaussian polar decomposition theorem, \(U:=Z/\|Z\|\sim\sigma_{d-1}\) and \(S:=\|Z\|^2\sim\chi^2_d\) with \(U\perp S\).
Define \(T:=P(d/2,\;S/2)\). Since \(T\) is the CDF of \(S\), by the Probability integral transform theorem we have \(T\sim\mathrm{Unif}[0,1]\), and \(U\perp T\).
Thus \((U,T)\sim\sigma_{d-1}\otimes\lambda=\mu_0\), i.e. \(P_\gamma=\mu_0\).

**(\(\Leftarrow\))** Suppose \(P_Q=\mu_0\).
Let \(Z\sim Q\) and set \((U,T):=\Phi(Z)\). Then \(U\sim\sigma_{d-1}\), \(T\sim\mathrm{Unif}[0,1]\), and \(U\perp T\).
Let \(S:=\|Z\|^2\). By definition \(T=P(d/2,\;S/2)=F_{\chi^2_d}(S)\). Since \(T\) is uniform, \(S\sim\chi^2_d\), and \(U\perp S\).
Let \(R:=\sqrt S\). By the spherical construction determined by radius lemma, \(Z\) is spherically symmetric and determined by the law of \(R\).
But \(\gamma\) has the same pair \((U,R)\) distribution (by Gaussian polar decomposition), hence \(Q=\gamma\). \(\square\)

---

## 4. Repulsion kernel used by the method

The code builds a kernel on \(\mathcal W\) with:
- an **angular** Gaussian factor using either chordal or geodesic distance on \(S^{d-1}\);
- a **radial** Gaussian factor in \(t\);
- a **3-image reflection** in \(t\) to reduce boundary bias near \(t=0\) and \(t=1\).

For a clean correctness theorem we formalize the **chordal** variant (which is PSD by restriction of the Euclidean Gaussian kernel).

### 4.1 Angular component (chordal)

Fix parameters \(\beta>0\) and \(\alpha>0\).

**Definition (Chordal distance).**
For \(u,u'\in S^{d-1}\),
\[
d_{\mathrm{ch}}(u,u') := \|u-u'\|.
\]
Equivalently \(d_{\mathrm{ch}}^2(u,u')=2-2\langle u,u'\rangle\).

**Definition (Angular kernel).**
\[
k_{\mathrm{ang}}(u,u') := \exp\!\big(-\beta\alpha^2\, d_{\mathrm{ch}}^2(u,u')\big).
\]

### 4.2 Radial component (3-image reflection as in code)

**Definition (Three-image displacements).**
For \(t,t'\in[0,1]\) define
\[
\delta_0(t,t') := t-t',\qquad
\delta_1(t,t') := t+t',\qquad
\delta_2(t,t') := t+t'-2.
\]

**Definition (Three-image radial kernel).**
\[
k_{\mathrm{rad}}^{(3)}(t,t') := \sum_{m=0}^{2}\exp\!\big(-\beta\,\delta_m(t,t')^2\big).
\]

### 4.3 Joint kernel on the wristband

**Definition (Wristband kernel \(K^{(3)}\)).**
For \(w=(u,t)\), \(w'=(u',t')\in\mathcal W\),
\[
K^{(3)}(w,w')
:=k_{\mathrm{ang}}(u,u')\,k_{\mathrm{rad}}^{(3)}(t,t')
=\sum_{m=0}^{2}\exp\!\Big(-\beta\big(\alpha^2 d_{\mathrm{ch}}^2(u,u')+\delta_m(t,t')^2\big)\Big).
\]

This matches the code’s joint repulsion terms computed via:
\(\exp(e_{\mathrm{ang}}-\beta\,\delta_m^2)\) summed over \(m\in\{0,1,2\}\).

---

## 5. Population repulsion objective

To analyze correctness we define the population (infinite-data) functional corresponding to the repulsion term.

**Definition (Kernel energy).**  
For \(P\in\mathcal P(\mathcal W)\), define
\[
\mathcal E^{(3)}(P):=\iint_{\mathcal W\times\mathcal W}K^{(3)}(w,w')\,dP(w)\,dP(w').
\]
Equivalently, if \(W,W'\stackrel{iid}{\sim}P\),
\(\mathcal E^{(3)}(P)=\mathbb E[K^{(3)}(W,W')]\).

**Definition (Population repulsion loss).**  
For \(Q\in\mathcal P(\mathbb R^d)\) with \(Q(\{0\})=0\), define
\[
\mathcal L_{\mathrm{rep}}(Q) := \frac{1}{\beta}\log \mathcal E^{(3)}(P_Q).
\]
Since \(\log\) is strictly increasing, \(\arg\min \mathcal L_{\mathrm{rep}} = \arg\min \mathcal E^{(3)}\).

---

## 6. Kernel conditions needed for correctness

The full analytic proof that \(\mu_0\) uniquely minimizes \(\mathcal E^{(3)}\) for the **3-image** kernel is nontrivial.
However, the method only needs an “identification property”:
the energy should be uniquely minimized at the uniform wristband measure.

We isolate that as an explicit hypothesis.

**Hypothesis K (Uniform-energy identification).**  
The kernel \(K^{(3)}\) satisfies:
1. (**PSD & bounded**) \(K^{(3)}\) is positive semidefinite and bounded on \(\mathcal W\).
2. (**Uniform minimizes energy**) for all \(P\in\mathcal P(\mathcal W)\),
   \(\mathcal E^{(3)}(P)\ge \mathcal E^{(3)}(\mu_0)\).
3. (**Uniqueness**) if \(\mathcal E^{(3)}(P)=\mathcal E^{(3)}(\mu_0)\) then \(P=\mu_0\).

> **Remark.** For an *idealized* kernel that uses a **full Neumann reflection series** on \([0,1]\) (instead of 3 images),
> one can typically prove Hypothesis K using RKHS mean embeddings (characteristic kernels) and symmetry/constant-potential arguments.
> The 3-image kernel is a truncation of that ideal object; Hypothesis K can be treated as an approximation assumption justified when
> omitted images contribute negligibly (large \(\beta\)).

### Optional: sufficient conditions implying Hypothesis K (imported framework)

The following “sufficient condition route” is useful for a formal proof plan:

**Definition (MMD for a PSD kernel).**  
Let \(K\) be PSD and bounded on \(\mathcal W\). Define for \(P,Q\in\mathcal P(\mathcal W)\):
\[
\mathrm{MMD}_K^2(P,Q)
:=\mathbb E[K(X,X')]+\mathbb E[K(Y,Y')]-2\,\mathbb E[K(X,Y)]
\]
where \(X,X'\stackrel{iid}{\sim}P\), \(Y,Y'\stackrel{iid}{\sim}Q\), independent.

**Theorem (Characteristic kernel; imported).**  
If \(K\) is **characteristic** on \(\mathcal W\), then
\(\mathrm{MMD}_K(P,Q)=0\iff P=Q\).

*(Reference: [8], [9], [16].)*

**Lemma (Constant potential \(\Rightarrow\) energy difference equals MMD; standard).**  
Let \(K\) be PSD and bounded. Fix a measure \(\mu\in\mathcal P(\mathcal W)\) and define the potential
\(h(w):=\int K(w,w')\,d\mu(w')\).
If \(h\) is constant \(\mu\)-a.e. (or everywhere), then for all \(P\in\mathcal P(\mathcal W)\),
\[
\mathcal E_K(P)-\mathcal E_K(\mu)=\mathrm{MMD}_K^2(P,\mu)\ge 0.
\]

**Proof.** Expand \(\mathrm{MMD}_K^2(P,\mu)=\mathcal E_K(P)+\mathcal E_K(\mu)-2\iint K\,dP\,d\mu\).
Using \(\iint K\,dP\,d\mu=\int h\,dP\) and \(\int h\,d\mu = \mathcal E_K(\mu)\), the constant-potential condition implies
\(\int h\,dP=\int h\,d\mu=\mathcal E_K(\mu)\), giving the identity. \(\square\)

**Corollary (Uniqueness via characteristicness).**  
If \(K\) is characteristic and \(h\) is constant for \(\mu=\mu_0\), then \(\mu_0\) is the unique minimizer of \(\mathcal E_K\).

This corollary is the typical “external-results” pathway to establish Hypothesis K for a suitably symmetric kernel.

---

## 7. Main correctness theorem (population)

**Theorem (Population correctness of wristband repulsion).**  
Assume Hypothesis K holds for \(K^{(3)}\). Then the population repulsion loss
\(\mathcal L_{\mathrm{rep}}(Q)\) has a unique minimizer over \(\{Q\in\mathcal P(\mathbb R^d):Q(\{0\})=0\}\),
namely
\[
Q^\star=\gamma=\mathcal N(0,I_d).
\]

**Proof.**
By Hypothesis K(2–3), \(\mathcal E^{(3)}(P)\) is uniquely minimized at \(P=\mu_0\).
Since \(\log\) is strictly increasing, the same holds for \(\mathcal L_{\mathrm{rep}}(Q)\), so its unique minimizer must satisfy
\(P_Q=\mu_0\).
By the Wristband equivalence theorem, \(P_Q=\mu_0\iff Q=\gamma\). \(\square\)

---

## 8. Adding radial/moment penalties and calibration

The code’s returned scalar is a **calibrated** sum of components:
\(\text{total} = \text{zscore(rep)} + \lambda_{\mathrm{rad}}\text{zscore(rad)} + \lambda_{\mathrm{ang}}\text{zscore(ang)} + \lambda_{\mathrm{mom}}\text{zscore(mom)}\).
Calibration is an affine transformation under the null, which does not change population minimizers.

### 8.1 Radial uniformity term (as used in code)

The code’s radial term is an empirical \(W_2^2\)-style functional on \(t\in[0,1]\), up to a positive scale factor.
At population level we can define the canonical target.

**Definition (Radial marginal).**  
For \(P\in\mathcal P(\mathcal W)\), let \(P^t := (\pi_t)_\# P\in\mathcal P([0,1])\).

**Definition (Population radial penalty).**
\[
\mathcal L_{\mathrm{rad}}(Q):= W_2^2(P_Q^t,\lambda).
\]
Then \(\mathcal L_{\mathrm{rad}}(Q)\ge 0\) and equals \(0\) iff \(P_Q^t=\lambda\).

*(References for Wasserstein basics: [11], [12].)*

### 8.2 Moment penalty (one example: Gaussian \(W_2^2\))

The code supports several moment penalties; the cleanest population statement is for squared Wasserstein distance between Gaussians.

Assume \(Q\) has finite second moment. Let \(\mu_Q:=\mathbb E_Q[Z]\) and \(\Sigma_Q:=\mathrm{Cov}_Q(Z)\).

**Definition (Gaussian moment penalty).**
\[
\mathcal L_{\mathrm{mom}}(Q):=\frac{1}{d}W_2^2\big(\mathcal N(\mu_Q,\Sigma_Q),\;\mathcal N(0,I_d)\big).
\]
Then \(\mathcal L_{\mathrm{mom}}(Q)\ge 0\) and equals \(0\) iff \(\mu_Q=0\) and \(\Sigma_Q=I_d\).

### 8.3 Composite loss does not change the population minimizer

**Lemma (Nonnegative add-ons preserve a unique minimizer).**  
Let \(f\) have a unique minimizer at \(x^\star\).
If \(g\ge 0\) and \(g(x^\star)=0\), then \(f+\lambda g\) has the same unique minimizer for any \(\lambda\ge 0\).

**Lemma (Affine calibration preserves minimizers).**  
If \(a>0\) and \(b\in\mathbb R\), then \(\arg\min f = \arg\min (af+b)\).

**Corollary (Population correctness of the full wristband loss).**  
Assume the Population correctness of wristband repulsion theorem (repulsion term has unique minimizer \(\gamma\)).
Let \(\lambda_{\mathrm{rad}},\lambda_{\mathrm{mom}},\lambda_{\mathrm{ang}}\ge 0\) and define any calibrated/affine combination of
\(\mathcal L_{\mathrm{rep}},\mathcal L_{\mathrm{rad}},\mathcal L_{\mathrm{mom}}\) (and an optional angular-only uniformity term).
Then the composite population loss is uniquely minimized at \(Q=\gamma\).

---

## 9. Optional: empirical estimator consistency (for algorithmic correctness)

To connect population correctness to the batch loss, one typically shows that the batch statistic estimates \(\mathcal E^{(3)}(P_Q)\).

Let \(W_1,\dots,W_N\stackrel{iid}{\sim}P\) and consider the U-statistic
\(\widehat{\mathcal E}_N := \frac{1}{N(N-1)}\sum_{i\ne j}K^{(3)}(W_i,W_j)\).
The “global” reduction is essentially \(\log \widehat{\mathcal E}_N\) up to diagonal/image conventions.

**Theorem (Law of large numbers for U-statistics; imported).**  
If \(K^{(3)}\) is bounded, then \(\widehat{\mathcal E}_N\to \mathcal E^{(3)}(P)\) almost surely as \(N\to\infty\).

*(Reference: [15] for U-statistics and convergence.)*

This justifies that minimizing the empirical repulsion approximates minimizing the population energy.

---

## 10. Notes on the geodesic option

The code optionally uses a geodesic distance on the sphere:
\(\theta(u,u')=\arccos(\langle u,u'\rangle)\) and kernel factor \(\exp(-\beta\alpha^2\theta^2)\).

A full correctness proof for the geodesic squared-exponential kernel requires care: positive definiteness and characteristicness on
curved manifolds are more delicate than in the chordal case. For a clean correctness theorem, the chordal variant is the safest default.

---

## 11. Bibliography (as in the project document)

[1] K.T. Fang, S. Kotz, K.W. Ng. *Symmetric Multivariate and Related Distributions.* Chapman & Hall, 1990.

[2] G. Casella, R.L. Berger. *Statistical Inference.* 2nd edition, Duxbury, 2002.

[3] I.J. Schoenberg. "Metric spaces and positive definite functions." *Trans. AMS*, 44(3):522–536, 1938.

[4] H. Wendland. *Scattered Data Approximation.* Cambridge University Press, 2005.

[5] R. Gangolli. "Positive definite kernels on homogeneous spaces and certain stochastic processes related to Lévy's Brownian motion of several parameters."
*Ann. Inst. Henri Poincaré (B)*, 3(2):121–226, 1967.

[6] F. Dai, Y. Xu. *Approximation Theory and Harmonic Analysis on Spheres and Balls.* Springer, 2013.

[7] N.S. Landkof. *Foundations of Modern Potential Theory.* Springer, 1972.

[8] B.K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Schölkopf, G.R.G. Lanckriet.
"Hilbert space embeddings and metrics on probability measures." *JMLR*, 11:1517–1561, 2010.

[9] I. Steinwart, A. Christmann. *Support Vector Machines.* Springer, 2008.

[10] A. Gretton, K.M. Borgwardt, M.J. Rasch, B. Schölkopf, A. Smola, et al.
"A kernel two-sample test." *JMLR*, 13:723–773, 2012.

[11] E. del Barrio, E. Giné, C. Matrán. "Central limit theorems for the Wasserstein distance between the empirical and the true distributions."
*Ann. Probab.*, 27(2):1009–1071, 1999.

[12] S.G. Bobkov, M. Ledoux. "One-dimensional empirical measures, order statistics, and Kantorovich transport distances."
*Mem. AMS*, 261(1259), 2019.

[13] R. Vershynin. *High-Dimensional Probability.* Cambridge University Press, 2018.

[14] T.W. Anderson. *An Introduction to Multivariate Statistical Analysis.* 3rd edition, Wiley, 2003.

[15] R.J. Serfling. *Approximation Theorems of Mathematical Statistics.* Wiley, 1980.

[16] A. Berlinet, C. Thomas-Agnan. *Reproducing Kernel Hilbert Spaces in Probability and Statistics.* Springer, 2004.

[17] Y.I. Ingster, I.A. Suslina. *Nonparametric Goodness-of-Fit Testing Under Gaussian Models.* Springer, 2003.
