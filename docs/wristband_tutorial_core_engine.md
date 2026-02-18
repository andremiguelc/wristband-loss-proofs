# Wristband Tutorial — Core Probabilistic Engine (`wristband_tutorial_core_engine.md`)

This note is a **slow, tutorial-style explanation** of the foundational probabilistic results behind the Wristband method.
It is meant to be readable and reusable as you build a proof repository.

It covers (in this file):

- Pushforward distributions (how “distributions transform” under a map)
- Wristband space and its target “uniform” distribution
- The wristband map \(\Phi\)
- Gaussian polar decomposition (direction + radius)
- Probability integral transform (CDF makes things uniform)
- Spherical reconstruction (direction uniform + radius law determines the whole distribution)
- The wristband equivalence theorem (uniform wristband \(\Leftrightarrow\) standard Gaussian)

> Suggested naming: use **“Core probabilistic engine”** rather than “Goal A.”  
> This is the mathematical mechanism that makes the wristband idea work.

---

## 1) Pushforward: turning one distribution into another

### Definition (Pushforward \(f_\#Q\))
Suppose you have:

- A measurable function \(f:X\to Y\)
- A probability distribution \(Q\) on \(X\)

Then the **pushforward distribution** \(f_\#Q\) is what you get by:

1. Sample \(x\sim Q\)
2. Compute \(y=f(x)\)
3. Look at the distribution of \(y\)

Formally, for any measurable set \(A\subseteq Y\),
\[
(f_\#Q)(A) := Q(f^{-1}(A)).
\]

### Intuition
A distribution is a “random generator of points.” The pushforward answers:

> “If I apply the transformation \(f\) to my random points, what distribution do I get?”

This is the clean formal way to talk about “the distribution of a function of a random variable.”

### Why it matters for wristband
The wristband method transforms a random vector \(Z\in\mathbb R^d\) into wristband coordinates \((U,T)\) using a map \(\Phi\).
So we want a precise name for the resulting distribution:

\(\Phi_\#Q\) is exactly “the distribution of \(\Phi(Z)\) when \(Z\sim Q\).”

---

## 2) Wristband space and its “uniform target”

### Definition (Wristband space)
Let
\[
S^{d-1} := \{u\in\mathbb R^d : \|u\|=1\}
\]
be the unit sphere (all directions). Define the wristband space:
\[
\mathcal W := S^{d-1}\times[0,1].
\]

A point \(w\in\mathcal W\) is a pair \(w=(u,t)\):
- \(u\) is a **direction** (unit vector),
- \(t\) is a number in \([0,1]\) (a “percentile-like” radial coordinate).

### Definition (Uniform wristband distribution)
Let:
- \(\sigma_{d-1}\) be uniform on \(S^{d-1}\),
- \(\lambda\) be uniform on \([0,1]\).

Define the product measure:
\[
\mu_0 := \sigma_{d-1}\otimes \lambda.
\]

This means:
- \(U\sim\sigma_{d-1}\) (direction uniform),
- \(T\sim\lambda\) (radial coordinate uniform),
- and \(U\) and \(T\) are independent.

### Intuition
\(\mu_0\) is “maximally unstructured” on \(\mathcal W\): no preferred direction, no preferred \(t\), no dependence between them.

The wristband method is designed so that a standard Gaussian in \(\mathbb R^d\) maps *exactly* to \(\mu_0\).

---

## 3) The target in \(\mathbb R^d\)

### Definition (Standard Gaussian target)
The “gold standard” distribution is:
\[
\gamma := \mathcal N(0,I_d).
\]

Intuition:
- Centered at \(0\),
- Same variance in all directions,
- No correlations,
- Rotational symmetry: it looks the same after any rotation of space.

---

## 4) The wristband map \(\Phi\)

This is the core engineering choice of the method.

### Definition (Wristband map)
For \(z\in\mathbb R^d\setminus\{0\}\), define
\[
\Phi(z)=(u,t)
:=\left(\frac{z}{\|z\|},\; P\!\left(\frac d2,\frac{\|z\|^2}{2}\right)\right).
\]

- The first part \(u=z/\|z\|\) strips off length and keeps only **direction**.
- The second part turns the squared radius \(\|z\|^2\) into a **CDF value** in \([0,1]\).

Here \(P(a,x)\) is the **regularized lower incomplete gamma** function. The key reason it appears is:

> For a standard Gaussian \(Z\), \(\|Z\|^2\) follows a chi-square distribution, and its CDF can be written using \(P(d/2,\,\|Z\|^2/2)\).

### Definition (Induced wristband distribution)
For any distribution \(Q\) on \(\mathbb R^d\) with \(Q(\{0\})=0\), define:
\[
P_Q := \Phi_\#Q,
\]
the distribution of \((U,T)=\Phi(Z)\) when \(Z\sim Q\).

### Why we assume \(Q(\{0\})=0\)
Because \(u=z/\|z\|\) is undefined at \(z=0\). Continuous distributions (like Gaussians) hit \(0\) with probability \(0\) anyway.

---

## 5) The probabilistic engine behind wristband

Now we explain the two classical results that make \(\Phi\) work.

### Theorem (Gaussian polar decomposition; classical)
Let \(Z\sim\mathcal N(0,I_d)\).
Define \(R:=\|Z\|\) and \(U:=Z/\|Z\|\). Then:

1. \(U\) is uniform on \(S^{d-1}\),
2. \(R^2\sim\chi_d^2\),
3. \(U\) is independent of \(R\) (equivalently independent of \(R^2\)).

#### Intuition
A standard Gaussian is a “perfectly round fog.” Because it has no preferred direction, the direction must be uniform.
And “how far from the origin” is a separate random ingredient that does not influence direction.

#### Key geometric reasoning
For any orthogonal matrix \(O\), \(OZ\stackrel d=Z\). Also,
\[
\frac{OZ}{\|OZ\|}=\frac{OZ}{\|Z\|}=O\left(\frac{Z}{\|Z\|}\right)=OU.
\]
So \(OU\stackrel d=U\) for all rotations \(O\). The only distribution on the sphere with that property is the uniform one.

Also:
\[
R^2=\|Z\|^2=\sum_{i=1}^d Z_i^2
\]
and the sum of squares of \(d\) independent \(\mathcal N(0,1)\) variables is \(\chi_d^2\).

Finally, conditioning on \(R=r\) leaves a uniform distribution over the sphere of radius \(r\), which captures independence of direction and radius.

---

### Theorem (Probability integral transform; classical)
If \(X\) has a continuous CDF \(F\), then
\[
F(X)\sim\mathrm{Unif}[0,1].
\]

#### Intuition
\(F(x)\) tells you “what fraction of the distribution lies below \(x\).”
So \(F(X)\) is the percentile rank of a random draw.
Percentiles are uniform: about 10% of draws are in the bottom 10%, about 50% are in the bottom half, etc.

#### One-line calculation
For \(y\in[0,1]\),
\[
\mathbb P(F(X)\le y)=\mathbb P(X\le F^{-1}(y))=F(F^{-1}(y))=y.
\]

---

## 6) Spherical reconstruction: direction + radius determine the whole distribution

### Lemma (Spherical construction determined by the radius)
Let \(U\sim\sigma_{d-1}\) be uniform on the sphere, and let \(R\ge 0\) be independent of \(U\).
Define \(Z:=RU\). Then:

1) \(Z\) is rotation-invariant (spherically symmetric).  
2) The law of \(Z\) is uniquely determined by the law of \(R\).

#### Intuition
To generate a “round” distribution:
- first choose how far you go from the origin (radius),
- then choose a random direction,
- then multiply.

Once direction is uniform, the only remaining freedom is the radius distribution.

#### Reasoning (slow)
- If \(O\) is any rotation, then \(OU\stackrel d=U\), hence \(ORU=R(OU)\stackrel d=RU\).
- For any set \(A\subset\mathbb R^d\),
  \[
  \mathbb P(RU\in A)=\int_0^\infty \mathbb P(RU\in A\mid R=r)\,d\mathbb P_R(r)
  =\int_0^\infty \sigma_{d-1}(\{u:ru\in A\})\,d\mathbb P_R(r).
  \]
  This shows the distribution is a “mixture over radii,” determined by \(R\).

---

## 7) The wristband equivalence theorem (the cornerstone)

### Theorem (Wristband equivalence)
Let \(Q\) be a distribution on \(\mathbb R^d\) with \(Q(\{0\})=0\). Then
\[
\Phi_\#Q=\mu_0
\quad\Longleftrightarrow\quad
Q=\mathcal N(0,I_d).
\]

This says:

> The wristband coordinates \((U,T)\) are uniform and independent **exactly when** the original distribution is a standard Gaussian.

### Proof, slowly

#### (A) If \(Q=\gamma\), then \(\Phi_\#Q=\mu_0\)
Let \(Z\sim\gamma\).

1. By Gaussian polar decomposition, \(U=Z/\|Z\|\sim\sigma_{d-1}\).
2. Also \(S=\|Z\|^2\sim\chi_d^2\) and \(U\perp S\).
3. Define \(T := F_{\chi_d^2}(S)=P(d/2,S/2)\).
   By the probability integral transform, \(T\sim\mathrm{Unif}[0,1]\).
4. Since \(T\) is a function of \(S\), and \(U\perp S\), we also have \(U\perp T\).

So \((U,T)\) has uniform marginals and independence, hence \((U,T)\sim\mu_0\).

#### (B) If \(\Phi_\#Q=\mu_0\), then \(Q=\gamma\)
Assume \((U,T)=\Phi(Z)\sim\mu_0\) when \(Z\sim Q\). Then:
- \(U\sim\sigma_{d-1}\),
- \(T\sim\mathrm{Unif}[0,1]\),
- \(U\perp T\).

Let \(S:=\|Z\|^2\). By definition of \(\Phi\),
\[
T = F_{\chi_d^2}(S).
\]
Since \(T\) is uniform, this forces \(S\sim\chi_d^2\).
Also, because \(T\) is a (monotone) function of \(S\), the independence \(U\perp T\) implies \(U\perp S\).

Let \(R:=\sqrt S\). Then:
- \(U\sim\sigma_{d-1}\),
- \(R\) has the same distribution as the radius of \(\gamma\),
- \(U\perp R\).

By the spherical reconstruction lemma, the law of \(Z=RU\) is uniquely determined by the law of \(R\).
Since \(\gamma\) has the same \(R\) distribution, \(Q\) must equal \(\gamma\).

---

## 8) Where this fits in a proof repository

A practical structure (both docs and formal proofs) is to split the project into layers:

1. **`probability/`**: wristband map and the equivalence theorem (this file).
2. **`kernels/`**: the repulsion kernel, positive definiteness, “uniform minimizes energy,” and identification conditions.
3. **`objectives/`**: population loss, uniqueness of minimizer, and then empirical estimators / convergence.

This mirrors how the method is built:
- First, \(\Phi\) converts Gaussianity into uniformity on \(\mathcal W\).
- Then, the kernel energy tries to enforce uniformity on \(\mathcal W\).
- Then, the full loss combines pieces for training stability.

---

## 9) References (minimal, high-level)

- Gaussian polar decomposition / spherical symmetry: standard multivariate probability (e.g., Fang–Kotz–Ng; Anderson).
- Probability integral transform: standard statistics (e.g., Casella–Berger).
