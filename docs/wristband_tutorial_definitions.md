# Wristband — Foundational Tutorial (Step-by-step)

This tutorial explains, very slowly and intuitively, the most foundational pieces of the wristband correctness framework.

It covers:

1. **Definition (Pushforward)**  
2. **Definition (Wristband space \(\mathcal W\) and uniform measure \(\mu_0\))**  
3. **Definition (Target distribution \(\gamma\))**  
4. **Definition (Wristband map \(\Phi\))**

The goal is to make the meaning of each object obvious before we move on to deeper theorems.

---

## Pushforward \(f_\#Q\)

### The statement

If you have:
- a measurable function \(f:X\to Y\), and
- a probability distribution \(Q\) on \(X\),

then the **pushforward** distribution \(f_\#Q\) is the distribution you get by:

1. sampling \(x\sim Q\),
2. computing \(y=f(x)\),
3. looking at the distribution of \(y\).

Formally, for any measurable set \(A\subseteq Y\),
\[
(f_\#Q)(A) := Q(f^{-1}(A)).
\]

### What this means in plain language

Think of a distribution as a “random generator of points.” The pushforward just means:

> “What distribution do I get after I apply my transformation to random samples?”

It is the clean way to talk about “the distribution of a function of a random variable.”

### Why we need it for wristband

The wristband method takes a random vector \(Z\in\mathbb R^d\) and transforms it into wristband coordinates \((U,T)\) using \(\Phi\).
So we want to talk about:

> the distribution of \((U,T)\) when \(Z\sim Q\)

That distribution is exactly:
\[
P_Q := \Phi_\#Q.
\]

So pushforward is the formal bridge:
- original distribution in \(\mathbb R^d\)  
→ transformed distribution on the wristband.

### Tiny example to make it concrete

Let \(X=\mathbb R\), \(Q\) = distribution of a random number \(X\).  
Let \(f(x)=x^2\).  
Then \(f_\#Q\) is the distribution of \(X^2\).

The wristband version is the same idea, but \(f=\Phi\) is “take direction and CDF-radius.”

---

## Wristband space \(\mathcal W\) and “uniform wristband” \(\mu_0\)

### The statement

We define the wristband space:
\[
\mathcal W := S^{d-1}\times[0,1].
\]

- \(S^{d-1}\) is the set of unit vectors in \(\mathbb R^d\). (All directions.)
- \([0,1]\) is the unit interval.

We define the uniform wristband measure:
\[
\mu_0 := \sigma_{d-1}\otimes\lambda,
\]
where:
- \(\sigma_{d-1}\) is the uniform distribution on the sphere \(S^{d-1}\),
- \(\lambda\) is the uniform distribution on \([0,1]\),
- \(\otimes\) means: **independent product distribution**.

### What this means in plain language

\(\mathcal W\) is a “two-part coordinate system”:

- pick a direction \(u\) on the sphere,
- pick a number \(t\) in \([0,1]\).

So a point on the wristband is \((u,t)\).

And \(\mu_0\) is the simplest possible distribution on this space:

> “Direction is completely random, and the \(t\) coordinate is completely random, and they are independent.”

### Why this is exactly what wristband wants

The wristband method tries to convert Gaussianity into “uniformity”:

- A standard Gaussian has no preferred direction → direction should be uniform on the sphere.
- A standard Gaussian’s radius has a specific distribution → after a CDF transform, it becomes uniform on \([0,1]\).
- For a standard Gaussian, direction and radius are independent.

So “Gaussian in \(\mathbb R^d\)” becomes:

> “uniform on the wristband \(\mathcal W\)” i.e. \(\mu_0\).

That is why \(\mu_0\) is the target *after transformation*.

### A physical analogy

Imagine you have a perfectly symmetric explosion at the origin in \(d\) dimensions.

- It doesn’t prefer any direction → directions are uniform.
- It has a certain law for how far fragments fly.
- If you convert “distance” into a percentile (“how far compared to typical?”), those percentiles are uniform.

That is exactly what \(\mu_0\) captures.

---

## The target distribution \(\gamma = \mathcal N(0,I_d)\)

### The statement

\[
\gamma := \mathcal N(0,I_d).
\]

This means:
- mean is \(0\),
- covariance matrix is \(I_d\) (identity).

### What this means intuitively

A draw \(Z\sim\gamma\) is the most “standard” multivariate Gaussian:

- centered at the origin,
- same variance in every coordinate,
- no correlations between coordinates,
- rotational symmetry: it looks the same if you rotate space.

### Why it is singled out

Because the wristband method is a normalization target. In many machine learning contexts, you want representations that look like:

> “white noise Gaussian”

So the “correctness” statement is:

> If the loss is minimized, the distribution must match \(\gamma\).

That is the core correctness objective.

---

## The wristband map \(\Phi\)

This is the heart of the method.

### The statement

For \(z\neq 0\),
\[
\Phi(z) = (u,t)
:=\left(\frac{z}{\|z\|},\; P\!\left(\frac d2,\frac{\|z\|^2}{2}\right)\right).
\]

So:
- \(u = z/\|z\|\) is the **direction** (unit vector).
- \(t = P(d/2,\|z\|^2/2)\) is the **CDF of a chi-square distribution evaluated at \(\|z\|^2\)**.

(That function \(P\) is the regularized incomplete gamma function; for this particular choice, it equals the cumulative distribution function of \(\chi_d^2\).)

We also define:
\[
P_Q := \Phi_\#Q,
\]
the distribution of wristband coordinates when \(z\sim Q\).

### Why these exact formulas?

Let us unpack each component.

#### Part 1: \(u = z/\|z\|\)

This strips off length and keeps only direction.

- If \(z\) points northeast, \(u\) is “northeast” but normalized to length 1.
- It maps every nonzero \(z\) onto the sphere.

This is what you want if you want to measure “is there a preferred direction?”

If your distribution is truly spherical like a standard Gaussian, the directions should be perfectly uniform.

#### Part 2: \(t = P(d/2,\|z\|^2/2)\)

This looks scary, but the idea is simple:

1. For a standard Gaussian \(Z\), the squared radius
   \[
   \|Z\|^2
   \]
   follows a known distribution: **chi-square with \(d\) degrees of freedom**.

2. If you take a random variable \(X\) and apply its own cumulative distribution function \(F\), then \(F(X)\) becomes uniform on \([0,1]\).
   This is the “probability integral transform” (we will explain it slowly later).

So the purpose of \(t\) is:

> convert “how far from the origin” into a percentile that is uniform under the Gaussian.

That makes the radius information comparable across dimensions and stable.

### The big design idea of \(\Phi\)

\(\Phi\) is engineered so that:

- If \(Q\) is Gaussian, \(\Phi_\#Q\) becomes the uniform wristband measure \(\mu_0\).
- And (crucially) if \(\Phi_\#Q\) is uniform wristband, then \(Q\) must have been Gaussian.

So \(\Phi\) is meant to be an “equivalence transformation” for Gaussianity.

### Why do we require \(Q(\{0\})=0\)?

Because \(u=z/\|z\|\) is undefined at \(z=0\).

In practice:
- a continuous distribution like a Gaussian hits exactly 0 with probability 0 anyway,
- but the condition keeps the math clean.

---

## Where we go next

Now that we have the objects, the next step is to justify the two key facts that make the wristband idea work:

1. **Gaussian polar decomposition**: Gaussian → direction is uniform and independent of radius  
2. **Probability integral transform**: applying the right CDF to radius → uniform \([0,1]\)

These are the **Gaussian polar decomposition theorem** and the
**Probability integral transform theorem** in the framework document, and they are the “engine” behind the wristband equivalence.
