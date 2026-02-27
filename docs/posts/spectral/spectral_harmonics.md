# Spherical Harmonics and the Spectral Decomposition of the Wristband Kernel

This document derives, step by step, *why* the Mercer eigenfunctions of our
angular kernel are spherical harmonics, *how* the eigenvalues are computed
via Gegenbauer polynomials and Bessel functions, and *what* the resulting
spectral decomposition of the full wristband kernel looks like.

**Prerequisites:** Basic familiarity with linear algebra, calculus, and the
notation $S^{d-1}$ for the unit sphere in $\mathbb{R}^d$.  No prior
knowledge of spherical harmonics, Gegenbauer polynomials, or Bessel
functions is assumed — everything is derived from scratch.

**Notation.** Throughout, $d \geq 3$ and $\nu = (d-2)/2 > 0$.

---

## 1. Why the eigenfunctions are spherical harmonics

### 1.1 Setup: the integral operator of a kernel

Given a continuous, symmetric, PSD kernel $K$ on a compact space $(X, \mu)$,
define the integral operator:

$$T_K f(x) = \int_X K(x, y)\, f(y)\, d\mu(y).$$

Three properties follow from the assumptions on $K$:

- **Self-adjoint:** $K(x,y) = K(y,x)$ implies $\langle T_K f, g\rangle = \langle f, T_K g\rangle$.
- **Compact:** continuity of $K$ on compact $X$ gives $K \in L^2(\mu \otimes \mu)$,
  so $T_K$ is Hilbert–Schmidt, hence compact.
- **Positive:** PSD of $K$ implies $\langle T_K f, f\rangle \geq 0$.

The spectral theorem for compact self-adjoint operators gives a countable
orthonormal eigenbasis $\{\varphi_j\}$ with real eigenvalues $\lambda_j \geq 0$,
$\lambda_j \to 0$.

Mercer's theorem is the *separate* strengthening: when $K$ is continuous,
the eigenexpansion $K(x,y) = \sum_j \lambda_j \varphi_j(x)\varphi_j(y)$
converges *pointwise and uniformly* — not just in $L^2$.

> **What is a compact operator?**
> $T_K$ maps bounded sets to *precompact* sets — sets whose closure is compact.
> Intuitively, $T_K$ "squishes" the infinite-dimensional unit ball into something
> finite-dimensional.  For continuous kernels on compact spaces, $T_K$ is
> Hilbert–Schmidt: $\|T_K\|_{\text{HS}}^2 = \int\!\int |K(x,y)|^2\,d\mu(x)\,d\mu(y) < \infty$.
> Every Hilbert–Schmidt operator is compact.
>
> **Why compactness matters.** The spectral theorem for *compact* self-adjoint
> operators guarantees a *countable* eigenbasis with $\lambda_j \to 0$.
> Without compactness, the spectrum can be continuous with no eigenfunctions.
> Without self-adjointness, eigenvalues may be complex.  Together, they force
> the clean discrete decomposition that Mercer's theorem requires.

### 1.2 Zonal kernels and rotation invariance

A kernel on $S^{d-1}$ is *zonal* if it depends only on the inner product:
$K(u, u') = f(\langle u, u'\rangle)$.  Since $\langle Qu, Qu'\rangle = \langle u, u'\rangle$
for any orthogonal $Q \in O(d)$:

$$K(Qu, Qu') = K(u, u') \quad \text{for all } Q \in O(d).$$

Let $(\rho(Q)g)(u) := g(Q^{-1}u)$ be the natural action of $O(d)$
on $L^2(S^{d-1})$.  Rotation invariance implies $T_K$ is an **intertwiner**:

$$T_K \circ \rho(Q) = \rho(Q) \circ T_K \quad \text{for all } Q \in O(d).$$

### 1.3 Schur's lemma forces spherical harmonics

By Schur's lemma, any intertwiner must preserve the irreducible invariant
subspaces of the group action.

> **What is an irreducible invariant subspace?**
>
> An $O(d)$-invariant subspace $V \subseteq L^2(S^{d-1})$ is a closed subspace
> closed under all rotations: $f \in V \implies f \circ Q^{-1} \in V$ for all $Q$.
>
> $V$ is *irreducible* if its only invariant subspaces are $\{0\}$ and $V$ itself.
>
> Since $T_K$ commutes with rotations and $V$ is irreducible, $T_K(V) \subseteq V$,
> so $T_K$ restricts to a linear map $V \to V$.

The irreducible $O(d)$-subspaces of $L^2(S^{d-1})$ are exactly the **spaces
of spherical harmonics of degree $\ell$**, denoted $\mathcal{H}_\ell^d$:
the homogeneous harmonic polynomials of degree $\ell$ restricted to the sphere.

**Why these are the right subspaces (Peter-Weyl):**

1. **Invariant.** Rotations preserve both polynomial degree and harmonicity
   ($\Delta$ commutes with rotations), so $\mathcal{H}_\ell^d$ is $O(d)$-invariant.
2. **Irreducible.** $\mathcal{H}_\ell^d$ is an eigenspace of $\Delta_{S^{d-1}}$
   with eigenvalue $-\ell(\ell+d-2)$.  An orbit argument shows no proper
   subspace is also invariant.
3. **Complete.** $L^2(S^{d-1}) = \bigoplus_\ell \mathcal{H}_\ell^d$ (Peter-Weyl).
4. **Unique.** Different $\ell$ give non-isomorphic representations (distinct
   Laplacian eigenvalues).

The dimensions are:

$$N(d, \ell) = \binom{\ell+d-1}{\ell} - \binom{\ell+d-3}{\ell-2}$$

with the convention $\binom{\ell+d-3}{\ell-2} = 0$ for $\ell = 0, 1$.

### 1.4 The eigenvalue is a scalar per degree

Since $T_K$ is an intertwiner and each $\mathcal{H}_\ell^d$ is irreducible,
Schur's lemma gives $T_K|_{\mathcal{H}_\ell^d} = \lambda_\ell I$.

> **Schur's lemma in detail.** Let $A: V \to V$ be an intertwiner on an
> irreducible representation.  Let $\lambda$ be any eigenvalue of $A$.
> Then $\ker(A - \lambda I)$ is a nonzero invariant subspace of $V$.
> By irreducibility, $\ker(A - \lambda I) = V$, so $A = \lambda I$.

Therefore:
- Every spherical harmonic of degree $\ell$ is an eigenfunction with
  eigenvalue $\lambda_\ell$.
- The multiplicity of $\lambda_\ell$ is $N(d, \ell)$.
- We need only one number $\lambda_\ell$ per degree, not one per basis function.

---

## 2. How eigenvalues are determined: the Funk-Hecke formula

The eigenvalue $\lambda_\ell$ equals the $\ell$-th Gegenbauer coefficient
of the kernel function, up to normalization.

### 2.1 The addition theorem

$$\sum_{m=1}^{N(d,\ell)} Y_{\ell m}(u)\, Y_{\ell m}(u') = \frac{N(d,\ell)}{|\mathbb{S}^{d-1}|}\, \frac{C_\ell^\nu(\langle u, u'\rangle)}{C_\ell^\nu(1)}$$

where $C_\ell^\nu$ are Gegenbauer polynomials.

### 2.2 The Funk-Hecke formula

For any zonal function $f(\langle u, v\rangle)$:

$$\int_{S^{d-1}} f(\langle u, v\rangle)\, Y_{\ell m}(v)\, d\sigma(v) = \mu_\ell \cdot Y_{\ell m}(u)$$

where:

$$\mu_\ell = \frac{|\mathbb{S}^{d-2}|}{C_\ell^\nu(1)} \int_{-1}^{1} f(t)\, C_\ell^\nu(t)\, (1-t^2)^{\nu-1/2}\, dt$$

So **the eigenvalue $\lambda_\ell$ is proportional to the $\ell$-th Gegenbauer
coefficient of the kernel function**.

> **What are Gegenbauer coefficients?**
>
> They are Fourier coefficients using Gegenbauer polynomials as the basis
> instead of complex exponentials.  The $C_\ell^\nu$ are orthogonal on
> $[-1,1]$ with weight $w_\nu(t) = (1-t^2)^{\nu-1/2}$:
>
> $$\int_{-1}^{1} C_\ell^\nu(t)\, C_m^\nu(t)\, (1-t^2)^{\nu-1/2}\, dt = \delta_{\ell m}\, h_\ell^\nu$$
>
> The weight $(1-t^2)^{\nu-1/2}$ is the spherical volume element in disguise:
> parameterize the sphere by $t = \langle u, e_1\rangle$ ("latitude"), and the
> induced measure on $[-1,1]$ is proportional to $(1-t^2)^{(d-3)/2}\,dt$.
>
> | Circle $S^1$ | Sphere $S^{d-1}$ |
> |---|---|
> | coordinate: $\theta \in [0, 2\pi)$ | coordinate: $t = \langle u, v\rangle \in [-1,1]$ |
> | basis: $e^{ik\theta}$ | basis: $C_\ell^\nu(t)$ |
> | translation-invariant kernel | zonal kernel |
> | eigenvalue = $k$-th Fourier coeff | eigenvalue = $\ell$-th Gegenbauer coeff |

---

## 3. Computing the eigenvalues for our kernel

Our angular kernel is $k_\text{ang}(u, u') = e^{-c} e^{c\langle u,u'\rangle}$
where $c = 2\beta\alpha^2$.  We need the Gegenbauer coefficients of $f(t) = e^{ct}$.

### 3.1 Gegenbauer polynomials

**Generating function:**

$$\frac{1}{(1 - 2xt + t^2)^\nu} = \sum_{\ell=0}^{\infty} C_\ell^\nu(x)\, t^\ell$$

**First few:**
$C_0^\nu(t) = 1$, $\quad C_1^\nu(t) = 2\nu t$, $\quad C_2^\nu(t) = 2\nu(\nu+1)t^2 - \nu$.

**Orthogonality:** $\int_{-1}^{1} C_\ell^\nu C_m^\nu\, (1-t^2)^{\nu-1/2}\, dt = \delta_{\ell m}\, h_\ell^\nu$
where $h_\ell^\nu = \frac{\pi\, 2^{1-2\nu}\, \Gamma(\ell+2\nu)}{\ell!\,(\ell+\nu)\,[\Gamma(\nu)]^2}$.

**Rodrigues formula:**

$$C_\ell^\nu(t) = \frac{(-1)^\ell}{2^\ell\,\ell!} \cdot \frac{\Gamma(\nu+\tfrac{1}{2})\,\Gamma(\ell+2\nu)}{\Gamma(2\nu)\,\Gamma(\ell+\nu+\tfrac{1}{2})} \cdot (1-t^2)^{1/2-\nu} \cdot \frac{d^\ell}{dt^\ell}\!\left[(1-t^2)^{\ell+\nu-1/2}\right]$$

> **Why does the Rodrigues formula exist?**  Every classical orthogonal
> polynomial family has one.  The pattern is $P_\ell(t) \propto w(t)^{-1}\frac{d^\ell}{dt^\ell}[w(t)\,p(t)^\ell]$.
> The function $g(t) = (1-t^2)^{\ell+\nu-1/2}$ vanishes to order $\geq \ell$
> at $t = \pm 1$.  Differentiating $\ell$ times produces a function with
> exactly $\ell$ sign changes — the defining property of a degree-$\ell$
> orthogonal polynomial.

**Goal:** Compute $I_\ell := \int_{-1}^{1} e^{ct}\, C_\ell^\nu(t)\, (1-t^2)^{\nu-1/2}\, dt.$

### 3.2 Step 1: Rodrigues + integration by parts

> **Strategy.** The Rodrigues formula gives
> $C_\ell^\nu(t)(1-t^2)^{\nu-1/2} = \text{const}\cdot g^{(\ell)}(t)$ where
> $g(t) = (1-t^2)^{\ell+\nu-1/2}$.  The weights cancel.  Then IBP moves
> the $\ell$ derivatives from $g$ onto $e^{ct}$, picking up a factor of $(-c)$
> each time.  Boundary terms vanish because $g$ has high-order zeros at $\pm 1$.

After substituting Rodrigues and performing $\ell$ integrations by parts
(all boundary terms vanish):

$$\boxed{I_\ell = \frac{c^\ell}{2^\ell\,\ell!} \cdot \frac{\Gamma(\nu+\frac{1}{2})\,\Gamma(\ell+2\nu)}{\Gamma(2\nu)\,\Gamma(\ell+\nu+\frac{1}{2})} \cdot J_{\ell+\nu}}$$

where $J_\mu := \int_{-1}^{1} e^{ct}\, (1-t^2)^{\mu-1/2}\, dt$ with $\mu = \ell + \nu$.

**What happened:** The Gegenbauer polynomial was absorbed into the
prefactor $c^\ell / 2^\ell$.  The integral $J_\mu$ has the same form for
all $\ell$ — only the exponent $\mu = \ell + \nu$ changes.

### 3.3 Step 2: The Poisson integral gives Bessel functions

> **Where do Bessel functions come from?** They are not introduced by choice.
> Expanding $e^{ct} = \sum_n (ct)^n/n!$ and integrating term by term: odd
> powers vanish by symmetry, even powers give Beta integrals, and the
> resulting series is *by definition* the modified Bessel function $I_\mu(c)$.

The **Poisson integral** for modified Bessel functions states: for $\text{Re}(\mu) > -1/2$,

$$\int_{-1}^{1} e^{ct}\, (1-t^2)^{\mu-1/2}\, dt = \frac{\sqrt{\pi}\,\Gamma(\mu+\frac{1}{2})}{(c/2)^\mu}\, I_\mu(c)$$

where $I_\mu(c) = \sum_{m=0}^{\infty} \frac{(c/2)^{2m+\mu}}{m!\,\Gamma(m+\mu+1)}$.

**Proof sketch:**

1. Expand $e^{ct}$ as a power series under the integral.
2. Odd terms vanish by symmetry.  Even terms give Beta integrals:
   $\int_{-1}^{1} t^{2m}(1-t^2)^{\mu-1/2}\,dt = B(m+\frac{1}{2},\, \mu+\frac{1}{2})$.
3. Apply the duplication formula $(2m)! = \frac{4^m m!\,\Gamma(m+\frac{1}{2})}{\sqrt{\pi}}$.
4. The resulting series matches the definition of $I_\mu(c)/(c/2)^\mu$.

$$\boxed{J_\mu = \frac{\sqrt{\pi}\,\Gamma(\mu+\frac{1}{2})}{(c/2)^\mu}\, I_\mu(c)}$$

### 3.4 Step 3: Assembly

Substituting $J_{\ell+\nu}$ into the expression for $I_\ell$:

**Key cancellation.** $\Gamma(\ell+\nu+\frac{1}{2})$ appears in the denominator
of step 1 and the numerator of step 2 — they cancel exactly.

**Power simplification.** $\frac{c^\ell}{2^\ell} \cdot \frac{2^{\ell+\nu}}{c^{\ell+\nu}} = \frac{2^\nu}{c^\nu}$ — independent of $\ell$.

After all cancellations:

$$I_\ell = \sqrt{\pi}\,\Gamma(\nu+\tfrac{1}{2}) \cdot \frac{\Gamma(\ell+2\nu)}{\Gamma(2\nu)\,\ell!} \cdot \frac{2^\nu}{c^\nu}\, I_{\ell+\nu}(c)$$

### 3.5 Step 4: From integral to Gegenbauer coefficient

Dividing by the squared norm $h_\ell^\nu$ and applying the Legendre duplication
formula $\Gamma(2\nu) = \frac{2^{2\nu-1}}{\sqrt{\pi}}\Gamma(\nu)\Gamma(\nu+\frac{1}{2})$:

$$b_\ell = \frac{I_\ell}{h_\ell^\nu} = \Gamma(\nu)\,(\ell+\nu)\,\left(\frac{2}{c}\right)^{\!\nu} I_{\ell+\nu}(c)$$

Reassembling:

$$\boxed{e^{ct} = \Gamma(\nu)\left(\frac{2}{c}\right)^{\!\nu}\sum_{\ell=0}^{\infty} (\ell+\nu)\, I_{\ell+\nu}(c)\, C_\ell^\nu(t)}$$

This is the classical Gegenbauer–Bessel expansion (Watson 1944, §11.5).

### 3.6 Step 5: The Mercer eigenvalue

Using the addition theorem to convert from Gegenbauer coefficients to
Mercer eigenvalues: $\lambda_\ell = b_\ell \cdot \nu/(\ell+\nu)$, and
$\nu\,\Gamma(\nu) = \Gamma(d/2)$:

$$\boxed{\lambda_\ell = e^{-c}\,\Gamma\!\left(\frac{d}{2}\right)\!\left(\frac{2}{c}\right)^{\!\frac{d-2}{2}} I_{\ell+\frac{d-2}{2}}(c), \qquad c = 2\beta\alpha^2}$$

---

## 4. The full wristband kernel decomposition

The wristband kernel $K(w,w') = k_\text{ang}(u,u') \cdot k_\text{rad}(t,t')$
decomposes as:

$$K\bigl((u,t),(u',t')\bigr) = \sum_{\ell=0}^{\infty} \sum_{k=0}^{\infty} \lambda_\ell\,\tilde{a}_k \sum_{m=1}^{N(d,\ell)} Y_{\ell,m}(u)\,Y_{\ell,m}(u') \cdot f_k(t)\,f_k(t')$$

| Symbol | Formula | Notes |
|--------|---------|-------|
| $\lambda_\ell$ | $e^{-c}\,\Gamma(d/2)\,(2/c)^\nu\,I_{\ell+\nu}(c)$ | angular eigenvalue |
| $\tilde{a}_0$ | $\sqrt{\pi/\beta}$ | radial constant-mode weight |
| $\tilde{a}_k$ ($k \geq 1$) | $2\sqrt{\pi/\beta}\,e^{-\pi^2 k^2/(4\beta)}$ | radial cosine-mode weight |
| $Y_{\ell,m}(u)$ | orthonormal spherical harmonics | $\ell=0$: $Y_{0,1}=1$; $\ell=1$: $Y_{1,m}=\sqrt{d}\,u_m$ |
| $f_k(t)$ | $1$ if $k=0$; $\cos(k\pi t)$ if $k\geq 1$ | radial eigenfunctions |

### 4.1 Spectral energy

$$\mathcal{E}(P) = \sum_{\ell=0}^{\infty}\sum_{k=0}^{\infty} \lambda_\ell\,\tilde{a}_k \sum_{m=1}^{N(d,\ell)} \bigl|\hat{c}_{\ell m,k}(P)\bigr|^2$$

where $\hat{c}_{\ell m,k}(P) = \mathbb{E}_{(u,t)\sim P}[Y_{\ell,m}(u)\,f_k(t)]$.

### 4.2 Eigenvalue qualitative properties

- **$\lambda_\ell \geq 0$ always** (Schoenberg's theorem).
- **Exponential decay**: $\lambda_\ell \to 0$ super-exponentially.
- **High-$d$ approximation**: $\lambda_1/\lambda_0 \approx c/d$ for $d \gg c$.

### 4.3 Diagonal verification

$k_\text{ang}(u,u) = 1$ requires $\sum_\ell \lambda_\ell N(d,\ell) = 1$.
From the addition theorem, this reduces to $f(1) = e^{-c}e^c = 1$. ✓

---

## 5. Supporting results

### 5.1 Schoenberg's theorem

**Theorem (Schoenberg, 1942).** A continuous $f : [-1,1] \to \mathbb{R}$
is positive definite on $S^{d-1}$ if and only if it has a Gegenbauer
expansion with non-negative coefficients:

$$f(t) = \sum_{\ell=0}^{\infty} b_\ell\, C_\ell^\nu(t), \qquad b_\ell \geq 0.$$

For our kernel: PSD is given (axiom), so $b_\ell \geq 0$, which is what makes
$\lambda_\ell \geq 0$ in the Mercer decomposition.

### 5.2 Mercer's pointwise convergence

For continuous PSD kernels on compact spaces, the $L^2$ eigendecomposition
strengthens to absolute and uniform convergence:

$$K(x, y) = \sum_{j=0}^{\infty} \lambda_j\, \varphi_j(x)\, \varphi_j(y) \quad \text{uniformly on } X \times X$$

Key consequences:
- Diagonal: $\sum_j \lambda_j \varphi_j(x)^2 = K(x,x)$.
- Trace: $\sum_j \lambda_j = \int_X K(x,x)\,d\mu(x)$.  For our kernel, $\sum_j \lambda_j = 1$.
- Absolute summability: $\sum_j \lambda_j |\varphi_j(x)\varphi_j(y)| < \infty$ (by Cauchy-Schwarz from the diagonal).

---

## References

1. Mercer, J. (1909). "Functions of positive and negative type." *Phil. Trans. R. Soc. London A* 209, 415–446.
2. Schoenberg, I.J. (1942). "Positive definite functions on spheres." *Duke Math. J.* 9(1), 96–108.
3. Watson, G.N. (1944). *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge. §§3.71, 11.5.
4. Szegő, G. (1975). *Orthogonal Polynomials*, 4th ed., AMS.
5. Dai, F. & Xu, Y. (2013). *Approximation Theory and Harmonic Analysis on Spheres and Balls*, Springer. Ch. 1.
6. Steinwart, I. & Christmann, A. (2008). *Support Vector Machines*, Springer. Thm 4.49.
7. NIST Digital Library of Mathematical Functions (DLMF): §§5.5, 10.25, 10.32, 18.3, 18.5.
