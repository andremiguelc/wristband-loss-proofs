# Poisson mode sampling: what it is, why it works, where it breaks

The Lean proofs are in `WristbandLossProofs/Poisson/`. [poisson_guide.md](poisson_guide.md)
maps this note to them, section by section. The scripts beside this file produce every number
below: `bessel_check.py`, `blind_check.py`, and the `fig_*.py` files that draw the figures.

This note is about the **angular** factor of the wristband kernel. Six exact cosine modes
handle the radial factor. They keep $99.999\%$ of the radial weight, so the radial factor is
not the problem.

---

## 0. Notation and terms

| symbol | meaning |
|---|---|
| $d$ | embedding dimension. $S^{d-1}=\{u\in\mathbb{R}^d:\lVert u\rVert=1\}$ is the unit sphere |
| $u,u'$ | two directions on $S^{d-1}$. $t:=u^\top u'\in[-1,1]$ is their cosine similarity |
| $s,s'$ | the *radial* coordinate of a wristband point, rescaled to $[0,1]$. Not the same as $t$ |
| $\beta,\alpha$ | kernel bandwidth and angular-radial balance (paper §3.1) |
| $c:=2\beta\alpha^2$ | the only parameter that the angular analysis uses |
| $\ell$ | *harmonic* degree. It indexes a spherical-harmonic subspace |
| $m$ | *monomial* degree, the exponent of $t$. **Not** the same as $\ell$ |
| $\mathcal{H}_\ell$ | the space of degree-$\ell$ spherical harmonics on $S^{d-1}$ |
| $N_\ell=\dim\mathcal{H}_\ell$ | its dimension, approximately $d^\ell/\ell!$. Also called the *multiplicity* |
| $Y_{\ell 1},\dots,Y_{\ell N_\ell}$ | an orthonormal basis of $\mathcal{H}_\ell$ |
| $\lambda_\ell$ | the Mercer eigenvalue of every element of $\mathcal{H}_\ell$ (paper Eq. 13) |
| $A_\ell := \lambda_\ell N_\ell$ | the total weight of degree $\ell$ |
| $p_m$ | the $m$-th Maclaurin coefficient of the kernel. It is a Poisson mass (§1) |
| $\rho_k(s)=\cos(k\pi s)$, $a_k$ | the radial modes and their weights |
| $P$, $\mu_0$ | a distribution on the sphere, and the uniform target |
| $\mathcal{E}(P)$ | kernel energy $\mathbb{E}_{u,u'\sim P}[k(u,u')]$ |
| $L$, $M$ | cutoffs. $L$ bounds the harmonic degree, $M$ bounds the monomial degree |
| $N$ | batch size. $D$ is the number of random features. $S$ is the number of shared projections |

Six radial modes means $k=0,\dots,5$. The Python code calls this `k_modes = 6`. The Lean
development writes the radial cutoff as $K=5$, which gives $K{+}1=6$ modes.

These terms occur below:

- **RKHS** is a reproducing-kernel Hilbert space. It is the space of functions that the
  kernel can represent.
- **PSD** means positive semi-definite.
- A kernel is **characteristic** if its mean embedding $P\mapsto\int k(\cdot,u)\,dP(u)$ is
  injective. Distinct distributions then get distinct embeddings.
- **SGD** is stochastic gradient descent.

Two configurations occur below. The **neural** configuration uses $\beta=8$ and
$\alpha^2=1/12$, so $c=4/3$. The **point-cloud** configuration uses $\beta=64$ and
$\alpha=0.8$, so $c=81.9$.

---

## 1. The forced patterns of the kernel, their cost, and why the weights are Poisson

The angular kernel (paper §3.1) is
$$k_{\mathrm{ang}}(u,u') \;=\; e^{-2\beta\alpha^2}\exp\bigl\{2\beta\alpha^2\,u^\top u'\bigr\}
\;=\; e^{-c}e^{c\,t},\qquad t=u^\top u',\quad c=2\beta\alpha^2 .$$

This section describes the same kernel twice. The first description is a catalogue of
patterns on the sphere. It is exact, symmetry forces it, and it is too expensive. The second
description is a power series in $t$. Its coefficients are a probability distribution, and
that gives the alternative.

### Why you can study the angular factor alone

The wristband kernel is a product of an angular score and a radial score (paper Eq. 3):
$$\mathcal{K}\bigl((u,s),(u',s')\bigr) \;=\; k_{\mathrm{ang}}(u,u')\;\times\;k_{\mathrm{rad}}(s,s').$$
No term mixes $u$ with $s'$. [Technical: $\mathcal{K}$ is a *tensor-product kernel* on
$S^{d-1}\times[0,1]$.]

Each factor expands into a weighted sum of simple patterns. The radial score becomes a sum of
cosine modes $\rho_k(s)=\cos(k\pi s)$ with weights $a_k$. A higher $k$ has a smaller weight.

The angular score becomes a sum over the harmonics of the sphere. These harmonics come in
**groups**. Group $\ell$ holds $N_\ell$ patterns $Y_{\ell 1},\dots,Y_{\ell N_\ell}$. All
patterns in the group have the same weight $\lambda_\ell$.

Group $0$ is the constant pattern. Group $1$ responds to the mean direction. Group $2$
responds to the axis of largest spread. The group sizes increase as
$N_\ell\approx d^\ell/\ell!$. At $d=128$, group $2$ already holds $8{,}255$ patterns.

Multiply the two expansions. The result is a sum over every pair of one angular pattern and
one radial mode. The weight of a pair is the product of the two weights:
$$\text{weight of the mode } (\ell,r,k) \;=\; \lambda_\ell \times a_k .$$

Collect each angular group into one row. This gives a multiplication table. Row $\ell$ has
total weight $A_\ell=\lambda_\ell N_\ell$, and column $k$ has weight $R_k$. The block at
$(\ell,k)$ has weight $A_\ell R_k$.

The figure shows that table at the neural configuration. The two grey bar charts show the row
weights and the column weights.

![mode table](fig_mode_grid.png)

*(Redraw with `fig_mode_grid.py`. The row weights use the large-$d$ Poisson form
$A_\ell=e^{-c}c^\ell/\ell!$ from below. The column weights are exact,
$R_k \propto 2e^{-\pi^2k^2/4\beta}$ for $k\ge1$.)*

[Technical: the joint eigenfunctions are the products $Y_{\ell r}\otimes\rho_k$, where
$(Y_{\ell r}\otimes\rho_k)(u,s) = Y_{\ell r}(u)\cdot\rho_k(s)$. The joint eigenvalues are
$\lambda_\ell a_k$. The tensor product of two orthonormal bases is an orthonormal basis of
$L^2$ on the product space, and $L^2(S^{d-1}\times[0,1]) \cong L^2(S^{d-1})\otimes
L^2([0,1])$, so the table loses nothing. This is `spectralEnergy` in the Lean development. Its
summand is `λv j * radialCoeff a0 a k * (modeProj j k P)^2`.]

#### The table makes the method linear in the batch size

The loss needs the mean similarity over all pairs in a batch of $N$ points. A direct
calculation needs about $N^2/2$ comparisons. At $N=4096$ that is $8.4$ million.

Every cell of the table has one useful form. It is a quantity at point $i$, multiplied by the
same quantity at point $j$. For that form, the square of a sum lists every pair:
$$(x_1+x_2+x_3)^2 \;=\; x_1^2+x_2^2+x_3^2 \;+\; 2x_1x_2+2x_1x_3+2x_2x_3 .$$
The right side lists the pairs. The left side needs one sum and one squaring operation.

So evaluate the pattern of each cell once at each of the $N$ points. Add the values, then
square the result. The cost is $N$, not $N^2$:
$$\hat c_{(\ell r),k} \;=\; \frac1N\sum_{i=1}^{N} Y_{\ell r}(u_i)\,\rho_k(s_i),
\qquad \mathcal{E}(P)\;\approx\;\sum_{\ell,r,k}\lambda_\ell a_k\,\hat c_{(\ell r),k}^{\,2}.$$
The total cost is $N$ multiplied by the number of cells kept. The product structure gives this
result.

#### Cost and accuracy are both products, and the angular factor is the small one

The number of cells kept is the number of rows kept, multiplied by the number of columns kept.
Keep groups $\ell\le1$ and the six radial modes at $d=128$. This gives $129\times6=774$ cells.

The share of the total weight kept is also a product. It is the row share multiplied by the
column share. Read both values from the bar charts in the figure:

| side | what is kept | share of the weight of that side |
|---|---|---|
| radial (columns) | six cosine modes | $99.999\%$ |
| angular (rows) | groups $\ell\le1$ | $61.5\%$ |
| **combined** | the dashed box | $0.615\times0.99999 = \mathbf{61.5\%}$ |

The radial side gives a factor of $0.99999$. A factor of $1$ does not change the product. More
columns therefore keep the product at $61.5\%$. The missing $38.5\%$ is all in the rows. For
this reason, the rest of this note uses the angular factor alone.

*(Two values for the angular share occur in this note. Each use states which value it is. The
large-$d$ Poisson form $(1+c)e^{-c}$ gives $61.5\%$, and the row weights in the figure use
this form. The exact $d=128$ Bessel values are $A_0=0.2654$ and $A_1=0.3539$, which give
$61.9\%$. The difference is $O(1/d)$, for the reason below.)*

#### Checks on the split

The error bound splits without help. The Lean theorem `spectralEnergyTruncated_error_le`
bounds the truncation error by
$T_{\mathrm{ang}}(L)\cdot R_{\mathrm{tot}} + S_{\mathrm{ang}}(L)\cdot R_{\mathrm{tail}}(K)$.
The first term is for a dropped row. The second term is for a kept row with a dropped column.
The theorem gives this separation; nothing imposes it. (`spectralEnergyTruncatedByDegree_error_le_explicit`
is the closed-form version, indexed by degree, and `spectralTruncationClosedForm` bounds it.)

Unbiasedness passes through the product. Replace the rows with a random quantity that is
correct in expectation, and keep the columns exact. The product is then still correct in
expectation, because $\mathbb{E}[\hat k_{\mathrm{ang}}]=k_{\mathrm{ang}}$, and because
$k_{\mathrm{rad}}$ is deterministic and independent of the draw. Therefore
$\mathbb{E}[\hat k_{\mathrm{ang}}k_{\mathrm{rad}}]=\mathcal{K}$.

The defect also passes through the product. A finite rank for $k_{\mathrm{ang}}$ gives a
finite rank for $\mathcal{K}$. The mean embedding then has a non-trivial null space, so the
product inherits the blindness of §2, and more columns cannot correct it. If both factors are
universal, the product is characteristic. That is
`productKernel_universal_compact_imported`.

### The forced catalogue of patterns, and its cost

$$k_{\mathrm{ang}}(u,u') \;=\; \sum_{\ell\ge0}\lambda_\ell\sum_{r=1}^{N_\ell}Y_{\ell r}(u)\,Y_{\ell r}(u') .$$

A fixed catalogue of patterns rebuilds the angular score. The catalogue is not a choice. One
fact forces it: the score uses only the *angle* between two directions. The patterns come in
groups, and the patterns of group $\ell$ change sign $\ell$ times between the poles. One
number gives the whole difficulty: the number of patterns in a group at large $d$.

![harmonic groups](fig_groups.png)

*(Redraw with `fig_groups.py`. The group sizes $N_\ell$ are exact. The "carries" percentages
use the large-$d$ Poisson approximation at $c=4/3$.)*

#### A similarity score is a symmetric table, and symmetric tables split

Use $1000$ directions in place of the whole sphere. Then $k_{\mathrm{ang}}$ is a
$1000\times1000$ table, and the table is **symmetric**. The score of $(A,B)$ equals the score
of $(B,A)$, because the score uses only the angle, and an angle has no direction.

A symmetric table has a set of mutually perpendicular eigenvectors, and those eigenvectors
rebuild it:
$$A \;=\; \sum_i \lambda_i\, e_i e_i^\top, \qquad\text{entry by entry}\qquad A_{xy}=\sum_i \lambda_i\,e_i(x)\,e_i(y).$$
Take a pattern $e_i$, which is one number for each direction. Multiply its value at $x$ by its
value at $y$. Weight the product by $\lambda_i$, then sum over the patterns. The expansion at
the head of this subsection has the same form.

Now use every direction on the sphere in place of $1000$ directions. The structure does not
change. The sums become integrals, and the list of patterns can be infinite.
[Technical: $k_{\mathrm{ang}}$ defines a self-adjoint compact operator $T$ on
$L^2(S^{d-1},\sigma)$, where $(Tf)(u)=\int k_{\mathrm{ang}}(u,u')f(u')\,d\sigma(u')$. Mercer's
theorem is the spectral theorem in this setting.]

This step shows only that **some** catalogue works. It does not identify the catalogue.

#### Rotation invariance identifies the catalogue

Put $12$ points at equal spacing on a circle. Score two points by the difference of their
indices, so $(3,7)$ and $(9,1)$ both get the score $4$. In the $12\times12$ table, each row is
the row above it, moved along by one position.

Sines and cosines diagonalise a table of this kind. Also, the patterns **do not depend on the
values in the table**. If you change the score, the weights change, but the sines and cosines
do not change. The pattern of movement fixes them alone.

Here is the reason. A rotation by one position leaves the table unchanged. So if a pattern is
an eigenvector, its rotation is also an eigenvector with the same weight. Sines and cosines
are the only patterns that return to themselves under rotation, up to a scale factor.

The sphere gives the same situation. There, a rotation by one position becomes a rotation in
any direction. Rotations keep angles, because $(Ru)^\top(Ru')=u^\top u'$. Therefore
$k_{\mathrm{ang}}(Ru,Ru')=k_{\mathrm{ang}}(u,u')$ for every rotation $R$, and the same
reasoning identifies the catalogue.
[Technical: such a kernel is *zonal*. $T$ commutes with the rotation action
$(R\cdot f)(u)=f(R^{-1}u)$, and commuting operators share eigenspaces. The circle table is a
**circulant matrix**. Its eigenvectors are the Fourier modes for any first row.]

#### The forced patterns are harmonic polynomials, sorted by degree

List the polynomials in the coordinates $u_1,\dots,u_d$, and sort them by degree:

* **Group $0$** holds the constants. That is one pattern.
* **Group $1$** holds the coordinates, $u\mapsto u_1,\ \dots,\ u\mapsto u_d$. That is $d$
  patterns.
* **Group $2$** holds the quadratics $u_iu_j$, but not the part that a lower group covers. On
  the sphere, $u_1^2+\dots+u_d^2=1$. That combination is therefore the constant pattern of
  group $0$. Remove it, and group $2$ remains.

Group $2$ at $d=3$ is $xy$, $xz$, $yz$, $x^2-y^2$, and $x^2+y^2-2z^2$. That is five patterns.
The sixth combination, $x^2+y^2+z^2$, is absent, because it equals $1$ on the sphere.

The condition "remove the part that a lower group covers" has an exact form. The Laplacian
must kill the polynomial: $\Delta p=\sum_i\partial^2p/\partial x_i^2=0$. A function with
$\Delta p=0$ is **harmonic**. This gives the name of the expansion.
[Technical: $\mathcal{H}_\ell=\{p|_{S^{d-1}} : p$ homogeneous of degree $\ell,\ \Delta p=0\}$,
and $L^2(S^{d-1})=\bigoplus_{\ell\ge0}\mathcal{H}_\ell$.]

Each group has one member that uses only the angle to a fixed pole. That member changes sign
exactly $\ell$ times between the poles. On a circle the group is $\cos\ell\theta$ and
$\sin\ell\theta$. The left panel of the figure shows this. It deforms the radius by
$\cos\ell\theta$, which makes the sign changes visible.

#### Every pattern in a group has the same weight

Rotate the sphere under any pattern of group $2$. The result is another pattern of group $2$. A
rotated quadratic is a quadratic, and a rotation adds no lower-degree content.

The score does not respond to rotations. Assume that one member of a group has more weight than
another member. Then a rotation of the first member into the second member must change the
weight. But nothing changed. So **all members of a group have one weight** $\lambda_\ell$.
[Technical: $\mathcal{H}_\ell$ is *irreducible* under the rotation action, and Schur's lemma
gives $T|_{\mathcal{H}_\ell}=\lambda_\ell\cdot\mathrm{Id}$.]

Two results follow, and both are necessary below. First, the expansion has one number for each
group, not one number for each pattern, and $\lambda_\ell$ occurs $N_\ell$ times. Second, **you
keep a group whole or you drop it whole**. A rotation maps any member onto any other member, so
a selection of some members would break the rotation symmetry that identified the catalogue.

#### The weight is one integral in one variable

$$\lambda_\ell \;=\; \int_{-1}^{1} f(t)\,\underbrace{\frac{C_\ell^{\nu}(t)}{C_\ell^{\nu}(1)}}_{\text{the pattern}}\,\underbrace{w_d(t)}_{\text{sphere area}}\,dt ,
\qquad f(t)=e^{-c}e^{ct},\quad w_d(t)\propto(1-t^2)^{\frac{d-3}{2}},\quad \nu=\tfrac{d-2}{2}.$$

An integral over a $128$-dimensional sphere became an integral over one number
$t\in[-1,1]$. The symmetry gives that reduction.

![Funk–Hecke ingredients](fig_funkhecke.png)

*(Redraw with `fig_funkhecke.py`. `bessel_check.py` holds the numerical checks below.)*

**The source of the integral in one variable.** The answer is one number $\lambda_\ell$ for the
whole group, so one convenient member is sufficient. Take the member that uses only the angle
to a chosen pole $v$, and call it $Z_\ell(t)$ with $t=u^\top v$. Average the score against it,
then evaluate at the pole, where $u=v$:
$$\lambda_\ell\, Z_\ell(1) \;=\; \int_{S^{d-1}} k_{\mathrm{ang}}(v^\top u')\,Z_\ell(v^\top u')\,d\sigma(u') .$$
Both factors in that integral use $u'$ only through $t=v^\top u'$. So sweep over $t$ in place of
the sphere, and weight each value of $t$ by the sphere area at that value. Divide by
$Z_\ell(1)$, and the displayed formula remains. [Technical: this is the Funk–Hecke theorem,
$\int f(u^\top u')Y_\ell(u')\,d\sigma(u')=\lambda_\ell Y_\ell(u)$ for every
$Y_\ell\in\mathcal{H}_\ell$.]

**The source of the weight $(1-t^2)^{(d-3)/2}$.** Cut the sphere at angle $t$ from the pole.
The slice is a sphere of one dimension less, with radius $\sqrt{1-t^2}$. Area increases as the
radius to the power of the dimension of the slice, which is $d-2$. So the area of the slice is
proportional to
$$\bigl(\sqrt{1-t^2}\bigr)^{d-2}=(1-t^2)^{\frac{d-2}{2}} .$$
The slices have equal spacing in *angle*, not in $t$. Put $t=\cos\theta$. Then
$dt=-\sin\theta\,d\theta=-\sqrt{1-t^2}\,d\theta$, so $d\theta=dt/\sqrt{1-t^2}$. Multiply the
two factors:
$$w_d(t)\;\propto\;(1-t^2)^{\frac{d-2}{2}}\cdot(1-t^2)^{-\frac12}\;=\;(1-t^2)^{\frac{d-3}{2}} .$$
The exponent is the area of a slice. It is not a convention.

The right panel shows this weight. As $d$ increases, the weight concentrates at $t=0$. At
$d=128$, $97.7\%$ of the sphere is within $|t|<0.2$ of any pole. Two random directions in $128$
dimensions are almost always close to perpendicular. This fact makes $d$ cancel below.

**What a Gegenbauer polynomial is.** On the circle, the pattern that changes sign $\ell$ times
is $\cos\ell\theta$. Write it in terms of $t=\cos\theta$, and it becomes a polynomial:
$$\cos 0\theta=1,\qquad \cos1\theta=t,\qquad \cos2\theta=2t^2-1,\qquad \cos3\theta=4t^3-3t .$$
The double-angle and triple-angle formulas give the third and fourth values. These polynomials
are the **Chebyshev** polynomials.

$C_\ell^\nu$ is the same object for a $d$-dimensional sphere. Two properties define it.
Orthogonality forces it: different groups are orthogonal, and for their zonal members that
condition is $\int_{-1}^1 Z_\ell Z_{\ell'}\,w_d\,dt=0$ for $\ell\ne\ell'$. Only one sequence of
polynomials, one for each degree, satisfies that condition under a given weight. Also,
$C_\ell^\nu$ crosses zero exactly $\ell$ times on $(-1,1)$. The left panel shows this, and it
makes the statement "group $\ell$ changes sign $\ell$ times" exact.

At $d=3$, $\nu=\tfrac12$, and these polynomials are the **Legendre** polynomials. The left
panel draws them. The circle gives the Chebyshev polynomials at the other limit. Other
dimensions lie between the two.

The division by $C_\ell^\nu(1)$ rescales the pattern to the value $1$ at the pole, like
$\cos\ell\theta$ at $\theta=0$.
[Technical: these are the Gegenbauer (ultraspherical) polynomials. They are orthogonal on
$[-1,1]$ with weight $(1-t^2)^{\nu-1/2}$, and $\nu-\tfrac12=\tfrac{d-3}{2}$. $C_\ell^{1/2}$
gives Legendre, and $\lim_{\nu\to0}C_\ell^\nu/\nu=(2/\ell)T_\ell$ gives Chebyshev. The
addition theorem links back to the full group:
$\sum_r Y_{\ell r}(u)Y_{\ell r}(u')=(N_\ell/|S^{d-1}|)\,C_\ell^\nu(t)/C_\ell^\nu(1)$. It is
`mercerEigenfun_addition_theorem` in the development.]

**The source of the modified Bessel functions.** On the circle, $\lambda_n$ is the $n$-th
Fourier coefficient of the score:
$$\lambda_n \;=\; \frac1\pi\int_0^\pi e^{-c}e^{c\cos\theta}\cos(n\theta)\,d\theta .$$
The definition of the modified Bessel function of the first kind, at integer order $n$, is
$$I_n(c) \;:=\; \frac1\pi\int_0^\pi e^{c\cos\theta}\cos(n\theta)\,d\theta .$$
These are the same integral, so $\lambda_n=e^{-c}I_n(c)$. This step renames the quantity; it
does not derive it. Bessel functions occur here for one reason. They are the standard name for
the Fourier coefficients of $e$ to the power of a cosine, and the angular score has exactly
that form. Any kernel of the form $\exp(\text{constant}\times\cos)$ gives them.
(`bessel_check.py` checks this to 10 digits at $c=4/3$.)

In $d$ dimensions, only the *order* changes. It moves from $n$ to $\nu+\ell$, so the dimension
selects a position in the Bessel family:
$$e^{ct} \;=\; \Gamma(\nu)\Bigl(\tfrac{2}{c}\Bigr)^{\!\nu}\sum_{\ell\ge0}(\nu+\ell)\,I_{\nu+\ell}(c)\,C_\ell^\nu(t).$$

Read off the $\ell$-th coefficient. This gives the total weight of the group in closed form:
$$\boxed{\;A_\ell \;=\; \lambda_\ell N_\ell \;=\; e^{-c}\,\Gamma(\nu)\Bigl(\tfrac{2}{c}\Bigr)^{\!\nu}(\nu+\ell)\,I_{\nu+\ell}(c)\,C_\ell^\nu(1)\;}$$
This is Eq. (13). It is **exact**, and it sums to $1$ without a normalisation. To see this, put
$t=1$ in the expansion and multiply by $e^{-c}$, which gives $k_{\mathrm{ang}}(u,u)=1$ again.
Direct quadrature of the Funk–Hecke integral agrees with it to about $10^{-13}$ at $d=8,32,128$.

The dimension occurs twice in that formula: in the Bessel order $\nu+\ell$, and in
$C_\ell^\nu(1)$. At large $\nu$ the two nearly cancel. Keep only the leading term of the Bessel
series, $I_\mu(c)\approx(c/2)^\mu/\Gamma(\mu+1)$. This gives
$$\frac{I_{\nu+\ell}(c)}{I_\nu(c)}\;\approx\;\frac{(c/2)^\ell}{(\nu+1)\cdots(\nu+\ell)}\;\approx\;\Bigl(\frac{c}{d}\Bigr)^{\!\ell}.$$
At $d=128$ and $\ell=2$ the true value is $1.0682\times10^{-4}$, against $1.0684\times10^{-4}$.

Multiply by $N_\ell\approx d^\ell/\ell!$. Every power of $d$ cancels, and $e^{-c}c^\ell/\ell!$
remains, which is a Poisson probability. The power series below reaches the same result without
Bessel functions, and it shows the reason.

#### The cost

On a circle, group $\ell$ holds at most $2$ patterns. At $d=3$ it holds $2\ell+1$. At $d=128$
the right panel of the figure above gives
$$N_0=1,\quad N_1=128,\quad N_2=8\,255,\quad N_3=357\,632,\quad N_4=11\,708\,384,$$
which increases as $N_\ell\approx d^\ell/\ell!$. You must keep a group whole or drop it whole.
So the $23\%$ of the kernel in group $2$ costs $8\,255$ patterns, and the $10\%$ in group $3$
costs $357\,632$ patterns. Truncation at $\ell\le L$ costs
$N_{\le L}=\sum_{\ell\le L}N_\ell\sim d^L$ patterns, not $L$.

The paper truncates this expansion at $\ell\le1$. That keeps the constant and the $d$
coordinate patterns, which is $129$ patterns, and they carry $61.9\%$ of the weight at $d=128$
exactly. The dropped groups hold everything that the score knows beyond the mean direction of
the cloud. §2 makes this exact.

So the catalogue is exact, symmetry forces it, and it is too expensive above group $2$.

### The same kernel as a power series

#### The Maclaurin expansion

Read the score as a function of one variable, $k_{\mathrm{ang}} = e^{-c}e^{ct}$ for
$t\in[-1,1]$. Expand the exponential about $0$:
$$k_{\mathrm{ang}}(u,u') \;=\; e^{-c}\sum_{m\ge0}\frac{(ct)^m}{m!}\;=\;\sum_{m\ge0}p_m\,t^m,
\qquad p_m \;=\; e^{-c}\frac{c^m}{m!} .$$
[Technical: a Taylor series about $0$ is a *Maclaurin* series. In Lean this is
`kernelAngChordal_maclaurinExpansion`.]

Two things differ from the catalogue. First, the building blocks are now powers of $t$, and
nothing in the expansion uses $d$. Second, **the unit of truncation is one number**. To drop
the $m=3$ term, drop the number $p_3$. To drop group $3$, do not store $357\,632$ functions.
The kernel is the same, but the two prices are not comparable.

The exponent $m$ is **not** the group number $\ell$. The two are closely related, as below, but
$m$ counts a power of a cosine, and $\ell$ names a group of patterns on a sphere.

#### The coefficients are a Poisson distribution

Add the coefficients:
$$\sum_{m\ge0}p_m \;=\; e^{-c}\sum_{m\ge0}\frac{c^m}{m!}\;=\;e^{-c}e^{c}\;=\;1 .$$
They are non-negative, and they sum to one. So they are the **Poisson distribution with mean
$c$**. In Lean this is `poissonWeight_tsum_eq_one`.

This is not a coincidence, for two reasons.

First, the Poisson probabilities *are* the exponential series. The definition
$\Pr[\mathrm{Poisson}(c)=m]=e^{-c}c^m/m!$ is the $m$-th term of $e^c$, divided by $e^c$. An
expansion of an exponential in powers of $t$ can give nothing else.

Second, the condition $k(u,u)=1$ forces the normalisation. Put $u'=u$, so $t=1$. Then
$k_{\mathrm{ang}}(u,u)=e^{-c}e^{c}=1$, and that substitution is the statement $\sum_m p_m=1$.
A normalisation of the kernel on the diagonal is a normalisation of a distribution.

[Technical: more generally, $k(t)/k(1)$ with all Maclaurin coefficients $\ge0$ is a *probability
generating function*. This one is the Poisson function, $G(z)=e^{c(z-1)}$. The same generating
function occurs in the variance calculation of §4, which is why the variance has a closed
form.]

Write the expansion as an average:
$$k_{\mathrm{ang}}(u,u') \;=\; \mathbb{E}_{m\sim\mathrm{Poisson}(c)}\bigl[(u^\top u')^m\bigr].$$
Draw a whole number $m$. Measure the alignment of the two directions. Raise the alignment to
the power $m$. The score is the mean result.

The exponent controls how much the score decreases with misalignment. $u^\top u'$ is a cosine
in $[-1,1]$, so a power only makes it smaller, and a higher power makes it much smaller:

| alignment $t$ | $m=0$ | $m=1$ | $m=4$ | $m=10$ |
|---|---|---|---|---|
| $0.9$ (almost parallel) | $1$ | $0.90$ | $0.66$ | $0.35$ |
| $0.5$ (a wide angle) | $1$ | $0.50$ | $0.063$ | $0.001$ |

At $m=0$ every pair gets the score $1$, which is no test. At $m=1$ the score is the cosine. At
$m=10$ only almost parallel directions get a large score. So $m$ sets how much alignment the
score demands. The Poisson distribution sets how often the kernel uses each exponent, and its
mean is $c=2\beta\alpha^2$:

> $c$ is the mean exponent of the alignment test.

A larger $\beta$ gives a larger mean exponent. A truncation that holds only the two smallest
exponents therefore becomes worse as $\beta$ increases. This is why the point-cloud
configuration at $c=81.9$ is useless for that truncation, and the neural configuration at
$c=4/3$ is only poor.

#### Both expansions agree, and this is where $d$ cancels

Two expansions of the same object must agree. That condition gives the Poisson law for the
group weights.

**The groups that a power $t^m$ uses.** $t^m$ is a polynomial of degree $m$ in the coordinates
of $u$. The forced catalogue can therefore express it. It uses the groups
$$\ell \;=\; m,\ m-2,\ m-4,\ \dots$$
and no others. Here is the reason. $t^m$ starts at degree $m$. The only way to make a piece of
lower degree is to pair two coordinate indices and collapse the pair with
$u_1^2+\dots+u_d^2=1$. Each collapse costs exactly two degrees.

**Almost all the weight stays at $\ell=m$.** A collapse sums one index over all $d$ of its
values, and holds the other indices fixed. That average divides the remaining weight by about
$d$. So the pieces of lower degree are smaller by $1/d$, then by $1/d^2$. At high dimension
they are negligible.

At the large-$d$ limit, the power $t^m$ therefore lies entirely in group $m$. The total weight
of group $\ell$ is then the coefficient of $t^\ell$:
$$A_\ell \;=\; \lambda_\ell N_\ell \;\longrightarrow\; p_\ell \;=\; e^{-c}\frac{c^\ell}{\ell!} .$$
The Poisson law of the group weights *is* the list of power-series coefficients.

![the d-cancellation](fig_cancel.png)

*(Redraw with `fig_cancel.py`. $N_\ell$ is exact, and $A_\ell$ uses the exact Bessel formula
above. The dashed curve is the Poisson limit.)*

So $A_\ell$ does not use $d$. But the group holds $N_\ell\approx d^\ell/\ell!$ patterns, so
each pattern has only
$$\lambda_\ell \;=\; \frac{A_\ell}{N_\ell}\;\approx\;e^{-c}\Bigl(\frac{c}{d}\Bigr)^{\!\ell}.$$
Two quantities change in opposite directions at matching rates. The left and middle panels show
them, and the right panel shows their product.

They cancel for this reason. The weight at exponent $\ell$ is a property of the profile in one
variable, $f(t)=e^{-c}e^{ct}$, and that function does not use $d$. The dimension sets only how
thinly the fixed weight spreads across the patterns. This is also why the Bessel formula gives
a Poisson probability. It calculates the same quantity by a longer route.

The error agrees with the $1/d$ argument for each collapse. The largest difference between the
exact $A_\ell$ and the Poisson value is

| $d$ | $8$ | $32$ | $128$ | $512$ |
|---|---|---|---|---|
| max $\lvert A_\ell - \Pr[\mathrm{Poisson}(c)=\ell]\rvert$ | $3.2\times10^{-2}$ | $9.3\times10^{-3}$ | $2.4\times10^{-3}$ | $6.1\times10^{-4}$ |

The difference falls to a quarter each time $d$ increases by a factor of four. That is an
$O(1/d)$ error. (`bessel_check.py` and `fig_cancel.py` calculate this. The closed form is
exact, and the Poisson form is its large-$d$ limit.)

#### A distribution is cheap to sample, but expensive to truncate

| | the catalogue | the power series |
|---|---|---|
| unit of truncation | a whole group of $N_\ell\sim d^\ell$ functions | one number $p_m$ |
| cost to keep exponent $\ell$ | store and evaluate $N_\ell$ patterns | no storage |
| type of the weights | eigenvalues | **a probability distribution** |
| effect of a drop | removes those patterns permanently, which is a bias (§2) | — |

The first column shows why the paper stops at $\ell\le1$. The second column gives more than a
short list of numbers. It gives a *probability distribution*, and it shows that the kernel is
an **average** over that distribution.

One standard method deals with an average that is too expensive to calculate. **Draw from the
distribution, then average the draws.** One draw of $m$ costs one random integer. It does not
cost $d^m$ of anything.

> Sample the exponent. Do not truncate it.

The factor $d^\ell$ is the price of an orthonormal basis of $\mathcal{H}_\ell$. The kernel
needs only the zonal function $t\mapsto t^m$, which is one scalar function of one variable at
every $d$. The problem here is a problem of **representation**, not of information.

---

## 2. Why $\ell\le L$ is blind

The paper keeps only groups $0$ and $1$, because a whole group is too expensive. The cost is
not an approximation error. It is a permanent inability to see certain shapes.

### The $\ell\le1$ score is a straight line

Groups $0$ and $1$ give two terms of the expansion. Group $0$ is the constant. The $d$ patterns
of group $1$ collapse into one dot product, because every pattern in a group has the same
weight. What remains is
$$k_{\le1}(u,u') \;=\; A_0 \;+\; A_1\,t,\qquad t=u^\top u',$$
with $A_0=0.2654$ and $A_1=0.3539$ at $d=128$ and $c=4/3$. (`blind_check.py` gives these exact
values.)

So the truncation replaces the curve $e^{-c}e^{ct}$ with **a straight line in $t$**. At $t=1$
the true score is $1$, and the line gives $0.619$. At $t=-1$ the true score is $e^{-2c}=0.069$,
and the line gives $-0.088$. That is a negative similarity, and the true score never gives one.
The line is still a valid kernel, because a drop of Mercer terms cannot break that property.
But it is no longer a similarity in the usual sense.

### The whole loss uses one number

Put that straight line into the energy. The energy averages the score over two independent
points:
$$\mathcal{E}_{\le1}(P)\;=\;\mathbb{E}_{u,u'\sim P}\bigl[A_0+A_1\,u^\top u'\bigr]
\;=\;A_0+A_1\sum_i \mu_i\mu_i \;=\; A_0+A_1\lVert\mu\rVert^2 ,$$
where $\mu=\mathbb{E}_{u\sim P}[u]$ is the mean of the unit vectors that point at the points.
The middle step holds because $u$ and $u'$ are independent, so the mean of $u_iu'_i$ is
$\mu_i^2$.

That is the whole content of the $\ell\le1$ loss:

> It measures the length of the mean vector, and nothing else.

To minimise it, make the vectors cancel. Every arrangement whose vectors cancel gets exactly
the score $A_0$. The uniform target also gets $A_0$, because its vectors cancel. So the loss
reports the same number for the target and for every arrangement with zero mean, and the
difference between them is exactly $0$.

![what the l<=1 loss cannot see](fig_blind.png)

*(Redraw with `fig_blind.py`. `blind_check.py` also prints the numbers. All four arrangements
lie in one $2$-plane of $\mathbb{R}^{128}$, so an exact calculation gives both the reported
energies and the true energies. $A_0=0.2654$ **is** the true energy of the target, because
$\lambda_0$ is the mean of the kernel over uniform pairs by construction.)*

The true energies of those four arrangements are between $0.394$ and $0.535$. The target gives
$0.265$. The antipodal pair differs from the target by more than the whole energy of the
target. The $\ell\le1$ loss reports $0.265$ for all four.

### There is also no gradient

The loss is $A_0+A_1\lVert\mu\rVert^2$. As a function of $\mu$, that is a bowl with its lowest
point at $\mu=0$. At the lowest point of a bowl, the slope is zero in every direction. So the
loss does not only give an antipodal pair the same score as the target. It also applies no
force towards the target.

### The same result holds at any $L$

Nothing above needs $L=1$. Groups up to $L$ make the loss a function of the first few summary
statistics of the arrangement. Those are the mean vector, then its spread and orientation, then
the next layer. There are finitely many of them at any $L$. Two arrangements that agree on all
of them are the same arrangement to the loss. Infinitely many such pairs always exist, because
a finite list of numbers cannot hold an infinite-dimensional object without collisions.

[Technical: $k_{\le L}$ has finite rank $N_{\le L}$, so its RKHS is the finite-dimensional
$\bigoplus_{\ell\le L}\mathcal{H}_\ell$. The mean embedding
$P\mapsto\bigl(\int Y_{\ell r}\,dP\bigr)_{\ell\le L,\,r\le N_\ell}\in\mathbb{R}^{N_{\le L}}$ is
a linear map out of an infinite-dimensional space of measures, so it has a non-trivial null
space. $\mathcal{E}_{\le L}$ uses $P$ only through that vector. So every $P$ in the fibre of
$\mu_0$ satisfies $\mathcal{E}_{\le L}(P)=\mathcal{E}_{\le L}(\mu_0)$ and
$\nabla\mathcal{E}_{\le L}(P)=0$. Equivalently, a finite-rank kernel is never
*characteristic*.]

### This is a bias, not noise

Noise decreases when you collect more data. The defect above does not decrease with the batch
size $N$, with the number of batches, or with the training time. Run the loss for a million
steps on infinite data, and the antipodal pair is still at a global minimum. No inequality can
become tighter and remove it, because there is no inequality. The two energies are *equal*.

### The size of the discarded part

At $\ell\le1$, the loss can run only the two smallest alignment tests. Those are "score
everything $1$" and "use the cosine". The distribution of the kernel sets how often it needs
each exponent. The fraction that the loss can still reach is
$$p_0+p_1 \;=\; (1+c)\,e^{-c},$$
and it loses the rest.

At the neural configuration $c=4/3$, that keeps $61.5\%$ and discards $38.5\%$ in the large-$d$
Poisson form. The exact $d=128$ value from the Bessel formula is $A_0+A_1=61.9\%$ kept. The two
values differ by $O(1/d)$.

At the point-cloud configuration $c=81.9$, the kernel needs an exponent near $82$ almost
always, and $(1+c)e^{-c}\approx2\times10^{-34}$. The truncated loss then measures nothing.

---

## 3. The construction: sample the exponent, do not truncate it

### You can sample an average

The score is
$$k_{\mathrm{ang}}(u,u')\;=\;\mathbb{E}_{m\sim\mathrm{Poisson}(c)}\bigl[(u^\top u')^m\bigr].$$
Draw an exponent $m$, apply that test, then average the results. Truncation keeps some terms of
this average, and discards the rest. This is why the defect of §2 is permanent: the loss
discards the same terms at every step.

Sampling treats the same average differently. Draw from the distribution, then average the
draws. One draw costs one random integer, not $d^{\,m}$ of anything.

### At a fixed exponent, sign vectors give the answer without a basis

Start at $m=1$. Let $w$ be a vector of $d$ independent signs. Each sign is $+1$ or $-1$ with
probability $1/2$. Then
$$(w^\top u)(w^\top u')\;=\;\Bigl(\sum_i w_iu_i\Bigr)\Bigl(\sum_j w_ju'_j\Bigr)
\;=\;\sum_{i,j} w_iw_j\,u_iu'_j .$$

Average each term. If $i\ne j$, the signs $w_i$ and $w_j$ are independent, and each one
averages to $0$. That term therefore vanishes. If $i=j$, then $w_i^2=1$ for either sign, so
that term remains with the weight $u_iu'_i$. What remains is $\sum_i u_iu'_i=u^\top u'$:
$$\mathbb{E}\bigl[(w^\top u)(w^\top u')\bigr]\;=\;u^\top u'\;=\;t .$$

Two random numbers give a product that is correct in expectation. Compare this with the
square-of-a-sum identity in §1. There, a square of a sum made every cross term. Here, the signs
remove every cross term and keep the diagonal.

[Technical: $w$ is a *Rademacher* vector, and the calculation is
$\mathbb{E}[w_iw_j]=\delta_{ij}$. In Lean, see `RademacherDraw` and
`randomMaclaurinFeature`.]

### For exponent $m$, take $m$ independent vectors and multiply

Take $m$ independent sign vectors $w_1,\dots,w_m$, and build one number for each point:
$$\psi(u)\;:=\;\prod_{i=1}^m (w_i^\top u).$$
The $w_i$ are independent, so the mean of the product is the product of the means. The previous
step then applies to each factor:
$$\mathbb{E}_w\bigl[\psi(u)\,\psi(u')\bigr]
\;=\;\prod_{i=1}^m\mathbb{E}\bigl[(w_i^\top u)(w_i^\top u')\bigr]\;=\;t^m .$$

### The two steps together

Draw $m\sim\mathrm{Poisson}(c)$. Draw $w_1,\dots,w_m$. Set
$\psi(u)=\prod_{i=1}^m(w_i^\top u)$. Average over $w$ first, then over $m$:
$$\boxed{\;\mathbb{E}_{m,w}\bigl[\psi(u)\psi(u')\bigr]\;=\;\mathbb{E}_m\bigl[t^m\bigr]\;=\;k_{\mathrm{ang}}(u,u')
\quad\text{exactly, at every exponent.}\;}$$
Not only up to $\ell\le L$. Every exponent. The method drops nothing, because it enumerates
nothing.

In Lean this is `poissonAngularSampler_unbiased`. `sampledEnergy_eq_kernelEnergy` carries it to
the energy. The sampled kernel is not an approximation of the wristband kernel. It *is* the
wristband kernel at every pair of points. So `sampledEnergy_minimizer_unique` follows by a
rewrite.

[Technical: this is the **random Maclaurin** construction (Kar & Karnick, *Random Feature Maps
for Dot Product Kernels*, AISTATS 2012). It applies to any $f(u^\top u')$ whose Maclaurin
coefficients are all $\ge0$. This kernel has $p_m>0$ for every $m$, so it satisfies the
hypothesis strictly.]

**The kernel is PSD without a further condition.** $t^m=\langle u^{\otimes m},u'^{\otimes
m}\rangle$ is the $m$-fold tensor power. It is an inner product, so it is a PSD kernel for
every $m\ge0$, and $p_m>0$. Every partial sum is therefore a valid kernel, and the estimator is
an explicit inner product of features.

### What changes

![truncation leaves a hole, sampling leaves noise](fig_sample.png)

*(Redraw with `fig_sample.py`, which prints every number below. Right panel: $600$ independent
draws at each $D$. The true value is exact, and the $\ell\le1$ value uses the exact $A_0,A_1$.)*

The left half shows the structural difference. Truncation uses the same two exponents at every
step, so a shape in the red region stays invisible at every step. Sampling draws the exponents
again at each step. No exponent has probability zero, so some draw sees every deviation.

The right half gives a number, for a well-aligned pair at $t=0.8$. A batch that collapses holds
many pairs of this kind. The true score is $0.766$. The $\ell\le1$ loss reports $0.549$, and it
reports $0.549$ at every future step. Sampling centres on $0.766$ from the first draw. Its
spread depends on the position of the pair:

| pair at $t=0.8$, $c=4/3$, $d=128$ | s.d. of one feature | crosses the truncation error at |
|---|---|---|
| axis-aligned ($u=e_1$, $u'$ in the $e_1e_2$ plane) | $0.643/\sqrt{D}$ | $D\approx9$ |
| general position | $2.17/\sqrt{D}$ | $D\approx100$ |

The axis-aligned case is the best case. There the second-moment factor
$\gamma=1+2t^2-2\sum_iu_i^2u_i'^2$ equals $1$ exactly, so the variance of one feature is
$1-k(u,u')^2$. In general position at the same $t$, $\gamma\approx2.25$, and the variance is
$e^{c(\gamma-1)}-k^2\approx4.71$. That is $3.4$ times more noise. Quote the general-position
number, unless you mean the axis-aligned case.

The exchange is a fixed error that you cannot reduce, against a random error that decreases as
you draw more features.

### Cost

Calculate $Wu$ once for each point, for $S$ shared sign vectors. That costs $O(NSd)$. After
that, each feature is a product of $m$ *entries* of a vector that already exists. That costs
$O(m)$, not $O(md)$, and $\mathbb{E}[m]=c$.

The total for the angular factor is
$O\!\left(N(Sd + Dc)\right)$. It is linear in $N$, it is linear in $d$, and the feature budget
$D$ does not use $d$. For comparison, one more angular group costs $8\,255$ functions at
$d=128$.

### The joint kernel: the radial side does not change

No spherical harmonic occurs in the construction above. It draws a whole number, draws sign
vectors, then multiplies dot products. The sphere enters only through $t=u^\top u'$. The
harmonics gave the diagnosis, not the correction. The cost of §1 and the blindness of §2 are
both statements about groups, and both describe the old method. The boxed identity above gives
the correctness of the estimator, and its proof mentions no harmonic.
[Technical: the construction needs only that $k_{\mathrm{ang}}=f(u^\top u')$ with all Maclaurin
coefficients of $f$ non-negative. Such a kernel is a *dot-product kernel*. This section uses no
Mercer theory, no Funk–Hecke theorem, and no addition theorem.]

The radial side needs no correction, for a structural reason. The angular side is expensive
because group $\ell$ holds $N_\ell\approx d^\ell/\ell!$ patterns with one shared weight, so you
cannot buy part of a group. The radial coordinate is one number, so its group $k$ holds exactly
one pattern, the mode $\rho_k(s)=\cos(k\pi s)$. There is no multiplicity, so nothing increases
with $d$. The radial side therefore keeps its six cosine modes and their weights $a_k$, which
hold $99.999\%$ of the radial weight.

Now put the two halves together. The angular half gives $D$ random features, with
$\frac1D\sum_j \psi_j(u)\psi_j(u')\approx k_{\mathrm{ang}}(u,u')$. The radial half gives six
cosines, with $\sum_k a_k\rho_k(s)\rho_k(s')\approx k_{\mathrm{rad}}(s,s')$. Their product is
$$\widehat{\mathcal{K}}\bigl((u,s),(u',s')\bigr)
\;=\;\sum_{j,k}\Phi_{jk}(u,s)\,\Phi_{jk}(u',s'),
\qquad \Phi_{jk}(u,s)=\sqrt{\tfrac{a_k}{D}}\;\psi_j(u)\,\rho_k(s).$$

That is the table of §1 again, with one cell for each random angular feature and cosine mode.
The cell has the same form as before, so the square-of-a-sum identity applies without a change:
$$\widehat{\mathcal{E}}(P)\;=\;\sum_{j,k}\Bigl(\frac1N\sum_{i=1}^N \Phi_{jk}(u_i,s_i)\Bigr)^{\!2}.$$
Each cell needs one pass over the batch, so the cost is $N\times 6D$, for example
$4096\times384\times6$. No sum over pairs remains. (In Lean: `kernelEnergy_featureForm`.)

Note the source of the linearity in $N$. It is the product structure of the features, which
does not change. Only the method that builds one of the two lists changes.

The six radial cosines are still a cut, so the argument of §2 also applies to them. Two
arrangements that differ only in radial modes $k\ge6$ are exactly indistinguishable, in value
and in gradient. The difference is one of proportion, not of type. The radial hole holds about
$10^{-5}$ of the weight of the kernel, against $0.38$ for the angular hole.

The same correction is available for the radial side, if it ever matters. The $a_k$ are
non-negative and summable, so $q_k=a_k/\sum_{k'}a_{k'}$ is a probability distribution. Draw
$k\sim q$ with the feature $\sqrt{\sum a_{k'}}\,\rho_k(s)$. This is unbiased for
$k_{\mathrm{rad}}$, by the same argument. There is no reason to do it. Sampling removes a bias
and adds variance (§4), and the radial side has no bias worth that exchange.

### The encoder stays deterministic, and the method adds no hyperparameter

The encoder is a deterministic function of its weights. The same input gives the same
embedding, at training time and at inference time.

The estimate of the loss is random. Every minibatch method already has that property, because
the composition of a batch is a draw. A draw of $m$ adds a second source of randomness to the
*gradient estimate*. It does not change the map that the network learns. Dropout does randomise
the network; this method does not.

The distribution is $\mathrm{Poisson}(c)$ with $c=2\beta\alpha^2$. $\beta$ and $\alpha$ are
kernel parameters, and you choose them before this step. So there is nothing to tune, because
the coefficients must be that distribution.

The method adds one control, $D$, the number of draws to average. $D$ sets compute against
variance; it is not a modelling choice. Each value of $L$ changes **what the loss can see**.
Each value of $D$ sees the same quantity, with more noise or less noise.

---

## 4. Limitations, with the math

### A cap on $m$ gives exact blindness again

Cap the mixture at $M$. The estimator then targets $k_M=\sum_{m\le M}p_m t^m$. Its RKHS is the
space of polynomials of degree $\le M$ on the sphere. That space is finite-dimensional, so the
kernel is not characteristic, and §2 applies without a change.

A cap does not remove the defect. It moves the defect from degree $L$ to degree $M$. The
discarded mass $\Pr[\mathrm{Poisson}(c)>M]$ at $c=4/3$ is:

| $M$ | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| discarded | 38.5% | 15.1% | 4.6% | 1.2% | 0.25% | 0.05% |

So the method samples $m$ without a bound. This costs nothing. $\mathbb{E}[m]=c=4/3$, and
Poisson tails decrease faster than geometric tails. The largest $m$ in $D=10^3$ draws is
therefore $O(\log D/\log\log D)\approx6$. There is no reason for a cap.

### A fixed draw has finite rank, so you must draw again at each step

Hold the $D$ features fixed. The estimator is then $\langle\Psi(u),\Psi(u')\rangle$ for an
explicit feature map $\Psi:S^{d-1}\to\mathbb{R}^D$. Its rank is $D$, so it is blind on a set of
codimension $D$, by §2. Draw again at every optimisation step. Then
$\mathbb{E}[\widehat{\nabla\mathcal{E}}]=\nabla\mathcal{E}$, no *fixed* blind direction exists,
and SGD targets the true minimiser.

| | blind set |
|---|---|
| harmonic truncation $\ell\le L$ | fixed, the same at every step, so a **bias** |
| one fixed random draw | fixed, but arbitrary, so still a bias |
| a new draw at each step | moves at every step, so a **variance** |

A bias does not average out across steps. A variance does. One fixed random draw is the worst
choice.

### The variance increases exponentially in $c$, which is the real constraint

Two constants matter here, and they differ. One is for a single pair. The other is for the
energy, which is the quantity that the loss reports.

**For one pair.** Define $\gamma(u,u'):=\mathbb{E}_w[(w^\top u)^2(w^\top u')^2]$, the second
moment of one factor. Expand
$(w^\top u)^2(w^\top u')^2=\sum_{i,j,k,l}u_iu_ju'_ku'_l\,w_iw_jw_kw_l$. For Rademacher $w$, the
expectation $\mathbb{E}[w_iw_jw_kw_l]$ vanishes unless the indices form pairs. Each of the
three pairings contributes $1$. If all four indices are equal, the three pairings give the same
term, and $\mathbb{E}[w_i^4]=1$. So
$$\mathbb{E}[w_iw_jw_kw_l]=\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk}-2\,\delta_{ijkl}.$$
Substitute this, and use $\lVert u\rVert=\lVert u'\rVert=1$:
$$\gamma(u,u') \;=\; 1 \;+\; 2(u^\top u')^2 \;-\; 2\sum_i u_i^2u_i'^2 .$$
Multiply over the $m$ independent factors, then average over the Poisson draw. The sum
$\sum_m p_m \gamma^m$ is the Poisson generating function $G(z)=e^{c(z-1)}$ at $z=\gamma$:
$$\mathbb{E}\bigl[\psi(u)^2\psi(u')^2\bigr] \;=\; \mathbb{E}_m\bigl[\gamma^m\bigr] \;=\;
\boxed{\,e^{\,c\,(\gamma-1)}\,}$$
On the diagonal, $u=u'$ and $\gamma=3-2\sum_iu_i^4\approx3$, so the second moment is about
$e^{2c}$. That is the worst case, and it is a number for one pair. If $u$ is nearly orthogonal
to $u'$, which is typical at high $d$ where $u^\top u'\sim d^{-1/2}$, then $\gamma\to1$ and the
second moment tends to $1$.

**For the energy.** The energy averages over pairs. At the target, that average is far from the
diagonal worst case. The variance of the realized energy is $V(P)/D$, where
$V(P)=\mathbb{E}[A^4]-\mathcal{E}(P)^2$.

Pair the Rademacher indices, then apply the generating function again. This gives
$\mathbb{E}[A^4]=\mathbb{E}_{x_1..x_4\sim P}[e^{c(Q-1)}]$, where
$Q=t_{12}t_{34}+t_{13}t_{24}+t_{14}t_{23}-2\sum_i u_{1i}u_{2i}u_{3i}u_{4i}$.

At the uniform target, four independent directions are nearly orthogonal, so $Q\to0$. The
**relative** variance for one draw is then $e^{c}-1$. It does not use $d$, the batch size $N$,
or the radial factor. Let $\varepsilon$ be the relative standard error on the energy. Then

$$\boxed{\;D \;=\; \frac{e^{c}-1}{\varepsilon^{2}}\;}$$

This is the constant that the Lean development uses. `realizedEnergy_variance` gives the $1/D$
law, and `featureCount_suffices` turns a bound on the variance into a feature count through
Chebyshev. At $c=4/3$, where $e^c-1=2.794$:

| $\varepsilon$ | 20% | 10% | 8.5% | 5% |
|---|---|---|---|---|
| $D$ | 70 | 279 | **384** | 1117 |

The value $D=384$ in use is the $8.5\%$ choice.

**Agreement with measurement.** Take $c=4/3$ and $D=384$. The target constant predicts
$\varepsilon=\sqrt{2.794/384}=8.5\%$. The worst case for one pair, $e^{2c}=14.4$, predicts
$\sqrt{14.4/384}=19\%$. The measured relative standard deviation on a clustered batch was
$12\%$. A clustered batch lies between the target and the diagonal, so the two constants
predict a value between $8.5\%$ and $19\%$.

**Feasibility.** Demand $\varepsilon\le0.1$ with $D\le10^4$. This gives $e^{c}-1\le100$, so
$$c \;=\; 2\beta\alpha^2 \;\lesssim\; 4.6 .$$
The neural configuration is at $c=4/3$, which is well inside the limit. The point-cloud
configuration is at $c=81.9$, where $e^{c}-1\approx4\times10^{35}$. The necessary $D$ is then
impossible to compute. But every spectral variant is also impossible at that $c$, and this is
why those runs use the pairwise method.

### The logarithm is biased, and the bias has a closed form

The estimate of the energy is unbiased. The code descends
$(1/\beta)\log\widehat{\mathcal{E}}_D$, and $\log$ is concave. By Jensen's inequality,
$\mathbb{E}[\log\widehat{\mathcal{E}}] < \log\mathbb{E}[\widehat{\mathcal{E}}]$. The bias is
$$-\frac{e^{c}-1}{2D} \;=\; -\frac{\varepsilon^{2}}{2}.$$
So it is not an independent constraint on $D$. It is the variance constraint again. At $c=4/3$
and $D=384$, the bias is $-0.0036$.

The bias does not move the optimum. $\mu_0$ stays an exact critical point of
$\mathbb{E}[\log\widehat{\mathcal{E}}]$, and the bias makes the bowl steeper, not flatter. Its
permanent effect is far from the target. There, the loss under-reports a collapsed batch by
about $14/D$ of the collapse signal, so it tolerates collapse a little too much. The Lean
development does not cover the logarithm. All of it is about the energy.

### Heavy tails: a finite variance is not concentration

$\psi$ is a *product* of $m$ variables that are close to Gaussian, so its distribution is close
to log-normal. At high $d$, $w^\top u$ is close to standard normal, by the central limit theorem
over the $d$ coordinates. The $2p$-th moment of a standard normal is the double factorial
$(2p-1)!!=1\cdot3\cdot5\cdots(2p-1)$. Multiply over $m$ factors, then apply the Poisson
generating function again:
$$\mathbb{E}\bigl[\psi(u)^{2p}\bigr] \;\approx\; e^{\,c\,\left((2p-1)!!\,-\,1\right)} .$$

| $p$ | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| $(2p-1)!!$ | 1 | 3 | 15 | 105 |
| $\mathbb{E}[\psi^{2p}]$ at $c=4/3$ | 1 | 14.4 | $1.3\times10^{8}$ | $1.7\times10^{60}$ |

The moments increase twice exponentially in $p$. So one feature is far from *sub-Gaussian*.
Bernstein-type concentration inequalities assume that the variance controls all the moments, so
they do not apply to one feature.

The estimator of the energy is much better behaved, and its noise depends on the position. At
the uniform target, a feature contributes $1$ if it drew $m=0$, and about $0$ otherwise. The
reason is that $\psi$ averages to about $0$ over the sphere for $m\ge1$.

So $\widehat{\mathcal{E}}_D(\mu_0)$ is close to binomial. The predicted s.d.
$\sqrt{p_0(1-p_0)/D}$ is $0.0551$ at $D=64$, against $0.0554$ measured. Its range is finite, and
its excess kurtosis is $-0.2$. At a degenerate configuration such as an antipodal pair, the same
estimator has an s.d. $4.3$ times larger, and excess kurtosis $+59.7$.

So Hoeffding's inequality does apply near the target. A concentration bound for a neighbourhood
of $\mu_0$ is therefore much easier than a bound over all $P$. Far from the target the tails are
heavy, and sample means converge slowly. One visible symptom: a Monte-Carlo estimate of the
second moment for one pair was $16\%$ below the exact value at $4\times10^5$ samples. A heavy
right tail with too few samples gives that result.

### The exchange

$$\underbrace{d^{\,L}}_{\text{exact: enumerate the basis}}\qquad\longleftrightarrow\qquad
\underbrace{e^{c}-1}_{\text{sample: draw the zonal function}}$$

To capture the Poisson mass, you need $L\gtrsim c+\sqrt{c}$. That is the mean plus one standard
deviation, because $\mathrm{Poisson}(c)$ has mean $c$ and variance $c$. At $c=4/3$ that gives
$L\approx2.5$, so $L=3$, and $N_{\le3}=366\,016$ patterns at $d=128$. $L=4$ costs
$1.2\times10^7$ patterns. Sampling costs $(e^{c}-1)/\varepsilon^2$ features at every $d$.

So sampling exchanges a cost in $d$ for a cost in $c$. The application sets $d$, and you choose
$c$. That is the better exchange, but only while $c=O(1)$.

### Not checked here

- **Gradient variance.** $\nabla_u\psi(u)=\sum_i w_i\prod_{j\ne i}(w_j^\top u)$ is computable,
  and the test `TestPoissonVarianceAndD` in the notebook reports the gradient cosine against
  the exact target. So a measurement exists. No bound exists, and gradient variance is not the
  same as value variance. Training uses gradients.
- **Radial coupling.** The variance above is for the angular factor alone. A product with the
  exact cosine modes multiplies the variances.
- **No timing.** The $O(\cdot)$ costs are a model of the operation count, not a measurement of
  wall-clock time. `python/notebooks/poisson_benchmarks.ipynb` measures wall-clock time
  separately.
- **Normalisation.** $u=x/\lVert x\rVert$ sends gradients through the projection to the sphere.
  This is the same as the existing method, but it is untested here.
- **The convention for self-pairs.** The pairwise method subtracts the self terms, so it is a
  U-statistic. Every feature form, including this one, keeps them, so it is a V-statistic, and
  it is high by $(e^c-1)/N$. Apply
  $\widehat{\mathcal{E}}_{\text{corrected}} = (N\widehat{\mathcal{E}}-1)/(N-1)$ before you
  compare the two methods.

---

## 5. Summary

| property | pairwise | harmonic $\ell\le L$ | Poisson mode sampling |
|---|---|---|---|
| cost | $O(N^2d)$ | $O(NKN_{\le L})$, $N_{\le L}\sim d^L$ | $O(N(Sd+Dc)K)$ |
| linear in $N$ | no | yes | yes |
| linear in $d$ | yes | **no** ($d^L$) | yes |
| sees harmonic degree $\ell$ | all | only $\ell\le L$ | all, in expectation |
| characteristic | yes | **no** | yes, in expectation |
| type of error | — | **bias**, irreducible | variance, $\propto(e^{c}-1)/D$ |
| fails when | $N$ is large | always, above $L$ | $c\gtrsim4.6$ |

Harmonic truncation gives linearity in $N$, but it loses the characteristic property. Poisson
mode sampling gives both properties, and it pays with a variance that increases like $e^{c}$.
