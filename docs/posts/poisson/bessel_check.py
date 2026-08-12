"""Numbers for the Funk-Hecke integral and the closed-form angular weight A_l (section 1).

(1) Funk-Hecke by direct quadrature gives the same lambda_l as the closed form
    A_l = lambda_l * N_l = e^{-c} * Gamma(nu) (2/c)^nu * (nu+l) * I_{nu+l}(c) * C_l^nu(1),
    which comes from matching the modified plane-wave (Gegenbauer) expansion
        e^{ct} = Gamma(nu) (c/2)^{-nu} sum_l (nu+l) I_{nu+l}(c) C_l^nu(t).
(2) Sum_l A_l = 1 exactly (put t=1 above).
(3) d=2 sanity: lambda_n is literally the n-th Fourier coefficient of e^{-c}e^{c cos th},
    i.e. e^{-c} I_n(c) -- the modified Bessel function IS that coefficient.
"""
import numpy as np
from scipy import integrate, special
import math

c = 4.0 / 3.0
LMAX = 8


def n_harm(d, l):
    if l == 0:
        return 1
    if l == 1:
        return d
    return math.comb(d + l - 1, l) - math.comb(d + l - 3, l - 2)


def lam_quad(d, l, c):
    """Funk-Hecke integral, normalised so that f == 1 gives lambda_0 = 1."""
    nu = (d - 2) / 2.0
    w = lambda t: (1 - t * t) ** ((d - 3) / 2.0)
    Cl1 = special.eval_gegenbauer(l, nu, 1.0)
    num = integrate.quad(
        lambda t: math.exp(-c) * math.exp(c * t)
        * special.eval_gegenbauer(l, nu, t) / Cl1 * w(t), -1, 1, limit=400)[0]
    den = integrate.quad(lambda t: w(t), -1, 1, limit=400)[0]
    return num / den


def A_bessel(d, l, c):
    """closed form for the degree mass lambda_l * N_l"""
    nu = (d - 2) / 2.0
    Cl1 = special.eval_gegenbauer(l, nu, 1.0)
    pref = math.exp(-c) * math.exp(special.gammaln(nu)) * (2.0 / c) ** nu
    return pref * (nu + l) * special.iv(nu + l, c) * Cl1


for d in (8, 32, 128):
    nu = (d - 2) / 2.0
    print(f"\n=== d={d}  (nu={nu})  c={c:.4f} ===")
    print(f"{'l':>2} {'A quad':>12} {'A bessel':>12} {'Poisson':>12} {'quad-bes':>10} {'bes-Poi':>10}")
    tot_q = tot_b = 0.0
    for l in range(LMAX + 1):
        aq = lam_quad(d, l, c) * n_harm(d, l)
        ab = A_bessel(d, l, c)
        ap = math.exp(-c) * c**l / math.factorial(l)
        tot_q += aq; tot_b += ab
        print(f"{l:>2} {aq:>12.6f} {ab:>12.6f} {ap:>12.6f} {aq-ab:>10.2e} {ab-ap:>10.2e}")
    print(f"   sum(quad)={tot_q:.6f}  sum(bessel)={tot_b:.6f}")

# ---- (3) the d=2 anchor: lambda_n is the n-th Fourier coefficient ---------------
print("\n=== d=2 (circle): lambda_n vs e^{-c} I_n(c) ===")
for n in range(6):
    fc = integrate.quad(lambda th: math.exp(-c) * math.exp(c * math.cos(th))
                        * math.cos(n * th) / math.pi, 0, math.pi)[0]
    print(f"  n={n}: Fourier coeff {fc:.10f}   e^-c I_n(c) {math.exp(-c)*special.iv(n,c):.10f}")

# ---- the large-d cancellation, stated as a ratio --------------------------------
print("\n=== why d cancels: I_{nu+l}/I_nu ~ (c/2)^l / nu^l  and  N_l ~ d^l/l! ===")
for d in (32, 128, 512):
    nu = (d - 2) / 2.0
    for l in (1, 2, 3):
        ratio = special.iv(nu + l, c) / special.iv(nu, c)
        approx = (c / 2) ** l / np.prod([nu + j for j in range(1, l + 1)])
        print(f"  d={d:>4} l={l}: I ratio {ratio:.4e}  vs (c/2)^l/prod(nu+j) {approx:.4e}")
