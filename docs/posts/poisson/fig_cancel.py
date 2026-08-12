"""What the picture proves: the weight of a single pattern collapses with dimension and
the number of patterns explodes with dimension, at exactly matching rates -- so their
product, the weight of a whole group, does not depend on d at all, and lands on the
Poisson curve.

Left  : per-pattern weight lambda_l, several d.  Right down, hard, and d-dependent.
Mid   : number of patterns N_l, several d.        Right up,   hard, and d-dependent.
Right : the product A_l = lambda_l * N_l.         All curves collapse onto Poisson(c).
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import special
import math

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig_cancel.png")

c, LMAX = 4.0 / 3.0, 6
DIMS = [8, 32, 128, 512]
COLS = ["#c9c9c9", "#9aaed8", "#5b7fc7", "#1f3f8f"]


def log_iv(mu, c, kmax=40):
    """log I_mu(c) by its defining series, in log space (scipy.iv underflows at mu>~300)"""
    k = np.arange(kmax)
    terms = (2 * k + mu) * math.log(c / 2) - special.gammaln(k + 1) - special.gammaln(k + mu + 1)
    return special.logsumexp(terms)


def log_C1(l, nu):
    """log C_l^nu(1) = log binom(l+2nu-1, l)"""
    return special.gammaln(l + 2 * nu) - special.gammaln(2 * nu) - special.gammaln(l + 1)


def n_harm(d, l):
    if l == 0:
        return 1
    if l == 1:
        return d
    return math.comb(d + l - 1, l) - math.comb(d + l - 3, l - 2)


def log_A(d, l, c):
    nu = (d - 2) / 2.0
    return (-c + special.gammaln(nu) + nu * math.log(2 / c)
            + math.log(nu + l) + log_iv(nu + l, c) + log_C1(l, nu))


# sanity: log-space route must agree with the direct scipy route where the latter works
nu = 63.0
direct = math.log(special.iv(nu + 2, c))
print(f"log I_65(c): log-space {log_iv(nu+2, c):.10f}  vs scipy {direct:.10f}")

ls = np.arange(LMAX + 1)
poisson = np.array([math.exp(-c) * c**l / math.factorial(l) for l in ls])

fig, axes = plt.subplots(1, 3, figsize=(13.2, 4.0))
axL, axM, axR = axes

for d, col in zip(DIMS, COLS):
    A = np.array([math.exp(log_A(d, l, c)) for l in ls])
    N = np.array([float(n_harm(d, l)) for l in ls])
    lam = A / N
    print(f"d={d:>4}  sum A = {A.sum():.6f}   max |A - Poisson| = {np.abs(A-poisson).max():.2e}")
    axL.semilogy(ls, lam, "o-", color=col, lw=2, ms=4, label=f"$d={d}$")
    axM.semilogy(ls, N, "o-", color=col, lw=2, ms=4, label=f"$d={d}$")
    axR.plot(ls, A, "o-", color=col, lw=2, ms=4, label=f"$d={d}$")

axR.plot(ls, poisson, "k--", lw=1.6, label="Poisson($c$)")

axL.set_title("weight of ONE pattern, $\\lambda_\\ell$", fontsize=10.5, fontweight="bold")
axL.set_ylabel("$\\lambda_\\ell$   (log scale)")
axL.text(0.98, 0.93, "falls like $(c/d)^\\ell$", transform=axL.transAxes,
         ha="right", fontsize=9, color="0.35")

axM.set_title("how many patterns, $N_\\ell$", fontsize=10.5, fontweight="bold")
axM.set_ylabel("$N_\\ell$   (log scale)")
axM.text(0.02, 0.93, "rises like $d^\\ell/\\ell!$", transform=axM.transAxes,
         ha="left", fontsize=9, color="0.35")

axR.set_title("their product, $A_\\ell=\\lambda_\\ell N_\\ell$", fontsize=10.5, fontweight="bold")
axR.set_ylabel("share of the kernel's weight")
axR.text(0.5, 0.88, "$d$ has cancelled out", transform=axR.transAxes,
         ha="center", fontsize=10, color="#c0392b", fontweight="bold")
axR.set_ylim(0, 0.42)

for ax in axes:
    ax.set_xlabel("group (harmonic degree $\\ell$)")
    ax.set_xticks(ls)
    ax.spines[["top", "right"]].set_visible(False)
    ax.legend(frameon=False, fontsize=8.5,
              loc={id(axL): "lower left", id(axM): "lower right", id(axR): "upper right"}[id(ax)])

fig.tight_layout()
fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
