"""What the picture proves: the l<=1 loss is a function of ONE number -- the length of
the average arrow -- so every arrangement whose arrows cancel gets the identical score,
and that score is the target's own. The true energies of those same arrangements differ
by a factor of two.

Top   : four arrangements, all with average arrow exactly zero.
Bottom: what the l<=1 loss reports for each (identical) vs what the full kernel says.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import integrate, special
import math

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig_blind.png")

c, d = 4.0 / 3.0, 128
nu = (d - 2) / 2.0


def log_iv(mu, x, kmax=60):
    k = np.arange(kmax)
    return special.logsumexp((2 * k + mu) * math.log(x / 2)
                             - special.gammaln(k + 1) - special.gammaln(k + mu + 1))


def A(l):
    return math.exp(-c + special.gammaln(nu) + nu * math.log(2 / c) + math.log(nu + l)
                    + log_iv(nu + l, c)
                    + special.gammaln(l + 2 * nu) - special.gammaln(2 * nu)
                    - special.gammaln(l + 1))


A0, A1 = A(0), A(1)
w = lambda t: (1 - t * t) ** ((d - 3) / 2.0)
E_target = (math.exp(-c) * integrate.quad(lambda t: math.exp(c * t) * w(t), -1, 1, limit=400)[0]
            / integrate.quad(w, -1, 1, limit=400)[0])


def energy(th, p=None):
    th = np.asarray(th, float)
    p = np.ones_like(th) if p is None else np.asarray(p, float)
    p = p / p.sum()
    return float(math.exp(-c) * (p[:, None] * p[None, :] * np.exp(c * np.cos(th[:, None] - th[None, :]))).sum())


G = 4096
tg = np.arange(G) * 2 * np.pi / G
CONFIGS = [
    ("uniform on a\ngreat circle", tg, np.ones(G)),
    ("a two-lobed belt", tg, 1 + np.cos(2 * tg)),
    ("four clusters", np.array([0, .5, 1, 1.5]) * np.pi, None),
    ("one antipodal pair", np.array([0.0, np.pi]), None),
]
Etrue = [energy(t, p) for _, t, p in CONFIGS]
for (n, t, p), E in zip(CONFIGS, Etrue):
    print(f"{n.replace(chr(10),' '):<22} true {E:.6f}   reported {A0:.6f}   gap {E-E_target:.6f}")
print(f"{'target (uniform S^127)':<22} true {E_target:.6f}   reported {A0:.6f}")

fig = plt.figure(figsize=(11.4, 6.0))
gs = fig.add_gridspec(2, 1, height_ratios=[1.0, 1.15], hspace=0.30)

# ---------------- top: the four arrangements ----------------------------------
gsT = gs[0].subgridspec(1, 4, wspace=0.10)
th = np.linspace(0, 2 * np.pi, 600)
for i, (name, tt, pp) in enumerate(CONFIGS):
    ax = fig.add_subplot(gsT[0, i])
    ax.plot(np.cos(th), np.sin(th), color="0.78", lw=1.0, ls=":")
    if pp is None:                                   # a few atoms
        ax.plot(np.cos(tt), np.sin(tt), "o", color="#2c5aa0", ms=9, zorder=3)
    elif np.allclose(pp, pp[0]):                     # uniform ring
        ax.plot(np.cos(th), np.sin(th), color="#2c5aa0", lw=4.5, solid_capstyle="round")
    else:                                            # density -> equal-mass dots
        cdf = np.cumsum(pp); cdf /= cdf[-1]
        q = np.interp(np.linspace(0, 1, 60, endpoint=False), cdf, tt)
        ax.plot(np.cos(q), np.sin(q), "o", color="#2c5aa0", ms=4.2, zorder=3)
    ax.plot(0, 0, "x", color="#c0392b", ms=8, mew=2.2, zorder=4)
    ax.text(0, -0.30, "average arrow $=0$", color="#c0392b", fontsize=8.5,
            ha="center", va="top")
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_xlim(-1.35, 1.35); ax.set_ylim(-1.35, 1.35)
    ax.set_title(name, fontsize=9.5, pad=3)

fig.text(0.5, 0.975, "four different arrangements — the arrows cancel in every one",
         ha="center", fontsize=12, fontweight="bold")
fig.text(0.5, 0.932, "drawn inside one 2-plane of $\\mathbb{R}^{128}$; the arithmetic below is exact",
         ha="center", fontsize=9, color="0.4")

# ---------------- bottom: reported vs true ------------------------------------
axb = fig.add_subplot(gs[1])
x = np.arange(len(CONFIGS))
axb.bar(x - 0.19, [A0] * len(CONFIGS), width=0.36, color="#9aaed8",
        label="what the $\\ell \\leq 1$ loss reports")
axb.bar(x + 0.19, Etrue, width=0.36, color="#c0392b",
        label="what the full kernel says")
axb.axhline(E_target, color="0.25", ls="--", lw=1.5, label="the target's own energy")

for i, E in enumerate(Etrue):
    axb.text(i - 0.19, A0 + 0.012, f"{A0:.3f}", ha="center", fontsize=8.5, color="#2c5aa0")
    axb.text(i + 0.19, E + 0.012, f"{E:.3f}", ha="center", fontsize=8.5, color="#c0392b")

axb.set_xticks(x)
axb.set_xticklabels([n.replace("\n", " ") for n, _, _ in CONFIGS], fontsize=9.5)
axb.set_ylabel("kernel energy")
axb.set_ylim(0, 0.74)
axb.spines[["top", "right"]].set_visible(False)
axb.legend(frameon=False, fontsize=9.5, loc="upper left", ncol=1,
           handlelength=1.4, borderaxespad=0.2)
axb.set_title("the reported number is identical — and identical to the target's, so the loss sees no error at all",
              fontsize=10.5, fontweight="bold", pad=8)

fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
