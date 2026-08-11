"""What the picture proves: truncation and sampling fail in qualitatively different ways.
Truncation leaves a hole in the same place at every training step; sampling leaves noise
that shrinks with the number of features and sits in a different place every step.

Left  : which severity levels the loss actually uses, step by step -- fixed vs redrawn.
Right : the estimated kernel value for one well-aligned pair (t = 0.8), against the
        number of random features. Truncation is a permanent offset; sampling is noise.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from scipy import special
import math

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig_sample.png")

c, d, T_VAL = 4.0 / 3.0, 128, 0.8
nu = (d - 2) / 2.0
rng = np.random.default_rng(20260804)


def A(l):
    k = np.arange(60)
    logI = special.logsumexp((2 * k + nu + l) * math.log(c / 2)
                             - special.gammaln(k + 1) - special.gammaln(k + nu + l + 1))
    return math.exp(-c + special.gammaln(nu) + nu * math.log(2 / c) + math.log(nu + l) + logI
                    + special.gammaln(l + 2 * nu) - special.gammaln(2 * nu) - special.gammaln(l + 1))


A0, A1 = A(0), A(1)
k_true = math.exp(-c) * math.exp(c * T_VAL)
k_trunc = A0 + A1 * T_VAL
print(f"t={T_VAL}:  true k = {k_true:.6f}   l<=1 gives {k_trunc:.6f}   "
      f"permanent error {abs(k_true-k_trunc):.6f}")

# ------------------------------------------------------------------ right panel
# For u = e1 and u' = t e1 + sqrt(1-t^2) e2, a Rademacher w only ever enters through
# w1 and w2, and one random feature's contribution collapses to a product of m draws
# of X in {t + s, t - s} with s = sqrt(1-t^2). Mean t, second moment t^2+s^2 = 1.
S_VAL = math.sqrt(1 - T_VAL ** 2)
DMAX, TRIALS = 4096, 600
Ds = np.array([4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096])

ms = rng.poisson(c, size=(TRIALS, DMAX))
feat = np.ones((TRIALS, DMAX))
for step in range(1, ms.max() + 1):                      # multiply in one factor at a time
    live = ms >= step
    X = T_VAL + S_VAL * rng.choice([-1.0, 1.0], size=live.sum())
    feat[live] *= X
run = np.cumsum(feat, axis=1) / np.arange(1, DMAX + 1)
est = run[:, Ds - 1]
mu, sd = est.mean(axis=0), est.std(axis=0)
print(f"one-feature variance: empirical {feat.var():.4f}   predicted 1 - k^2 = {1-k_true**2:.4f}")
for D, m_, s_ in zip(Ds, mu, sd):
    print(f"  D={D:>5}  mean {m_:.4f}  sd {s_:.4f}  (predicted sd {math.sqrt(1-k_true**2)/math.sqrt(D):.4f})")
cross = (1 - k_true ** 2) / (k_true - k_trunc) ** 2
print(f"sampling noise drops below the truncation error at D > {cross:.1f}")

# ------------------------------------------------------------------- the figure
fig = plt.figure(figsize=(12.6, 5.0))
gs = fig.add_gridspec(1, 2, width_ratios=[1.06, 1], wspace=0.26)
gsL = gs[0].subgridspec(2, 1, hspace=0.55)

STEPS, LMAX, DPS = 7, 8, 16
levels = np.arange(LMAX + 1)

# --- top-left: truncation uses the same two levels forever
axT = fig.add_subplot(gsL[0])
for r in range(STEPS):
    for l in levels:
        on = l <= 1
        axT.add_patch(Rectangle((l - .42, r - .40), .84, .80,
                                facecolor="#2c5aa0" if on else "white",
                                edgecolor="0.85", lw=.6))
axT.add_patch(Rectangle((1.62, -.55), LMAX - 1.1, STEPS - .05, facecolor="#c0392b",
                        alpha=.10, edgecolor="#c0392b", lw=1.4, ls="--", zorder=3))
axT.text(5.0, (STEPS - 1) / 2, "never, at any step", color="#c0392b",
         fontsize=10.5, fontweight="bold", ha="center", va="center", zorder=4)
axT.set_title("truncating at $\\ell \\leq 1$", fontsize=10.5, fontweight="bold", pad=4)

# --- bottom-left: sampling redraws the levels every step
axS = fig.add_subplot(gsL[1])
for r in range(STEPS):
    cnt = np.bincount(rng.poisson(c, DPS), minlength=LMAX + 1)[:LMAX + 1]
    for l in levels:
        f = cnt[l] / DPS
        axS.add_patch(Rectangle((l - .42, r - .40), .84, .80,
                                facecolor=plt.cm.Blues(0.15 + 2.4 * f) if f else "white",
                                edgecolor="0.85", lw=.6))
axS.set_title(f"sampling the severity, {DPS} features per step",
              fontsize=10.5, fontweight="bold", pad=4)
axS.text(0.5, -0.52, "high levels come up rarely — in exact proportion to their weight —\n"
                     "but no level has probability zero", transform=axS.transAxes,
         ha="center", va="top", fontsize=8.5, color="0.4")

for ax in (axT, axS):
    ax.set_xlim(-.7, LMAX + .7); ax.set_ylim(STEPS - .5, -.7)
    ax.set_xticks(levels); ax.set_yticks(range(STEPS))
    ax.set_yticklabels([f"step {r+1}" for r in range(STEPS)], fontsize=8)
    ax.set_xlabel("severity level used", fontsize=9.5, labelpad=1)
    ax.tick_params(length=0, labelsize=9)
    for sp in ax.spines.values():
        sp.set_visible(False)

# --- right: the estimate for one well-aligned pair
axR = fig.add_subplot(gs[1])
axR.fill_between(Ds, mu - sd, mu + sd, color="#2c5aa0", alpha=.22, lw=0,
                 label="sampling, $\\pm1$ s.d. over 600 draws")
axR.plot(Ds, mu, "o-", color="#2c5aa0", lw=1.8, ms=4)
axR.axhline(k_true, color="0.25", ls="--", lw=1.6, label="the true kernel value")
axR.axhline(k_trunc, color="#c0392b", lw=2.2, label="$\\ell \\leq 1$, at every $D$")
axR.annotate("", xy=(6.2, k_true), xytext=(6.2, k_trunc),
             arrowprops=dict(arrowstyle="<->", color="#c0392b", lw=1.4))
axR.text(7.0, (k_true + k_trunc) / 2, f"off by {k_true-k_trunc:.2f}\nand it stays off",
         color="#c0392b", fontsize=9.5, va="center")
axR.set_xscale("log")
axR.set_xlabel("number of random features $D$")
axR.set_ylabel("estimated $k_{\\mathrm{ang}}(u,u')$")
axR.set_xlim(3.2, 6000); axR.set_ylim(0.45, 1.05)
axR.spines[["top", "right"]].set_visible(False)
axR.legend(frameon=False, fontsize=9, loc="upper right")
axR.set_title(f"one nearly-aligned pair, $t=u^\\top u'={T_VAL}$", fontsize=10.5,
              fontweight="bold", pad=6)

fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
