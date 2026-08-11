"""What the picture proves: the mode table is a multiplication table of two weight lists,
so both the cost and the share of the kernel kept factorise into a row part and a column
part -- and the column part is already at 100%, so every loss sits in the rows.

rows  = angular degree l, weight A_l = Poisson(c) pmf, c = 2*beta*alpha^2 = 4/3
cols  = radial mode k,   weight R_k proportional to 1 (k=0) and 2 exp(-pi^2 k^2/(4 beta)) (k>=1), beta=8
cell  = A_l * R_k  (the joint weight of one mode)
box   = what "l <= 1, k <= 5" keeps
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import math

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig_mode_grid.png")

c, beta = 4.0 / 3.0, 8.0
LMAX, KMAX = 5, 5

A = np.array([math.exp(-c) * c**l / math.factorial(l) for l in range(LMAX + 1)])
a = np.pi**2 / (4 * beta)
Rfull = np.array([1.0] + [2 * math.exp(-a * k * k) for k in range(1, 400)])
R = Rfull[: KMAX + 1] / Rfull.sum()

W = np.outer(A, R)

print("angular kept (l<=1):", A[:2].sum())
print("radial kept  (k<=5):", R.sum())
print("joint kept        :", W[:2, :].sum())

fig = plt.figure(figsize=(8.4, 6.6))
gs = fig.add_gridspec(2, 2, width_ratios=[1, 5.2], height_ratios=[1, 5.2],
                      wspace=0.06, hspace=0.10)

ax = fig.add_subplot(gs[1, 1])
axL = fig.add_subplot(gs[1, 0], sharey=ax)
axT = fig.add_subplot(gs[0, 1], sharex=ax)

ax.imshow(W**0.35, cmap="Blues", vmin=0, vmax=(W.max())**0.35, aspect="auto")
for i in range(LMAX + 1):
    for j in range(KMAX + 1):
        v = 100 * W[i, j]
        txt = f"{v:.1f}" if v >= 0.05 else "~0"
        ax.text(j, i, txt, ha="center", va="center", fontsize=9,
                color="white" if W[i, j] > 0.06 else "0.25")
ax.set_xticks(range(KMAX + 1)); ax.set_yticks(range(LMAX + 1))
ax.set_xlabel("radial mode  k   (cosine number)")
ax.set_ylabel("angular group (degree $\\ell$)")
ax.xaxis.set_label_position("bottom")
ax.yaxis.tick_right(); ax.yaxis.set_label_position("right")

ax.add_patch(Rectangle((-0.5, -0.5), KMAX + 1, 2, fill=False,
                       edgecolor="crimson", lw=2.2, ls="--"))
ax.text(-0.42, 1.66, "kept by $\\ell \\leq 1$", color="crimson", fontsize=10.5,
        ha="left", va="center", fontweight="bold",
        bbox=dict(fc="white", ec="crimson", lw=1.0, pad=2.5))

axL.barh(range(LMAX + 1), A, color="0.45")
axL.invert_xaxis()
axL.set_title("angular group\nweight $A_\\ell=\\lambda_\\ell N_\\ell$", fontsize=9)
axL.tick_params(labelleft=False)
for i, v in enumerate(A):
    axL.text(v + 0.015, i, f"{100*v:.0f}%", va="center", ha="right", fontsize=8.5)
axL.set_xlim(0.52, 0)
axL.spines[["top", "right", "left"]].set_visible(False)
axL.set_xticks([])

axT.bar(range(KMAX + 1), R, color="0.45")
axT.set_title("radial weight $R_k$", fontsize=9)
axT.tick_params(labelbottom=False)
for j, v in enumerate(R):
    if v > 0.005:
        axT.text(j, v + 0.012, f"{100*v:.0f}%", ha="center", fontsize=8.5)
axT.set_ylim(0, 0.58)
axT.spines[["top", "right", "left"]].set_visible(False)
axT.set_yticks([])

fig.text(0.045, 0.975,
         "every cell = (its row's weight) $\\times$ (its column's weight),  in % of the whole kernel",
         fontsize=10.5, fontweight="bold")
fig.text(0.045, 0.940,
         f"rows keep {100*A[:2].sum():.1f}% $\\;\\cdot\\;$ columns keep {100*R.sum():.3f}%"
         f"  $\\Rightarrow$  the box keeps {100*W[:2, :].sum():.1f}%."
         "  The rows are the problem.",
         fontsize=9.5, color="0.3")

fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
