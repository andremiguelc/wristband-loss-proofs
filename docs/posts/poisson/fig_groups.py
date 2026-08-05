"""What the picture proves: the forced patterns are just "wiggle l times", and the ONLY
thing that changes in high dimension is how many of them each group holds -- which is
what makes keeping a whole group unaffordable.

Left  : the patterns on a circle, l = 0,1,2,3 (radius deformed by cos(l*theta)).
Right : how many patterns each group holds on the sphere at d=128, log scale,
        annotated with the share of the kernel's weight that group carries.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import math

OUT = "/Users/andrec/Documents/projects/math/wristband-loss-proofs/docs/posts/poisson/fig_groups.png"

d, c, LMAX = 128, 4.0 / 3.0, 5


def n_harm(d, l):
    """dim of degree-l spherical harmonics on S^{d-1}"""
    if l == 0:
        return 1
    if l == 1:
        return d
    return math.comb(d + l - 1, l) - math.comb(d + l - 3, l - 2)


counts = [n_harm(d, l) for l in range(LMAX + 1)]
mass = [math.exp(-c) * c**l / math.factorial(l) for l in range(LMAX + 1)]
counts_s2 = [2 * l + 1 for l in range(LMAX + 1)]          # d = 3, for the text
counts_s1 = [1] + [2] * LMAX                              # the circle

print("d =", d)
for l in range(LMAX + 1):
    print(f"  l={l}: circle {counts_s1[l]:>2}  d=3 {counts_s2[l]:>2}  "
          f"d=128 {counts[l]:>12,}   mass {100*mass[l]:5.1f}%")

fig = plt.figure(figsize=(11.4, 4.6))
gs = fig.add_gridspec(1, 2, width_ratios=[1.05, 1], wspace=0.22)

# ---------------- left: the patterns themselves --------------------------------
gsL = gs[0].subgridspec(1, 4, wspace=0.12)
th = np.linspace(0, 2 * np.pi, 600)
for l in range(4):
    axp = fig.add_subplot(gsL[0, l])
    val = np.cos(l * th)
    r = 1 + 0.30 * val
    x, y = r * np.cos(th), r * np.sin(th)
    axp.plot(x, y, color="0.25", lw=1.4)
    axp.fill(x, y, color="#3b7dd8", alpha=0.16)
    axp.plot(np.cos(th), np.sin(th), color="0.7", lw=0.8, ls=":")
    axp.set_aspect("equal")
    axp.set_xlim(-1.45, 1.45); axp.set_ylim(-1.85, 1.45)
    axp.axis("off")
    axp.set_title(f"group {l}", fontsize=10, pad=1)
    axp.text(0, -1.68, ["flat", "1 wiggle", "2 wiggles", "3 wiggles"][l],
             ha="center", fontsize=8.5, color="0.35")

fig.text(0.055, 0.955, "the patterns are forced: group $\\ell$ wiggles $\\ell$ times",
         fontsize=11, fontweight="bold")
fig.text(0.055, 0.895,
         "drawn on a circle, where each group holds only 1 or 2 patterns",
         fontsize=9, color="0.35")

# ---------------- right: how many of them, at d = 128 --------------------------
axc = fig.add_subplot(gs[1])
bars = axc.bar(range(LMAX + 1), counts, color=["#3b7dd8"] * 2 + ["#c0392b"] * (LMAX - 1),
               width=0.62)
axc.set_yscale("log")
axc.set_ylim(0.5, 3e12)
axc.set_xlabel("group (harmonic degree $\\ell$)", labelpad=2)
axc.set_ylabel("patterns in the group,  $N_\\ell$")
axc.set_xticks(range(LMAX + 1))
axc.set_xticklabels([f"{l}\ncarries\n{100*m:.0f}%" for l, m in enumerate(mass)],
                    fontsize=9)
for tick, l in zip(axc.get_xticklabels(), range(LMAX + 1)):
    tick.set_color("#c0392b" if l >= 2 else "#2c5aa0")
axc.spines[["top", "right"]].set_visible(False)
axc.grid(axis="y", ls=":", color="0.85", zorder=0)

for l, b in enumerate(bars):
    axc.text(b.get_x() + b.get_width() / 2, b.get_height() * 1.7,
             f"{counts[l]:,}", ha="center", fontsize=8.5)

axc.axvline(1.5, color="crimson", ls="--", lw=1.8)
axc.text(1.66, 1.8e12, "dropped by the $\\ell\\leq1$ cutoff",
         color="crimson", fontsize=9.5, va="top", fontweight="bold")

fig.text(0.575, 0.955, "in high dimension a group is huge", fontsize=11, fontweight="bold")
fig.text(0.575, 0.895, "$d=128$; a group is kept whole or not at all",
         fontsize=9, color="0.35")

fig.subplots_adjust(top=0.80)
fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
