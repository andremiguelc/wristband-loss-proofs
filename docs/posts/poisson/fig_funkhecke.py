"""What the picture proves: the Funk-Hecke integral has only two moving parts -- a
polynomial that crosses zero l times (left), and a weight saying how much sphere sits
at each angle, which collapses onto the equator as d grows (right). Everything else
in Step 5 is bookkeeping.
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy import special, integrate

OUT = "/Users/andrec/Documents/projects/math/wristband-loss-proofs/docs/posts/poisson/fig_funkhecke.png"

t = np.linspace(-1, 1, 1200)

fig, (axA, axB) = plt.subplots(1, 2, figsize=(11.2, 4.2))

# ---------------- left: the zonal polynomials, d = 3 ----------------------------
d0 = 3
nu0 = (d0 - 2) / 2.0
cols = ["#2c5aa0", "#3b9c4e", "#d1892a", "#c0392b"]
for l in range(4):
    y = special.eval_gegenbauer(l, nu0, t) / special.eval_gegenbauer(l, nu0, 1.0)
    axA.plot(t, y, color=cols[l], lw=2, label=f"group {l}")
    roots = np.where(np.diff(np.sign(y)))[0]
    print(f"  d=3 l={l}: sign changes on (-1,1) = {len(roots)}")
axA.axhline(0, color="0.7", lw=0.8)
axA.set_xlabel("$t=u^\\top u'$   (1 = same direction, $-1$ = opposite)\n"
               "drawn for $d=3$, where these are the Legendre polynomials")
axA.set_ylabel("value of the group's zonal pattern")
axA.set_ylim(-1.15, 1.35)
axA.legend(frameon=False, fontsize=9, ncol=4, loc="upper center",
           handlelength=1.2, columnspacing=1.1)
axA.spines[["top", "right"]].set_visible(False)
axA.set_title("group $\\ell$ crosses zero exactly $\\ell$ times", fontsize=10.5,
              fontweight="bold", pad=22)

# ---------------- right: how much sphere sits at angle t -----------------------
for d, col in zip((3, 8, 32, 128), ["#c9c9c9", "#9aaed8", "#5b7fc7", "#1f3f8f"]):
    w = (1 - t**2) ** ((d - 3) / 2.0)
    Z = integrate.quad(lambda x: (1 - x * x) ** ((d - 3) / 2.0), -1, 1)[0]
    axB.plot(t, w / Z, color=col, lw=2, label=f"$d={d}$")
    print(f"  d={d}: peak density {np.max(w/Z):.3f}, "
          f"mass in |t|<0.2 = {integrate.quad(lambda x: (1-x*x)**((d-3)/2.)/Z, -0.2, 0.2)[0]:.3f}")
axB.set_xlabel("$t=u^\\top u'$")
axB.set_ylabel("how much of the sphere sits at angle $t$")
axB.legend(frameon=False, fontsize=9)
axB.spines[["top", "right"]].set_visible(False)
axB.set_title("in high $d$ almost all of the sphere is at right angles",
              fontsize=10.5, fontweight="bold", pad=22)
axB.text(0.02, 0.93, "$(1-t^2)^{(d-3)/2}$, normalised", transform=axB.transAxes,
         ha="left", fontsize=8.5, color="0.4")

fig.savefig(OUT, dpi=170, bbox_inches="tight", facecolor="white")
print("wrote", OUT)
