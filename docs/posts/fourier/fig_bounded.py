"""The figure that carries the note: a bounded feature gives a slower budget.

Left  — what one draw's feature value looks like. The Fourier feature lives inside
        a hard interval. The random-Maclaurin feature has no interval.
Right — the price of that, in features per step. Relative variance per draw at
        the uniform target, against the kernel scale c.

Run:  .venv/bin/python docs/posts/fourier/fig_bounded.py

Memory: every array below is at most a few tens of megabytes.
"""

from __future__ import annotations

import math
import os

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np
from scipy.special import roots_jacobi

HERE = os.path.dirname(os.path.abspath(__file__))
RNG = np.random.default_rng(20260812)

INK = "#1a1a1a"
BLUE = "#2f6f9f"
RED = "#c0492b"
GREEN = "#3f7d52"
GREY = "#8a8a8a"


# ---------------------------------------------------------------------------
# the two features, one general-position direction, many draws
# ---------------------------------------------------------------------------


def fourier_feature_samples(c: float, n: int) -> np.ndarray:
    """sqrt(2) cos(<omega, u> + b).  <omega, u> ~ N(0, c) at any unit u."""
    proj = math.sqrt(c) * RNG.standard_normal(n)
    phase = RNG.uniform(0.0, 2.0 * math.pi, size=n)
    return math.sqrt(2.0) * np.cos(proj + phase)


def maclaurin_feature_samples(d: int, c: float, n: int, u: np.ndarray) -> np.ndarray:
    """prod_{i<m} <w_i, u>, m ~ Poisson(c), w_i Rademacher in {-1,+1}^d."""
    m = RNG.poisson(c, size=n)
    out = np.ones(n)
    for k in range(1, int(m.max()) + 1):
        idx = np.nonzero(m >= k)[0]
        if idx.size == 0:
            continue
        w = RNG.integers(0, 2, size=(idx.size, d)).astype(np.float64) * 2.0 - 1.0
        out[idx] *= w @ u
    return out


# ---------------------------------------------------------------------------
# relative variance per draw at the uniform target, without any batch
# ---------------------------------------------------------------------------


def jacobi_nodes(d: int, n: int = 400) -> tuple[np.ndarray, np.ndarray]:
    x, w = roots_jacobi(n, 0.5 * (d - 3), 0.5 * (d - 3))
    return x, w / w.sum()


def phi_sigma(r: np.ndarray, x: np.ndarray, w: np.ndarray) -> np.ndarray:
    out = np.empty_like(r)
    step = 4096
    for s in range(0, r.size, step):
        blk = r[s:s + step]
        out[s:s + step] = np.cos(blk[:, None] * x[None, :]) @ w
    return out


def rho_at_target(d: int, c: float, n: int = 400_000) -> tuple[float, float]:
    """(rho_phase, rho_pair) at P = uniform on S^{d-1}."""
    x, w = jacobi_nodes(d)
    r = np.sqrt(c * RNG.chisquare(d, size=n))
    p2 = phi_sigma(r, x, w) ** 2
    b = RNG.uniform(0.0, 2.0 * math.pi, size=n)
    a_phase = 2.0 * np.cos(b) ** 2 * p2

    def rel(a: np.ndarray) -> float:
        m = a.mean()
        return float(a.var(ddof=1) / (m * m))

    return rel(a_phase), rel(p2)


def main() -> None:
    d, c_work = 128, 4.0 / 3.0
    n_feat = 200_000

    # a general-position direction: the Maclaurin feature is degenerate at u = e_1,
    # where every projection is +-1 and the product has modulus exactly one.
    u = RNG.standard_normal(d)
    u /= np.linalg.norm(u)

    f_four = fourier_feature_samples(c_work, n_feat)
    f_macl = maclaurin_feature_samples(d, c_work, n_feat, u)
    macl_max = float(np.abs(f_macl).max())

    print(f"Fourier feature          : range [{f_four.min():+.3f}, {f_four.max():+.3f}],"
          f"  proved bound +-{math.sqrt(2):.4f}")
    print(f"random Maclaurin feature : range [{f_macl.min():+.3f}, {f_macl.max():+.3f}],"
          f"  proved bound none")
    print(f"  general-position u; at the axis-aligned u every value is exactly +-1")
    print(f"  fraction of Maclaurin draws outside +-sqrt2 : "
          f"{float((np.abs(f_macl) > math.sqrt(2)).mean()):.4f}")

    cs = np.array([0.5, 4.0 / 3.0, 2.0, 3.0, 4.0, 6.0, 8.0, 12.0])
    rho_ph, rho_pr = [], []
    print()
    print(f"{'c':>7} {'rho phase':>11} {'rho paired':>11} {'(3/2)e^{2c^2/d}-1':>19} "
          f"{'e^c-1':>12} {'ratio to phase':>15}")
    for c in cs:
        rp, rq = rho_at_target(d, float(c))
        rho_ph.append(rp)
        rho_pr.append(rq)
        approx = 1.5 * math.exp(2.0 * c * c / d) - 1.0
        print(f"{c:>7.3f} {rp:>11.4f} {rq:>11.5f} {approx:>19.4f} "
              f"{math.exp(c) - 1:>12.4g} {(math.exp(c) - 1) / rp:>15.4g}")

    fig, (axL, axR) = plt.subplots(1, 2, figsize=(11.8, 4.6))

    # ---- left: the feature values -------------------------------------------
    lim = 6.0
    bins = np.linspace(-lim, lim, 241)          # out-of-range draws are dropped,
    axL.hist(f_macl, bins=bins, color=RED, alpha=0.55,   # not piled on the edge
             label="random Maclaurin feature", log=True)
    axL.hist(f_four, bins=bins, color=BLUE, alpha=0.8,
             label="Fourier feature", log=True)
    for s in (-1, 1):
        axL.axvline(s * math.sqrt(2), color=BLUE, ls="--", lw=1.5)
    axL.set_ylim(0.8, 4e5)
    axL.text(math.sqrt(2) + 0.20, 1.1e5, r"$\pm\sqrt{2}$",
             color=BLUE, fontsize=12, fontweight="bold")
    axL.annotate(
        f"{100 * float((np.abs(f_macl) > math.sqrt(2)).mean()):.0f}% of draws land\n"
        f"outside, out to {macl_max:.0f}",
        xy=(4.6, 25), xytext=(2.3, 3.0e3),
        color=RED, fontsize=9.5, ha="left",
        arrowprops=dict(arrowstyle="->", color=RED, lw=1.2),
    )
    axL.annotate(
        "the empty product,\ndrawn $e^{-c}$ of the time",
        xy=(1.0, 5.0e4), xytext=(-5.6, 6.0e4),
        color=RED, fontsize=8.6, ha="left",
        arrowprops=dict(arrowstyle="->", color=RED, lw=1.0),
    )
    axL.set_xlim(-lim, lim)
    axL.set_xlabel("value of one feature at one point")
    axL.set_ylabel("count out of 200 000 draws")
    axL.set_title("A.  One feature, one draw", loc="left", fontweight="bold")
    axL.legend(loc="lower center", fontsize=9, framealpha=0.92)

    # ---- right: what it costs -----------------------------------------------
    grid = np.linspace(0.3, 12.5, 300)
    axR.plot(grid, np.exp(grid) - 1.0, color=RED, lw=1.8, ls="--",
             label=r"random Maclaurin,  $e^{c}-1$")
    axR.plot(cs, rho_ph, "s-", color=BLUE, ms=5, lw=1.6,
             label=r"Fourier, random phase")
    axR.plot(cs, rho_pr, "o-", color=GREEN, ms=5, lw=1.6,
             label=r"Fourier, paired cosine and sine")
    axR.axhline(0.5, color=BLUE, ls=":", lw=1.3,
                label="floor $1/2$, from the random phase")
    axR.axvline(c_work, color=GREY, lw=1.0)
    axR.text(c_work + 0.22, 3.6e-3, "$c=4/3$, the setting in use",
             color=GREY, fontsize=8.6, va="bottom", ha="left")

    i = int(np.argmin(np.abs(cs - c_work)))
    axR.annotate(
        f"{(math.exp(c_work)-1)/rho_ph[i]:.0f}$\\times$ fewer features",
        xy=(c_work, rho_ph[i]), xytext=(5.0, 0.13),
        fontsize=9.5, color=BLUE,
        arrowprops=dict(arrowstyle="->", color=BLUE, lw=1.0),
    )
    axR.annotate(
        f"{(math.exp(c_work)-1)/rho_pr[i]:.0f}$\\times$ fewer, paired",
        xy=(c_work, rho_pr[i]), xytext=(5.0, 0.018),
        fontsize=9.5, color=GREEN,
        arrowprops=dict(arrowstyle="->", color=GREEN, lw=1.0),
    )

    axR.set_yscale("log")
    axR.set_xlabel(r"kernel scale $c = 2\beta\alpha^{2}$")
    axR.set_ylabel("relative variance per draw")
    axR.set_title(f"B.  What that costs, in features  ($d={d}$)", loc="left",
                  fontweight="bold")
    axR.legend(loc="upper left", fontsize=8.8, framealpha=0.92)
    axR.set_ylim(3e-3, 3e5)

    fig.suptitle(
        "A feature with a bound keeps the feature budget out of the exponential",
        fontsize=13, fontweight="bold", y=0.995,
    )
    fig.text(0.5, 0.015,
             "Panel A: $c=4/3$, $d=128$, one general-position direction. "
             "Panel B: exact target integrals by Gauss-Jacobi quadrature, "
             "400 000 frequency draws per point.",
             ha="center", fontsize=8.4, color=GREY)
    fig.tight_layout(rect=(0, 0.035, 1, 0.955))
    out = os.path.join(HERE, "fig_bounded.png")
    fig.savefig(out, dpi=160)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
