"""Every number in fourier_features.md that is not machine-checked.

Run:  .venv/bin/python docs/posts/fourier/variance_check.py

Memory: no array here exceeds ~40 MB. The angular target integrals use
Gauss-Jacobi quadrature, not a batch, so the dimension costs nothing.

Sections
  1. The target characteristic function, and a check against the Bessel form.
  2. Relative variance per draw at the uniform target, for three estimators.
  3. The same away from the target.
  4. The estimator is unbiased: features against the exact pairwise sum.
  5. The self-pair term is exactly one, so the U-form correction is free.
"""

from __future__ import annotations

import math

import numpy as np
from scipy.special import gammaln, ive, roots_jacobi

RNG = np.random.default_rng(20260812)

# ---------------------------------------------------------------------------
# 1. the target characteristic function
# ---------------------------------------------------------------------------


def jacobi_nodes(d: int, n: int = 400) -> tuple[np.ndarray, np.ndarray]:
    """Nodes and normalised weights for the law of <u, e> when u ~ Unif(S^{d-1}).

    That law has density proportional to (1 - x^2)^{(d-3)/2} on [-1, 1].
    """
    x, w = roots_jacobi(n, 0.5 * (d - 3), 0.5 * (d - 3))
    return x, w / w.sum()


def phi_sigma(r: np.ndarray, x: np.ndarray, w: np.ndarray) -> np.ndarray:
    """E_{u ~ Unif(S^{d-1})} cos(r <omega/|omega|, u>) as a function of r = |omega|."""
    out = np.empty_like(r)
    step = 4096
    for s in range(0, r.size, step):
        blk = r[s:s + step]
        out[s:s + step] = np.cos(blk[:, None] * x[None, :]) @ w
    return out


def lambda_ell(d: int, c: float, ell: int) -> float:
    nu = 0.5 * (d - 2)
    log_pref = gammaln(nu + 1.0) + nu * (math.log(2.0) - math.log(c))
    return float(math.exp(log_pref) * ive(nu + ell, c))


def section_1() -> None:
    print("=" * 78)
    print("1.  The target characteristic function")
    print("=" * 78)
    print("phi_sigma(r) is the mean of cos(<omega,u>) over the uniform sphere, at |omega| = r.")
    print("Check: E_omega[phi_sigma(|omega|)^2] must equal lambda_0, the angular energy")
    print("of the uniform measure. omega ~ N(0, c I_d), so |omega|^2 = c * chi^2_d.")
    print()
    print(f"{'d':>5} {'c':>8} {'lambda_0 exact':>15} {'E[phi^2] measured':>19} {'rel err':>10}")
    n = 400_000
    for c in (4.0 / 3.0, 4.0):
        for d in (8, 32, 128):
            x, w = jacobi_nodes(d)
            r = np.sqrt(c * RNG.chisquare(d, size=n))
            p = phi_sigma(r, x, w)
            meas = float((p * p).mean())
            exact = lambda_ell(d, c, 0)
            print(f"{d:>5} {c:>8.4f} {exact:>15.8f} {meas:>19.8f} "
                  f"{abs(meas - exact) / exact:>10.2e}")


# ---------------------------------------------------------------------------
# 2. relative variance per draw at the uniform target
# ---------------------------------------------------------------------------


def rho_at_target(d: int, c: float, n: int = 400_000) -> dict[str, float]:
    """Relative variance per draw of the angular energy estimator, at P = uniform.

    Random-phase feature : A = 2 cos^2(b) phi^2,  b ~ U[0, 2pi)
    Paired feature       : A = phi^2       (cos and sin at the same frequency)
    Both have mean E[phi^2] = lambda_0.
    """
    x, w = jacobi_nodes(d)
    r = np.sqrt(c * RNG.chisquare(d, size=n))
    p = phi_sigma(r, x, w)
    p2 = p * p
    b = RNG.uniform(0.0, 2.0 * math.pi, size=n)
    a_phase = 2.0 * np.cos(b) ** 2 * p2
    a_pair = p2

    def rel(a: np.ndarray) -> tuple[float, float]:
        m, v = a.mean(), a.var(ddof=1)
        rho = v / (m * m)
        return float(rho), float(rho * math.sqrt(2.0 / (n - 1)))

    rp, sp = rel(a_phase)
    rq, sq = rel(a_pair)
    return {
        "rho_phase": rp, "se_phase": sp,
        "rho_pair": rq, "se_pair": sq,
        "mean": float(a_phase.mean()),
        "fourth": float((p2 * p2).mean()),
    }


def section_2() -> None:
    print()
    print("=" * 78)
    print("2.  Relative variance per draw at the uniform target")
    print("=" * 78)
    print("rho = Var[one draw] / E[one draw]^2.  The feature budget is D = rho / eps^2")
    print("for a relative standard error eps.  The random-Maclaurin column is the")
    print("published closed form e^c - 1 (docs/working/_poisson_theorems/feature_count.md).")
    print()
    hdr = (f"{'c':>8} {'d':>5} {'phase feature':>16} {'paired feature':>16} "
           f"{'Maclaurin e^c-1':>17} {'ratio':>9}")
    print(hdr)
    for c in (0.5, 4.0 / 3.0, 2.0, 4.0, 8.0, 16.0, 81.9):
        for d in (32, 128):
            r = rho_at_target(d, c)
            mac = math.exp(c) - 1.0
            print(f"{c:>8.3f} {d:>5} {r['rho_phase']:>10.4f}+-{r['se_phase']:<5.4f} "
                  f"{r['rho_pair']:>10.5f}+-{r['se_pair']:<5.5f} "
                  f"{mac:>17.4g} {mac / r['rho_phase']:>9.4g}")
    print()
    print("The phase feature has an exact floor at 1/2, and it rises above that floor as c")
    print("grows:  E[A^2] = (3/2) E[phi^4] and E[A] = E[phi^2], so")
    print("rho = (3/2)E[phi^4]/E[phi^2]^2 - 1, and Jensen gives E[phi^4] >= E[phi^2]^2,")
    print("hence rho >= 1/2 for every P and every c.  The measured column follows")
    print("(3/2)e^{2c^2/d} - 1 while c^2/d stays small.")
    print("The paired feature removes the phase noise, so its rho is what is left, and that")
    print("is the spread of phi^2 alone.")


# ---------------------------------------------------------------------------
# 3. away from the target
# ---------------------------------------------------------------------------


def sphere_uniform(n: int, d: int) -> np.ndarray:
    v = RNG.standard_normal((n, d))
    return v / np.linalg.norm(v, axis=1, keepdims=True)


def configurations(d: int, n: int) -> dict[str, np.ndarray]:
    """Four batches on the sphere: the target, and three that are not it."""
    out: dict[str, np.ndarray] = {"uniform": sphere_uniform(n, d)}

    half = n // 2
    v = sphere_uniform(half, d)
    out["antipodal pairs"] = np.concatenate([v, -v], axis=0)

    k = 8
    basis = np.linalg.qr(RNG.standard_normal((d, k)))[0]      # (d, k)
    z = RNG.standard_normal((n, k)) @ basis.T
    out[f"collapse onto {k} of {d} dims"] = z / np.linalg.norm(z, axis=1, keepdims=True)

    g = RNG.standard_normal((n, d))
    g[:, 0] *= 3.0
    out["one axis stretched 3x"] = g / np.linalg.norm(g, axis=1, keepdims=True)
    return out


def rho_batch(u: np.ndarray, c: float, n_draw: int = 6_000) -> tuple[float, float, float]:
    """(rho, mean, se) of the random-phase draw energy on a fixed batch."""
    n, d = u.shape
    a = np.empty(n_draw)
    step = 256
    for s in range(0, n_draw, step):
        m = min(step, n_draw - s)
        omega = math.sqrt(c) * RNG.standard_normal((m, d))
        b = RNG.uniform(0.0, 2.0 * math.pi, size=(m, 1))
        proj = omega @ u.T                                    # (m, n)
        mean_psi = (math.sqrt(2.0) * np.cos(proj + b)).mean(axis=1)
        a[s:s + m] = mean_psi * mean_psi
    mean, var = a.mean(), a.var(ddof=1)
    rho = var / (mean * mean)
    return float(rho), float(mean), float(rho * math.sqrt(2.0 / (n_draw - 1)))


def exact_angular_energy(u: np.ndarray, c: float) -> float:
    """V-form mean of exp(c(<u_i,u_j>-1)) over all pairs, self-pairs included."""
    g = np.clip(u @ u.T, -1.0, 1.0)
    return float(np.exp(c * (g - 1.0)).mean())


def section_3() -> None:
    print()
    print("=" * 78)
    print("3.  Relative variance away from the target")
    print("=" * 78)
    d, n, c = 128, 2048, 4.0 / 3.0
    print(f"d = {d}, batch = {n}, c = {c:.4f}.  'energy' is the exact pairwise V-form.")
    print()
    print(f"{'configuration':<28} {'exact energy':>13} {'sampled mean':>12} {'rho':>16}")
    for name, u in configurations(d, n).items():
        rho, mean, se = rho_batch(u, c)
        print(f"{name:<28} {exact_angular_energy(u, c):>13.6f} {mean:>12.6f} "
              f"{rho:>10.4f}+-{se:<5.4f}")
    print()
    print("rho moves by about a factor of two across configurations that are far apart.")
    print("It is a property of the feature, not of the distribution the feature reads.")


# ---------------------------------------------------------------------------
# 4. unbiasedness
# ---------------------------------------------------------------------------


def section_4() -> None:
    print()
    print("=" * 78)
    print("4.  The feature estimate is unbiased for the exact pairwise energy")
    print("=" * 78)
    d, n, c = 32, 256, 4.0 / 3.0
    print(f"d = {d}, batch = {n}, c = {c:.4f}.  Mean of the feature estimate over many")
    print("independent features, against the exact V-form pairwise value.")
    print()
    print(f"{'batch':<28} {'exact':>12} {'sampled mean':>12} {'std error':>11} {'z':>7}")
    for name, u in configurations(d, n).items():
        exact = exact_angular_energy(u, c)
        n_draw = 200_000
        a = np.empty(n_draw)
        step = 1024
        for s in range(0, n_draw, step):
            m = min(step, n_draw - s)
            omega = math.sqrt(c) * RNG.standard_normal((m, d))
            b = RNG.uniform(0.0, 2.0 * math.pi, size=(m, 1))
            mean_psi = (math.sqrt(2.0) * np.cos(omega @ u.T + b)).mean(axis=1)
            a[s:s + m] = mean_psi * mean_psi
        est, se = a.mean(), a.std(ddof=1) / math.sqrt(n_draw)
        print(f"{name:<28} {exact:>12.6f} {est:>12.6f} {se:>11.6f} "
              f"{(est - exact) / se:>7.2f}")
    print()
    print("Every z score is within a few standard errors of zero, so no bias is visible.")


# ---------------------------------------------------------------------------
# 5. the self-pair term
# ---------------------------------------------------------------------------


def section_5() -> None:
    print()
    print("=" * 78)
    print("5.  The self-pair term is exactly one, so the U-form correction is free")
    print("=" * 78)
    print("The feature estimate keeps the N self-pairs, so it estimates the V-form.")
    print("The pairwise path drops them, so it estimates the U-form.  The two differ")
    print("by a known constant, because k_ang(u,u) = 1 at every u, and the mean of")
    print("psi(u)^2 over the phase is 1 at every u and every frequency.")
    print()
    n = 400_000
    for d in (32, 128):
        for c in (4.0 / 3.0, 4.0):
            u = sphere_uniform(1, d)[0]
            omega = math.sqrt(c) * RNG.standard_normal((n, d))
            b = RNG.uniform(0.0, 2.0 * math.pi, size=n)
            psi = math.sqrt(2.0) * np.cos(omega @ u + b)
            m2 = float((psi * psi).mean())
            se = float((psi * psi).std(ddof=1) / math.sqrt(n))
            print(f"  d = {d:>4}, c = {c:6.3f}:  mean psi^2 = {m2:.6f} +- {se:.6f}"
                  f"   (exact value 1)")
    print()
    print("So E_U = (N * E_V - 1) / (N - 1) converts one to the other with no extra")
    print("pass over the batch.")


def main() -> None:
    section_1()
    section_2()
    section_3()
    section_4()
    section_5()


if __name__ == "__main__":
    main()
