"""Numbers for section 2 (why l<=1 is blind).

Claim to check: the l<=1 energy of ANY distribution on the sphere is exactly
    E_{<=1}(P) = A_0 + A_1 * |mean arrow|^2,
so every P whose arrows cancel gets exactly the same score as the uniform target.

We check that identity numerically against a direct double sum, then tabulate the
TRUE energy of four zero-mean configurations to show how far apart they really are.
"""
import numpy as np
from scipy import integrate, special
import math

c, d = 4.0 / 3.0, 128
nu = (d - 2) / 2.0


def log_iv(mu, x, kmax=60):
    k = np.arange(kmax)
    return special.logsumexp((2 * k + mu) * math.log(x / 2)
                             - special.gammaln(k + 1) - special.gammaln(k + mu + 1))


def log_C1(l, nu):
    return special.gammaln(l + 2 * nu) - special.gammaln(2 * nu) - special.gammaln(l + 1)


def A(l):
    """exact degree mass lambda_l * N_l"""
    return math.exp(-c + special.gammaln(nu) + nu * math.log(2 / c)
                    + math.log(nu + l) + log_iv(nu + l, c) + log_C1(l, nu))


A0, A1 = A(0), A(1)
print(f"exact  A_0 = {A0:.6f}   A_1 = {A1:.6f}   A_0+A_1 = {A0+A1:.6f}")
print(f"Poisson  p_0 = {math.exp(-c):.6f}   p_1 = {c*math.exp(-c):.6f}   "
      f"sum = {(1+c)*math.exp(-c):.6f}")

# ---- true energy of the uniform target on S^{d-1} -----------------------------
w = lambda t: (1 - t * t) ** ((d - 3) / 2.0)
Z = integrate.quad(w, -1, 1, limit=400)[0]
E_target = math.exp(-c) * integrate.quad(lambda t: math.exp(c * t) * w(t), -1, 1, limit=400)[0] / Z
print(f"\ntrue energy of the uniform target on S^{d-1}: {E_target:.6f}")

# ---- four zero-mean configurations, all inside one 2-plane of R^d -------------
K = e = None


def energy_discrete(thetas, weights=None):
    th = np.asarray(thetas, float)
    p = np.ones_like(th) / len(th) if weights is None else np.asarray(weights, float)
    p = p / p.sum()
    dt = th[:, None] - th[None, :]
    return float(math.exp(-c) * (p[:, None] * p[None, :] * np.exp(c * np.cos(dt))).sum())


def mean_arrow(thetas, weights=None):
    th = np.asarray(thetas, float)
    p = np.ones_like(th) / len(th) if weights is None else np.asarray(weights, float)
    p = p / p.sum()
    return float(np.hypot((p * np.cos(th)).sum(), (p * np.sin(th)).sum()))


# fine grids so the continuous cases are accurate
G = 4096
th_g = np.arange(G) * 2 * np.pi / G

configs = []
configs.append(("uniform on a\ngreat circle", th_g, np.ones(G)))
configs.append(("a two-lobed belt\non that circle", th_g, 1 + np.cos(2 * th_g)))
configs.append(("four clusters\n(a square)", np.array([0, .5, 1, 1.5]) * np.pi, None))
configs.append(("one antipodal\npair", np.array([0.0, np.pi]), None))

print(f"\n{'configuration':<26} {'|mean arrow|':>13} {'l<=1 reports':>13} {'true energy':>12} {'true gap':>10}")
for name, th, wt in configs:
    m = mean_arrow(th, wt)
    E = energy_discrete(th, wt)
    rep = A0 + A1 * m ** 2
    label = name.replace("\n", " ")
    print(f"{label:<26} {m:>13.2e} {rep:>13.6f} {E:>12.6f} {E-E_target:>10.6f}")

print(f"{'the uniform target':<26} {0.0:>13.2e} {A0:>13.6f} {E_target:>12.6f} {0.0:>10.6f}")

# ---- closed forms, as a cross-check of the grid results ----------------------
print("\nclosed-form cross-checks:")
print(f"  great circle   e^-c I_0(c) = {math.exp(-c)*special.iv(0,c):.6f}")
print(f"  antipodal pair (1+e^-2c)/2 = {(1+math.exp(-2*c))/2:.6f}")
sq = (4 + 8 * math.exp(-c) + 4 * math.exp(-2 * c)) / 16
print(f"  square         (4+8e^-c+4e^-2c)/16 = {sq:.6f}")

# ---- the identity E_{<=1}(P) = A_0 + A_1 |mean|^2, verified by direct double sum
print("\nidentity check on a lopsided (nonzero-mean) config, so the A_1 term is live:")
th = np.array([0.0, 0.3, 0.7, 2.9])
p = np.array([0.4, 0.3, 0.2, 0.1])
dt = th[:, None] - th[None, :]
direct = float((p[:, None] * p[None, :] * (A0 + A1 * np.cos(dt))).sum())
formula = A0 + A1 * mean_arrow(th, p) ** 2
print(f"  direct double sum {direct:.12f}   A_0 + A_1|mean|^2 {formula:.12f}")
