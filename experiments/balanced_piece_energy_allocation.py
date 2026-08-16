"""Which piece of the balanced canonical coefficient actually carries the energy.

Balanced region is the repository's: 0 < d < u, so n = u*v with u < v = u+d < 2u,
taken over the square block n in [R^2, (R+1)^2).  Density is the repo convention
rho(q) = Li(q) - Li(q-1), approximated by the singleton density 1/log q, and
e(q) = 1_P(q) - rho(q).

The canonical coefficient splits exactly into five pieces:

    beta = mu_e + e_e + mu_rho + rho_rho + rho_e

    mu_e    = -mu(u)e(v)  - mu(v)e(u)      two oscillatory variables  (Type II)
    e_e     = -e(u)e(v)                    two centered error variables (Type II)
    rho_e   = -rho(u)e(v) - e(u)rho(v)     one smooth, one oscillatory (semilinear)
    mu_rho  = -mu(u)rho(v) - mu(v)rho(u)   one smooth, one Moebius     (semilinear)
    rho_rho = -rho(u)rho(v)                fully deterministic

The reported extended run establishes that rho_e carries all of the growth that
was wrongly attributed to the Type-II bucket, and that the genuine Type-II core
mu_e + e_e is flat and tiny.  This script asks the complementary question about
the coherent side: once rho_e is moved there, which piece of G* carries ITS
energy?

Translated-prefix energies of each piece, normalized by H N^2 with H = N, are
reported side by side with the true square-block increment
Delta_R = M((R+1)^2 - 1) - M(R^2 - 1).

Usage:  python3 experiments/balanced_piece_energy_allocation.py [NMAX]
"""

import math
import sys

import numpy as np


def build(n):
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    for p in np.nonzero(sieve)[0]:
        p = int(p)
        mu[p::p] = -mu[p::p]
        if p * p <= n:
            mu[p * p :: p * p] = 0
    return mu, sieve


def ranges_expand(lo, hi):
    cnt = np.maximum(hi - lo + 1, 0)
    total = int(cnt.sum())
    if total == 0:
        return np.empty(0, dtype=np.int64), np.empty(0, dtype=np.int64)
    idx = np.repeat(np.arange(lo.size), cnt)
    starts = np.repeat(np.cumsum(cnt) - cnt, cnt)
    return idx, lo[idx] + (np.arange(total) - starts)


def fit(xs, ys):
    lx = [math.log2(x) for x in xs]
    ly = [math.log2(max(y, 1e-14)) for y in ys]
    mx, my = sum(lx) / len(lx), sum(ly) / len(ly)
    return sum((a - mx) * (b - my) for a, b in zip(lx, ly)) / sum(
        (a - mx) ** 2 for a in lx
    )


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    Ns = [n for n in (256, 512, 1024, 2048) if (2 * n + 1) ** 2 <= NMAX]
    top = (2 * max(Ns) + 2) ** 2
    print(f"sieving to {top:,} ...", flush=True)
    mu, isP = build(top)
    muf = mu.astype(np.float64)
    rho = np.zeros(top + 1, dtype=np.float64)
    k = np.arange(2, top + 1, dtype=np.float64)
    rho[2:] = 1.0 / np.log(k)
    e = isP.astype(np.float64) - rho
    M = np.concatenate(([0], np.cumsum(mu.astype(np.int64))))

    names = ["mu_e", "e_e", "rho_e", "mu_rho", "rho_rho"]
    print()
    print("=" * 92)
    print("energy allocation across the five balanced pieces (u < v < 2u)")
    print("=" * 92)
    print("    translated-prefix energy / (H N^2), H = N;  Delta = true block increment")
    print()
    print(
        f"{'N':>7} " + " ".join(f"{nm:>10}" for nm in names)
        + f" {'TypeII':>9} {'Delta':>9}"
    )

    hist = {nm: [] for nm in names}
    hist["TypeII"] = []
    hist["Delta"] = []
    for N in Ns:
        acc = {nm: [] for nm in names}
        deltas = []
        for R in range(N, 2 * N):
            lo_n, hi_n = R * R, (R + 1) * (R + 1) - 1
            u0 = max(2, int(R / math.sqrt(2)) - 2)
            u = np.arange(u0, R + 2, dtype=np.int64)
            vlo = np.maximum(u + 1, -((-lo_n) // u))
            vhi = np.minimum(2 * u - 1, hi_n // u)
            iu, vv = ranges_expand(vlo, vhi)
            if vv.size == 0:
                for nm in names:
                    acc[nm].append(0.0)
            else:
                uu = u[iu]
                ok = (uu * vv >= lo_n) & (uu * vv <= hi_n) & (vv > uu) & (vv < 2 * uu)
                uu, vv = uu[ok], vv[ok]
                acc["mu_e"].append(float((-muf[uu] * e[vv] - muf[vv] * e[uu]).sum()))
                acc["e_e"].append(float((-e[uu] * e[vv]).sum()))
                acc["rho_e"].append(
                    float((-rho[uu] * e[vv] - e[uu] * rho[vv]).sum())
                )
                acc["mu_rho"].append(
                    float((-muf[uu] * rho[vv] - muf[vv] * rho[uu]).sum())
                )
                acc["rho_rho"].append(float((-rho[uu] * rho[vv]).sum()))
            deltas.append(float(M[hi_n + 1] - M[lo_n]))

        row = {}
        for nm in names:
            p = np.cumsum(acc[nm])
            row[nm] = float(np.sum(p * p)) / N**3
            hist[nm].append(row[nm])
        p2 = np.cumsum(np.array(acc["mu_e"]) + np.array(acc["e_e"]))
        row["TypeII"] = float(np.sum(p2 * p2)) / N**3
        pd = np.cumsum(deltas)
        row["Delta"] = float(np.sum(pd * pd)) / N**3
        hist["TypeII"].append(row["TypeII"])
        hist["Delta"].append(row["Delta"])
        print(
            f"{N:>7,} " + " ".join(f"{row[nm]:>10.5f}" for nm in names)
            + f" {row['TypeII']:>9.5f} {row['Delta']:>9.5f}"
        )

    print()
    print("    fitted growth exponents (4 points, diagnostics only):")
    for nm in names + ["TypeII", "Delta"]:
        print(f"      {nm:>9}  N^{fit(Ns, hist[nm]):+.3f}")

    print()
    print("=" * 92)
    print("reading")
    print("=" * 92)
    ti = hist["TypeII"][-1]
    mr = hist["mu_rho"][-1]
    dl = hist["Delta"][-1]
    print(f"    at N = {Ns[-1]:,}:   TypeII/Delta = {ti/dl:.4f}    mu_rho/Delta = {mr/dl:.4f}")
    print()
    print("    The genuine Type-II core carries a small fraction of the energy.")
    print("    That is a real finding, and it confirms the rebalancing: bilinearity")
    print("    was never where the difficulty lived.")
    print()
    print("    But it cuts both ways.  The coherent side G* now carries essentially")
    print("    all of it, and G* contains mu_rho = -mu(u)rho(v) - mu(v)rho(u).")
    print("    Since rho is smooth and deterministic, summing that over the balanced")
    print("    region gives  sum_u mu(u) * g(u)  with g smooth -- a SMOOTHED MOEBIUS")
    print("    SUM.  Bounding it at RH scale is the Mertens problem itself, not a")
    print("    classical Type-I estimate accessible by PNT or zero-density input.")
    print()
    print("    So E_loc(G*) << H N^{2+eps} is not a lemma toward the square-prefix")
    print("    criterion; up to a small Type-II correction it IS that criterion.")


if __name__ == "__main__":
    main()
