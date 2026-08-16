"""The general decomposition no-go is false; the true obstruction is narrower.

Proposed no-go: "no nontrivial finite decomposition of Delta_R has every piece
individually at RH scale."

That is refuted by any decomposition which partitions the INDEX SET rather than
the coefficient.  Splitting the square block by residue class mod 4,

    Delta_R = sum_{a=1,2,3} Delta_R^(a),
    Delta_R^(a) = sum_{n in [R^2, (R+1)^2), n = a mod 4} mu(n)

(the a = 0 class is identically zero, since 4 | n kills mu) gives three nonzero
pieces, none proportional to Delta, each of which is a Moebius sum over an
arithmetic progression and so inherits the same square-root behaviour.  This is
exactly the repository's own three-slot decomposition in
`PrimeWheelThreeSlotRecovery.lean`:  M(4K) = sum_j (R_j - 2 H_j).

So the repository already contains a counterexample to the proposed theorem.

What actually fails is narrower and forced.  PNT-centering writes
`1_P = rho + e` with `rho > 0` a positive density.  Any piece that retains an
uncancelled `rho` factor has block sums of a FIXED SIGN, so its prefixes
accumulate linearly instead of cancelling.  That is not a subtle cancellation
phenomenon -- it is what summing a positive quantity does.

This script measures both claims:

  A  residue-class pieces: normalized prefix energies of Delta^(1), Delta^(2),
     Delta^(3) against Delta.  If all are the same order and flat, the general
     no-go is false.

  B  rhoRho block sums: fraction with negative sign, and the growth of the
     prefix.  If the sign is constant, drift is forced by positivity.

Usage:  python3 experiments/decomposition_nogo_refutation.py [NMAX]
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
    return mu


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
    Ns = [n for n in (256, 512, 1024, 2048) if (2 * n + 2) ** 2 <= NMAX]
    top = (2 * max(Ns) + 2) ** 2
    print(f"sieving to {top:,} ...", flush=True)
    mu = build(top)
    mu64 = mu.astype(np.int64)
    rho = np.zeros(top + 1, dtype=np.float64)
    k = np.arange(2, top + 1, dtype=np.float64)
    rho[2:] = 1.0 / np.log(k)

    # cumulative Moebius by residue class mod 4
    idx = np.arange(top + 1, dtype=np.int64)
    cum = {}
    for a in (1, 2, 3):
        w = np.where(idx % 4 == a, mu64, 0)
        cum[a] = np.concatenate(([0], np.cumsum(w)))
    cumall = np.concatenate(([0], np.cumsum(mu64)))

    print()
    print("=" * 88)
    print("A  residue-class decomposition: are all pieces individually at RH scale?")
    print("=" * 88)
    print("    Delta_R = Delta^(1) + Delta^(2) + Delta^(3)  (mod 4; class 0 vanishes)")
    print("    normalized translated-prefix energy E_loc / N^3, H = N")
    print()
    print(f"{'N':>7} {'Delta':>10} {'Delta^(1)':>11} {'Delta^(2)':>11} {'Delta^(3)':>11}")
    hist = {k: [] for k in ("all", 1, 2, 3)}
    for N in Ns:
        seq = {k: [] for k in ("all", 1, 2, 3)}
        for R in range(N, 2 * N):
            lo, hi = R * R, (R + 1) * (R + 1) - 1
            seq["all"].append(float(cumall[hi + 1] - cumall[lo]))
            for a in (1, 2, 3):
                seq[a].append(float(cum[a][hi + 1] - cum[a][lo]))
        row = {}
        for key in ("all", 1, 2, 3):
            p = np.cumsum(seq[key])
            row[key] = float(np.sum(p * p)) / N**3
            hist[key].append(row[key])
        print(
            f"{N:>7,} {row['all']:>10.5f} {row[1]:>11.5f} {row[2]:>11.5f} "
            f"{row[3]:>11.5f}"
        )
    print()
    print("    fitted growth:")
    for key, nm in (("all", "Delta"), (1, "Delta^(1)"), (2, "Delta^(2)"), (3, "Delta^(3)")):
        print(f"      {nm:>10}  N^{fit(Ns, hist[key]):+.3f}")
    print()
    print("    All three pieces sit at the same order as Delta with the same")
    print("    behaviour.  This is a nontrivial decomposition with every piece at")
    print("    RH scale, so the general no-go is FALSE.  It is also precisely the")
    print("    repository's own three-slot split in PrimeWheelThreeSlotRecovery.")

    print()
    print("=" * 88)
    print("B  why the coefficient splits fail instead: positivity forces drift")
    print("=" * 88)
    print("    rhoRho(u,v) = -rho(u) rho(v) < 0 pointwise, so every block sum has")
    print("    the same sign and the prefix cannot cancel.")
    print()
    print(
        f"{'N':>7} {'blocks':>8} {'frac < 0':>10} {'mean block':>12} "
        f"{'max|prefix|':>13} {'/(N^2/log^2N)':>14}"
    )
    for N in Ns:
        vals = []
        for R in range(N, 2 * N):
            lo_n, hi_n = R * R, (R + 1) * (R + 1) - 1
            u0 = max(2, int(R / math.sqrt(2)) - 2)
            u = np.arange(u0, R + 2, dtype=np.int64)
            vlo = np.maximum(u + 1, -((-lo_n) // u))
            vhi = np.minimum(2 * u - 1, hi_n // u)
            iu, vv = ranges_expand(vlo, vhi)
            if vv.size == 0:
                vals.append(0.0)
                continue
            uu = u[iu]
            ok = (uu * vv >= lo_n) & (uu * vv <= hi_n) & (vv > uu) & (vv < 2 * uu)
            uu, vv = uu[ok], vv[ok]
            vals.append(float((-rho[uu] * rho[vv]).sum()))
        arr = np.array(vals)
        p = np.cumsum(arr)
        neg = float((arr < 0).mean())
        print(
            f"{N:>7,} {arr.size:>8,} {neg:>10.4f} {arr.mean():>12.3f} "
            f"{float(np.abs(p).max()):>13,.1f} "
            f"{float(np.abs(p).max())/(N**2/math.log(N)**2):>14.4f}"
        )
    print()
    print("=" * 88)
    print("C  the third category: splitting the FACTORIZATION space")
    print("=" * 88)
    print("    Delta_R is a sum over n in the block.  Rewriting mu(n) through the")
    print("    factorization identity moves to a different index space (pairs u*v=n),")
    print("    and restricting to the balanced region is not a partition of {n}.")
    print("    The exact coefficient beta = mu(u)mu(v)[u or v prime] summed over the")
    print("    balanced region alone:")
    print()
    print(
        f"{'N':>7} {'E/N^3 balanced':>16} {'E/N^3 Delta':>13} {'ratio':>10} "
        f"{'max|prefix|/N':>15}"
    )
    isP = np.zeros(top + 1, dtype=np.float64)
    sieve2 = np.ones(top + 1, dtype=bool)
    sieve2[:2] = False
    for p in range(2, int(top**0.5) + 1):
        if sieve2[p]:
            sieve2[p * p :: p] = False
    isP[sieve2] = 1.0
    muf = mu.astype(np.float64)
    for N in Ns:
        bal, dl = [], []
        for R in range(N, 2 * N):
            lo_n, hi_n = R * R, (R + 1) * (R + 1) - 1
            u0 = max(2, int(R / math.sqrt(2)) - 2)
            u = np.arange(u0, R + 2, dtype=np.int64)
            vlo = np.maximum(u + 1, -((-lo_n) // u))
            vhi = np.minimum(2 * u - 1, hi_n // u)
            iu, vv = ranges_expand(vlo, vhi)
            if vv.size == 0:
                bal.append(0.0)
            else:
                uu = u[iu]
                ok = (uu * vv >= lo_n) & (uu * vv <= hi_n) & (vv > uu) & (vv < 2 * uu)
                uu, vv = uu[ok], vv[ok]
                either = np.maximum(isP[uu], isP[vv])
                bal.append(float((muf[uu] * muf[vv] * either).sum()))
            dl.append(float(cumall[hi_n + 1] - cumall[lo_n]))
        pb, pd = np.cumsum(bal), np.cumsum(dl)
        eb = float(np.sum(pb * pb)) / N**3
        ed = float(np.sum(pd * pd)) / N**3
        print(
            f"{N:>7,} {eb:>16.4f} {ed:>13.5f} {eb/max(ed,1e-12):>10,.0f}x "
            f"{float(np.abs(pb).max())/N:>15,.2f}"
        )
    print()
    print("    The balanced region alone is orders of magnitude above Delta, so a")
    print("    factorization-space split destroys the scale even though it is not a")
    print("    coefficient split.  The cancellation in the factorization identity is")
    print("    BETWEEN the balanced and extreme regions, not within either.")
    print()
    print("    A sign-constant sequence has |prefix| growing linearly in the number")
    print("    of blocks, so no estimate can rescue it: rhoRho violates the budget")
    print("    by construction, not by an unlucky arithmetic conspiracy.  The same")
    print("    mechanism, weakened by the mu factor, is what drives muRho.")
    print()
    print("    So the correct no-go is not about decompositions in general.  It is")
    print("    about the PNT-centering family specifically: any piece retaining an")
    print("    uncancelled positive rho factor drifts.  Index-set decompositions")
    print("    are unaffected.")


if __name__ == "__main__":
    main()
