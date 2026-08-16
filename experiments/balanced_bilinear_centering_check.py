"""Checks on the balanced/coherent bilinear centering split.

Three independent checks.

  A  The canonical balanced coefficient identity, exhaustively:

         mu(u) mu(v) 1[u prime or v prime]
           = -mu(u) 1_P(v) - mu(v) 1_P(u) - 1_P(u) 1_P(v).

     Four cases on (u prime?, v prime?); the last term is the inclusion-exclusion
     correction for the both-prime overlap.

  B  Growth analysis of the reported normalized-energy table.  The stated
     obligation is E_loc <= H N^{2+eps} with H = N, i.e. E_loc / N^3 must be
     O(N^eps) -- the tabulated column must be FLAT.  A fitted power growth is a
     failure of the obligation, not a small blemish.  This fits the reported
     columns and, crucially, the ratios C/actual and G/actual, which measure how
     much cancellation between the two new pieces is still required.

  C  An independent probe of the centered Type-II object.  Balanced region taken
     as n = u*v with both factors within a factor 2 of sqrt(n), over the square
     block n in [R^2, (R+1)^2):

         beta_II(u,v) = -mu(u)e(v) - mu(v)e(u) - rho(u)e(v) - e(u)rho(v) - e(u)e(v)
         rho(n) = 1/log n  (singleton Li density),   e(n) = 1_P(n) - rho(n)

     and the translated-prefix energy of C_R = sum_balanced beta_II normalized by
     H N^2, exactly as in the reported table.  The balanced region here is this
     script's own reading, not necessarily the repository's, so the absolute
     level is not comparable -- the GROWTH EXPONENT is what is being tested.

Usage:  python3 experiments/balanced_bilinear_centering_check.py [NMAX]
"""

import math
import sys

import numpy as np


# ---------------------------------------------------------------- A
def check_identity():
    print()
    print("=" * 84)
    print("A  canonical balanced coefficient identity, exhaustive over u,v <= 200")
    print("=" * 84)
    n = 200
    mu = np.ones(n + 1, dtype=np.int64)
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
    P = sieve.astype(np.int64)

    U, V = np.meshgrid(np.arange(1, n + 1), np.arange(1, n + 1), indexing="ij")
    muU, muV = mu[U], mu[V]
    PU, PV = P[U], P[V]
    lhs = muU * muV * ((PU == 1) | (PV == 1))
    rhs = -muU * PV - muV * PU - PU * PV
    bad = int(np.count_nonzero(lhs != rhs))
    print(f"    pairs tested: {U.size:,}     mismatches: {bad}")
    print(f"    identity holds: {bad == 0}")
    return bad == 0


# ---------------------------------------------------------------- B
def fit(xs, ys):
    lx = [math.log2(x) for x in xs]
    ly = [math.log2(y) for y in ys]
    mx, my = sum(lx) / len(lx), sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) ** 2 for a in lx)
    return num / den


def check_reported_table():
    print()
    print("=" * 84)
    print("B  growth of the reported normalized energies (obligation: FLAT)")
    print("=" * 84)
    Ns = [256, 512, 1024, 2048, 4096, 8192]
    C = [0.102, 0.066, 0.120, 0.200, 0.185, 0.403]
    G = [0.195, 0.159, 0.377, 0.315, 0.237, 0.493]
    A = [0.052, 0.074, 0.122, 0.078, 0.065, 0.076]
    print()
    print(f"{'N':>7} {'C':>8} {'G':>8} {'actual':>8} {'C/actual':>9} {'G/actual':>9}")
    for i, N in enumerate(Ns):
        print(
            f"{N:>7,} {C[i]:>8.3f} {G[i]:>8.3f} {A[i]:>8.3f} "
            f"{C[i]/A[i]:>9.2f} {G[i]/A[i]:>9.2f}"
        )
    sC, sG, sA = fit(Ns, C), fit(Ns, G), fit(Ns, A)
    print()
    print(f"    fitted growth   C ~ N^{sC:+.3f}    G ~ N^{sG:+.3f}    actual ~ N^{sA:+.3f}")
    print(f"    ratio growth    C/actual ~ N^{sC-sA:+.3f}   G/actual ~ N^{sG-sA:+.3f}")
    print()
    print("    The 'actual' column is flat, as it must be if the true square-block")
    print("    residual is at RH scale.  Both new pieces are NOT flat: they grow.")
    print()
    print("    Old split needed cancellation of order 2689/0.076 ~ 35,000x.")
    print(f"    New split needs {C[-1]/A[-1]:.1f}x at N = 8192 -- a genuine gain of about")
    print("    3.8 orders of magnitude.  But the residual requirement is still")
    print(f"    growing like N^{sC-sA:.2f}, so the cancellation between C and G is being")
    print("    reduced in size, not eliminated in kind.")
    print()
    print("    6 noisy points, non-monotone, so treat the exponents as indicative.")
    print("    The decisive test is cheap: extend to N = 16384, 32768, 65536 and")
    print("    check whether the C and G columns flatten.  If C/N^3 keeps tracking")
    print("    N^0.4, the obligation E_loc(C) << H N^{2+eps} fails as stated.")
    return sC, sG, sA


# ---------------------------------------------------------------- C
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
    """Concatenate integer ranges [lo_i, hi_i] as one flat array."""
    cnt = np.maximum(hi - lo + 1, 0)
    total = int(cnt.sum())
    if total == 0:
        return np.empty(0, dtype=np.int64), np.empty(0, dtype=np.int64)
    idx = np.repeat(np.arange(lo.size), cnt)
    starts = np.repeat(np.cumsum(cnt) - cnt, cnt)
    offs = np.arange(total) - starts
    return idx, lo[idx] + offs


def probe_type_two(NMAX):
    print()
    print("=" * 84)
    print("C  independent probe: growth of the centered Type-II prefix energy")
    print("=" * 84)
    Ns = [n for n in (128, 256, 512, 1024) if 4 * n * n <= NMAX]
    if not Ns:
        print("    (NMAX too small)")
        return
    top = 4 * max(Ns) ** 2 + 8 * max(Ns)
    print(f"    sieving to {top:,} ...", flush=True)
    mu, isP = build(top)
    mu64 = mu.astype(np.float64)
    P64 = isP.astype(np.float64)
    rho = np.zeros(top + 1, dtype=np.float64)
    k = np.arange(2, top + 1, dtype=np.float64)
    rho[2:] = 1.0 / np.log(k)
    e = P64 - rho

    print()
    print(f"{'N':>7} {'E_loc(C)/N^3':>14} {'E_loc(actual)/N^3':>19} {'ratio':>8}")
    rows = []
    M = np.concatenate(([0], np.cumsum(mu.astype(np.int64))))
    for N in Ns:
        cvals, avals = [], []
        for R in range(N, 2 * N):
            u = np.arange(max(2, (R + 1) // 2), 2 * R + 1, dtype=np.int64)
            lo = -((-R * R) // u)
            hi = ((R + 1) * (R + 1) - 1) // u
            iu, vv = ranges_expand(lo, hi)
            if vv.size == 0:
                cvals.append(0.0)
            else:
                uu = u[iu]
                keep = (vv >= 2) & (vv <= 2 * R) & (vv >= (R + 1) // 2)
                uu, vv = uu[keep], vv[keep]
                b = (
                    -mu64[uu] * e[vv]
                    - mu64[vv] * e[uu]
                    - rho[uu] * e[vv]
                    - e[uu] * rho[vv]
                    - e[uu] * e[vv]
                )
                cvals.append(float(b.sum()))
            avals.append(float(M[(R + 1) * (R + 1)] - M[R * R]))
        pc = np.cumsum(cvals)
        pa = np.cumsum(avals)
        ec = float(np.sum(pc * pc)) / N**3
        ea = float(np.sum(pa * pa)) / N**3
        rows.append((N, ec, ea))
        print(f"{N:>7,} {ec:>14.4f} {ea:>19.4f} {ec/max(ea,1e-12):>8.2f}")

    if len(rows) >= 3:
        sc = fit([r[0] for r in rows], [max(r[1], 1e-12) for r in rows])
        sa = fit([r[0] for r in rows], [max(r[2], 1e-12) for r in rows])
        print()
        print(f"    fitted growth   C ~ N^{sc:+.3f}    actual ~ N^{sa:+.3f}")
        print()
        print("    Balanced region here is this script's reading (both factors within")
        print("    a factor 2 of sqrt(n)), so absolute levels are not comparable to")
        print("    the reported table.  The exponent is the transferable quantity.")


def check_five_piece():
    """Exact polynomial verification of the five-piece centering.

    The identity is degree <= 2 in each of the six free variables
    (mu_u, mu_v, rho_u, rho_v, P_u, P_v), so agreement on a 3-point grid per
    variable with exact rational arithmetic is a COMPLETE proof, not a sample.
    This is the mathematical content of
    `RHLean/Analysis/BalancedPrimeBilinearCentering.lean`.
    """
    from fractions import Fraction as Fr
    from itertools import product

    print()
    print("=" * 84)
    print("D  five-piece centering, exact over a complete rational grid")
    print("=" * 84)
    pts = [Fr(-1), Fr(0), Fr(3, 2)]
    bad = 0
    total = 0
    for mu_u, mu_v, rho_u, rho_v, P_u, P_v in product(pts, repeat=6):
        e_u, e_v = P_u - rho_u, P_v - rho_v
        lhs = -mu_u * P_v - mu_v * P_u - P_u * P_v
        rhs = (
            (-mu_u * e_v - mu_v * e_u)            # muE
            + (-e_u * e_v)                        # eE
            + (-rho_u * e_v - e_u * rho_v)        # rhoE
            + (-mu_u * rho_v - mu_v * rho_u)      # muRho
            + (-rho_u * rho_v)                    # rhoRho
        )
        total += 1
        bad += lhs != rhs
    print(f"    grid points: {total}    mismatches: {bad}")
    print(f"    identity holds: {bad == 0}  (complete for degree <= 2 per variable)")
    return bad == 0


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5_000_000
    check_identity()
    check_reported_table()
    probe_type_two(NMAX)
    check_five_piece()


if __name__ == "__main__":
    main()
