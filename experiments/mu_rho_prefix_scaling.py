"""Does mu_rho, taken alone, satisfy the RH-scale local-energy obligation?

The coherent obligation is  E_loc(G*) << H N^{2+eps}  with H = N, i.e. the
normalized column  E_loc / N^3  must be FLAT, which forces the translated
prefixes  P_j = sum_{R=N}^{N+j} (block sum)  to be  O(N^{1+eps}).

Before treating mu_rho as an RH-equivalent lemma it is worth checking whether
the bound is even true for it in isolation.  On the balanced region
`u < v < 2u`, `R^2 <= u*v < (R+1)^2`, the v-window attached to a given u has
length about `(2R+1)/u ~ 2` for `u ~ R`, so

    mu_rho block sum  ~  -(2/log N) * sum_{u ~ R} mu(u) * w(u)

with `w` a smooth O(1) weight.  Each block sum is therefore a Mertens-type sum
over `u ~ R` divided by `log N`, of expected size `sqrt(N)/log N`.  Consecutive
blocks overlap heavily in `u`, so the prefixes need not cancel across `R`.  If
they accumulate linearly, `P_j ~ j sqrt(N) / log N`, giving

    E_loc / N^3  ~  N / log^2 N        -- growing, so the obligation FAILS.

This script measures `max_j |P_j|`, its ratio to `N^1` and to
`N^{1.5} / log N`, and the normalized energy, for mu_rho alone and for the true
block increment Delta as a control.

Usage:  python3 experiments/mu_rho_prefix_scaling.py [NMAX]
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
    muf = mu.astype(np.float64)
    rho = np.zeros(top + 1, dtype=np.float64)
    k = np.arange(2, top + 1, dtype=np.float64)
    rho[2:] = 1.0 / np.log(k)
    M = np.concatenate(([0], np.cumsum(mu.astype(np.int64))))

    print()
    print("=" * 94)
    print("mu_rho translated prefixes against the RH-scale obligation")
    print("=" * 94)
    print("    obligation needs max|P_j| = O(N^{1+eps}) and E_loc/N^3 flat")
    print()
    print(
        f"{'N':>7} {'max|P_j| mu_rho':>16} {'/N':>8} {'/(N^1.5/logN)':>14} "
        f"{'E/N^3 mu_rho':>13} {'max|P_j| Delta':>15} {'E/N^3 Delta':>12}"
    )
    hist_e, hist_p, hist_ed, hist_pd = [], [], [], []
    for N in Ns:
        mr, dl = [], []
        for R in range(N, 2 * N):
            lo_n, hi_n = R * R, (R + 1) * (R + 1) - 1
            u0 = max(2, int(R / math.sqrt(2)) - 2)
            u = np.arange(u0, R + 2, dtype=np.int64)
            vlo = np.maximum(u + 1, -((-lo_n) // u))
            vhi = np.minimum(2 * u - 1, hi_n // u)
            iu, vv = ranges_expand(vlo, vhi)
            if vv.size == 0:
                mr.append(0.0)
            else:
                uu = u[iu]
                ok = (uu * vv >= lo_n) & (uu * vv <= hi_n) & (vv > uu) & (vv < 2 * uu)
                uu, vv = uu[ok], vv[ok]
                mr.append(float((-muf[uu] * rho[vv] - muf[vv] * rho[uu]).sum()))
            dl.append(float(M[hi_n + 1] - M[lo_n]))
        p = np.cumsum(mr)
        pd = np.cumsum(dl)
        e = float(np.sum(p * p)) / N**3
        ed = float(np.sum(pd * pd)) / N**3
        mp, mpd = float(np.abs(p).max()), float(np.abs(pd).max())
        hist_e.append(e)
        hist_p.append(mp)
        hist_ed.append(ed)
        hist_pd.append(mpd)
        print(
            f"{N:>7,} {mp:>16,.1f} {mp/N:>8.3f} "
            f"{mp/(N**1.5/math.log(N)):>14.4f} {e:>13.5f} "
            f"{mpd:>15,.1f} {ed:>12.5f}"
        )

    print()
    print("    fitted growth (4 points, diagnostics only):")
    print(f"      max|P_j| mu_rho   N^{fit(Ns, hist_p):+.3f}    (obligation needs <= 1)")
    print(f"      E/N^3    mu_rho   N^{fit(Ns, hist_e):+.3f}    (obligation needs 0)")
    print(f"      max|P_j| Delta    N^{fit(Ns, hist_pd):+.3f}")
    print(f"      E/N^3    Delta    N^{fit(Ns, hist_ed):+.3f}")

    print()
    print("=" * 94)
    print("reading")
    print("=" * 94)
    print("    If max|P_j| for mu_rho grows faster than N^1 while Delta's does not,")
    print("    then E_loc(mu_rho) << H N^{2+eps} is FALSE, not merely hard: mu_rho")
    print("    satisfies no RH-scale bound in isolation, and can only be bounded")
    print("    together with the other coherent pieces it cancels against.")
    print()
    print("    In that case the proposed registry entry")
    print("        mu_rho RH-scale  <->  RH")
    print("    is not correct as stated -- the left side is false, so the")
    print("    biconditional would make RH false.  What is true is the one-way")
    print("    statement about the COHERENT SIDE AS A WHOLE.")


if __name__ == "__main__":
    main()
