"""Growth of the smooth-core channel H in the three-slot (R - 2H) decomposition.

`PrimeWheelThreeSlotRecovery.lean` proves the EXACT pointwise identity

    raw - 2 * smoothCore = mu       (under square-root coverage)

hence, per slot j in {1,2,3} and at complete four-cell prefixes,

    R_j - 2 H_j = sum_{n <= 4K, n = j mod 4} mu(n),   sum_j (R_j - 2H_j) = M(4K).

Because that identity is exact, two reported observations carry no independent
information:

  * cos(R, 2H) ~ 1 and the scalar fit 2H ~ 1.0003 * R are forced by the identity
    together with |M(X)| << |R(X)|, i.e. by the Prime Number Theorem.  Concretely
    1 - cos ~ (1/2) |R-2H|^2 / |R|^2, so a small amplitude ratio and a high
    cosine are the same measurement reported twice.

  * the "amplitude ratio" rho_R = |R-2H| / sqrt(|R|^2 + |2H|^2) is
    |M(X)| / (size of the channels) up to bounded factors -- a measurement OF
    M(X), not evidence of a mechanism producing it.

What is NOT determined by the identity, and what actually decides whether the
decomposition can reach the square-root scale, is the size of H itself:

    H_j(K) = -sum_{n <= 4K, n = j mod 4, squarefree, P^+(n) <= y} mu(n),  y = sqrt(4K)

If |H| grows faster than X^{1/2}, then M = R - 2H expresses a target of size
X^{1/2} as the difference of two channels each much larger, and the route needs
that difference controlled to a relative precision finer than the channels'
own scale -- strictly harder than the original problem.

This script (1) reproduces the note's x = 10^7 slot values as a check that the
semantics match, and (2) fits the growth exponent of |H|.

Usage:  python3 experiments/three_slot_smooth_core_scale.py [N]
"""

import math
import sys

import numpy as np


def build_mu_and_maxpf(n):
    """Moebius array and largest-prime-factor array on [0, n]."""
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    maxpf = np.zeros(n + 1, dtype=np.int32)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    root = int(n**0.5)
    for p in range(2, root + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    for p in np.nonzero(sieve)[0]:
        p = int(p)
        mu[p::p] = -mu[p::p]
        maxpf[p::p] = p          # ascending p leaves the largest prime factor
        sq = p * p
        if sq <= n:
            mu[sq::sq] = 0
    return mu, maxpf


def slot_sums(mu32, maxpf, X, y):
    """Return (M_j, H_j) for j = 1,2,3 over n <= X, smoothness cutoff y."""
    n = np.arange(X + 1, dtype=np.int64)
    w = mu32[: X + 1].astype(np.int64)
    smooth = (maxpf[: X + 1] <= y) & (maxpf[: X + 1] > 0)
    res = n & 3
    Mj, Hj = [], []
    for j in (1, 2, 3):
        sel = res == j
        Mj.append(int(w[sel].sum()))
        Hj.append(-int(w[sel & smooth].sum()))
    return Mj, Hj


def hr(title):
    print()
    print("=" * 82)
    print(title)
    print("=" * 82)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    print(f"sieving mu and largest-prime-factor for n <= {N:,} ...", flush=True)
    mu, maxpf = build_mu_and_maxpf(N)
    mu32 = mu.astype(np.int32)

    # ------------------------------------------------------------------
    hr("check: reproduce the research note's x = 10^7 slot values")
    print("    note records R = (98983, -101628, 98288), H = (49262, -51048, 49089)")
    print()
    X = 10_000_000
    if X <= N:
        Mj, Hj = slot_sums(mu32, maxpf, X, 3163)
        Rj = [Mj[i] + 2 * Hj[i] for i in range(3)]
        print(f"    computed R = ({Rj[0]}, {Rj[1]}, {Rj[2]})")
        print(f"    computed H = ({Hj[0]}, {Hj[1]}, {Hj[2]})")
        print(f"    computed R - 2H = ({Mj[0]}, {Mj[1]}, {Mj[2]})  sum = {sum(Mj)}")
        print(f"    M(10^7) = {sum(Mj)}   (identity check: {sum(Rj) - 2*sum(Hj)})")
    else:
        print("    (need N >= 10^7)")

    # ------------------------------------------------------------------
    hr("growth of the smooth-core channel |H| against the sqrt(X) target")
    print("    y = sqrt(X) square-root coverage, as in the note")
    print()
    print(
        f"{'X':>12} {'|sum H_j|':>12} {'sqrt(X)':>10} {'|H|/sqrt(X)':>12} "
        f"{'exponent':>9} {'|M(X)|':>8} {'|M|/sqrt(X)':>12}"
    )
    xs = [10**k for k in range(3, int(math.log10(N)) + 1)]
    xs += [3 * 10**k for k in range(3, int(math.log10(N // 3)) + 1)]
    xs = sorted(x for x in xs if x <= N)
    rows = []
    for X in xs:
        y = int(math.isqrt(X))
        Mj, Hj = slot_sums(mu32, maxpf, X, y)
        Hs, Ms = abs(sum(Hj)), abs(sum(Mj))
        expo = math.log(Hs) / math.log(X) if Hs > 1 else float("nan")
        rows.append((X, Hs, Ms, expo))
        print(
            f"{X:>12,} {Hs:>12,} {int(X**0.5):>10,} {Hs/math.sqrt(X):>12.2f} "
            f"{expo:>9.4f} {Ms:>8,} {Ms/math.sqrt(X):>12.4f}"
        )

    # least-squares slope of log|H| against log X
    pts = [(math.log(x), math.log(h)) for x, h, _, _ in rows if h > 1]
    if len(pts) >= 2:
        mx = sum(p[0] for p in pts) / len(pts)
        my = sum(p[1] for p in pts) / len(pts)
        num = sum((p[0] - mx) * (p[1] - my) for p in pts)
        den = sum((p[0] - mx) ** 2 for p in pts)
        slope = num / den
        print()
        print(f"    least-squares growth exponent of |H|:  X^{slope:.4f}")
        print(f"    target for the route to close:         X^0.5")
        if slope > 0.5:
            X = rows[-1][0]
            gap = X ** (slope - 0.5)
            print()
            print(f"    |H| exceeds the sqrt(X) target by a factor ~X^{slope-0.5:.4f}")
            print(f"    at X = {X:,} that is a factor of {gap:,.0f}")
            print()
            print("    So M = R - 2H writes a target of size X^0.5 as the difference")
            print("    of two channels of size X^%.2f.  Extracting M needs those" % slope)
            print("    channels to a relative precision of X^-%.2f -- finer than" % (slope - 0.5))
            print("    their own scale.  The decomposition loses ground rather than")
            print("    gaining it: |H| <= X^{1/2+eps} is itself a Moebius-sum estimate")
            print("    over smooth numbers, no easier than the Mertens bound sought.")


if __name__ == "__main__":
    main()
