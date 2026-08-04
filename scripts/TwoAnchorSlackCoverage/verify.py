#!/usr/bin/env python3
"""Finite audit of the anchor-coverage tightening for issue #184.

Four independent checks, all exact:

1. Anchor algebra.  The identities and the coverage/sharpness statements
   formalized in ``RHLean/Proof/TwoAnchorSlackCoverage.lean`` are re-tested on an
   exhaustive integer grid, including the exact failure set for same-sign
   anchors.

2. End-to-end block verification.  Every prefix of the complete primorial block
   ``(13#, 17#] = (30030, 510510]`` is evaluated exactly: the true constant
   ``K_* = max |M|/sqrt(Q)``, the anchor coverage counts, and the constant
   ``K_anchor`` that the cross-term-free reduction actually requires.  The larger
   blocks through ``29#`` are handled by ``block_scan.c`` in this directory.

3. Reported diagnostics at the ``29#`` bottleneck.  Cross-term signs, the fibre
   normalization ``|P_2|/sqrt(m_2)``, ``alpha_2 sqrt(x_*)``, the degree-shell
   head/tail split, and the per-prime survivor factors are recomputed from the
   reported data and compared with the values quoted in the issue.

4. Degree-shell truncation.  The head/tail arithmetic showing that the
   degree ``0..4`` truncation cannot be used on its own.

Exact rational arithmetic (``fractions.Fraction``); floating point only for
display.  Standard library only.
"""

from fractions import Fraction as F
from math import isqrt, log

# --------------------------------------------------------------------------
# 1. anchor algebra
# --------------------------------------------------------------------------


def covers(c, y):
    """The anchor value ``c`` covers the interior value ``y``."""
    return c * (y - c) <= 0


def obligation(c, y):
    """Cross-term-free obligation numerator at the anchor ``c``: ``c^2+(y-c)^2``."""
    return c * c + (y - c) * (y - c)


def check_anchor_algebra(rng=range(-40, 41)):
    print("## 1. anchor algebra")

    # coverage half-lines
    for c in rng:
        for y in rng:
            if c > 0:
                assert covers(c, y) == (y <= c)
            elif c < 0:
                assert covers(c, y) == (c <= y)
            else:
                assert covers(c, y)
    print("   covers c y  <->  y <= c  (c>0),  c <= y  (c<0),  always  (c=0):  ok")

    # opposite signs cover every value; same signs leave exactly the far excursions
    for a in rng:
        for b in rng:
            if a * b <= 0:
                assert all(covers(a, y) or covers(b, y) for y in rng)
            else:
                bad = {y for y in rng if not covers(a, y) and not covers(b, y)}
                if a > 0:
                    assert bad == {y for y in rng if y > max(a, b)}
                else:
                    assert bad == {y for y in rng if y < min(a, b)}
    print("   opposite signs: total coverage; same signs: uncovered set is exactly")
    print("   the excursions beyond both anchors:                               ok")

    # the excess of the anchor obligation over the true requirement is exactly
    # the discarded cross term
    for c in rng:
        for y in rng:
            assert obligation(c, y) - y * y == -2 * c * (y - c)
    print("   obligation excess = discarded cross term  -2c(y-c):               ok")

    # a covering anchor makes the reduction sound
    for c in rng:
        for y in rng:
            for q in (1, 7, 100):
                for k2 in (F(1, 4), F(1), F(37, 10)):
                    if covers(c, y) and obligation(c, y) <= k2 * q:
                        assert y * y <= k2 * q
    print("   covering anchor + obligation  =>  slack nonnegative:              ok")


# --------------------------------------------------------------------------
# 2. exact end-to-end verification on one complete primorial block
# --------------------------------------------------------------------------


def mobius_upto(n):
    mu = [1] * (n + 1)
    primes = []
    composite = bytearray(n + 1)
    mu[0] = 0
    for i in range(2, n + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            composite[i * p] = 1
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def scan_block(lo, hi, mu, frozen_anchors):
    """Exact all-prefix scan of the block ``(lo, hi]``.

    ``frozen_anchors`` lists the Mertens values of all completed endpoints at or
    before ``lo``.  Returns the block report.
    """
    M = [0] * (hi + 1)
    Q = [0] * (hi + 1)
    for n in range(1, hi + 1):
        M[n] = M[n - 1] + mu[n]
        Q[n] = Q[n - 1] + (1 if mu[n] else 0)
    a, b = M[lo], M[hi]

    best = (0, 1, lo)                       # max M^2/Q  ->  K_*
    pair = (0, 1, lo, a, 0)                 # max two-endpoint obligation
    allf = (0, 1, lo, a, 0)                 # max all-frozen obligation
    cnt = {"left": 0, "right": 0, "both": 0, "neither": 0}
    anchors_all = list(frozen_anchors) + [b]
    for x in range(lo, hi + 1):
        y, q = M[x], Q[x]
        if y * y * best[1] > best[0] * best[0] * q:
            best = (abs(y), q, x)
        cl, cr = covers(a, y), covers(b, y)
        cnt["both" if cl and cr else "left" if cl else "right" if cr else "neither"] += 1
        cands = [(obligation(c, y), c) for c in (a, b) if covers(c, y)]
        if cands:
            v, c = min(cands)
            if v * pair[1] > pair[0] * q:
                pair = (v, q, x, c, y - c)
        cands = [(obligation(c, y), c) for c in anchors_all if covers(c, y)]
        if cands:
            v, c = min(cands)
            if v * allf[1] > allf[0] * q:
                allf = (v, q, x, c, y - c)
    return {
        "a": a, "b": b, "K_star": (best[0], best[1], best[2]),
        "counts": cnt, "pair": pair, "all": allf,
        "trough": min((M[x], x) for x in range(lo, hi + 1)),
        "crest": max((M[x], x) for x in range(lo, hi + 1)),
    }


def check_block():
    print("\n## 2. exact all-prefix verification of the block (13#, 17#]")
    lo, hi = 30030, 510510
    mu = mobius_upto(hi)
    M = 0
    endpoints = {}
    for n in range(1, hi + 1):
        M += mu[n]
        if n in (2, 6, 30, 210, 2310, 30030, 510510):
            endpoints[n] = M
    print("   M at primorial endpoints:", endpoints)
    frozen = [endpoints[p] for p in (2, 6, 30, 210, 2310, 30030)]
    r = scan_block(lo, hi, mu, frozen)
    ks = r["K_star"][0] / r["K_star"][1] ** 0.5
    kp = (r["pair"][0] / r["pair"][1]) ** 0.5
    ka = (r["all"][0] / r["all"][1]) ** 0.5
    print(f"   M(13#) = {r['a']}   M(17#) = {r['b']}   product = {r['a'] * r['b']}")
    print(f"   trough {r['trough']}   crest {r['crest']}")
    print(f"   K_*                        = {ks:.12f} at x = {r['K_star'][2]}")
    print(f"   coverage counts            = {r['counts']}")
    print(f"   K_anchor (two endpoints)   = {kp:.12f} at x = {r['pair'][2]}"
          f"   ratio {kp / ks:.6f}"
          f"   (anchor {r['pair'][3]}, excursion {r['pair'][4]})")
    print(f"   K_anchor (all frozen ends) = {ka:.12f} at x = {r['all'][2]}"
          f"   ratio {ka / ks:.6f}"
          f"   (anchor {r['all'][3]}, excursion {r['all'][4]})")
    print("   NOTE: the all-frozen figure is degenerate.  M(2#) = 0 is a frozen")
    print("   anchor, and a zero anchor is lossless but reimports the whole")
    print("   excursion A(x) = M(x) into the estimate the shell theorem must make.")
    assert r["counts"]["neither"] == 0, "opposite-sign endpoints must cover everything"
    assert kp >= ks - 1e-12, "the anchor reduction can never require less than K_*"
    print("   opposite-sign endpoints cover every prefix:                       ok")
    print("   the anchor reduction never asks for less than K_*:                ok")


# --------------------------------------------------------------------------
# 3. reported diagnostics at the 29# bottleneck
# --------------------------------------------------------------------------

M_23, M_29 = 3516, -5012
X_STAR, M_STAR, Q_STAR = 1109331447, -15335, 674392719
P2 = F(-59685, 4)                     # -14921.25, exact
A2 = 718357949
M2 = F(3, 4) * A2                     # 538768461.75, exact


def check_bottleneck():
    print("\n## 3. reported diagnostics at x_* = 1109331447")
    A = M_STAR - M_23
    B = M_29 - M_STAR
    assert (A, B) == (-18851, 10323)
    print(f"   A = {A}  B = {B}")
    print(f"   left  cross -2 M(L) A = {-2 * M_23 * A:>12}  favourable   "
          f"(covers: {covers(M_23, M_STAR)})")
    print(f"   right cross  2 M(U) B = {2 * M_29 * B:>12}  unfavourable "
          f"(covers: {covers(M_29, M_STAR)})")
    assert covers(M_23, M_STAR) and not covers(M_29, M_STAR)
    assert M_23 * M_29 <= 0

    k = abs(M_STAR) / Q_STAR ** 0.5
    print(f"   K_* = |M|/sqrt(Q)            = {k:.15f}   reported 0.590510118734035")
    r = abs(float(P2)) / float(M2) ** 0.5
    print(f"   |P_2|/sqrt(m_2)              = {r:.12f}   reported 0.642841823379")
    alpha = abs(P2) / M2
    print(f"   alpha_2 sqrt(x_*)            = {float(alpha) * X_STAR ** 0.5:.5f}"
          f"       reported 0.92243")
    print(f"   P_2/(M(x_*)-M(23#))          = {float(P2) / A:.10f}   reported 0.7915362580")
    # exact rational sandwiches, the form used in Lean
    assert P2 ** 2 > F("0.6428") ** 2 * M2 and P2 ** 2 < F("0.6429") ** 2 * M2
    assert alpha ** 2 * X_STAR > F("0.9224") ** 2 and alpha ** 2 * X_STAR < F("0.9225") ** 2
    print("   exact rational sandwiches for both normalizations:                ok")

    # per-prime survivor factors: ratios of the reported grouped l1 masses
    mass = [F("14921.250"), F("15267.750"), F("99527.957"), F("488367.124"),
            F("1138637.901"), F("1974160.424"), F("2833552.860"),
            F("3689151.635"), F("4563551.665"), F("5453934.006")]
    qs = [3, 5, 7, 11, 13, 17, 19, 23, 29]
    print("   survivor factors rho_q = A_{<=prev}/A_{<=q}:")
    print("     " + "  ".join(f"{q}:{float(mass[i] / mass[i + 1]):.4f}"
                              for i, q in enumerate(qs)))
    assert abs(float(mass[0] / mass[1]) - 0.9773) < 1e-4
    assert abs(float(mass[1] / mass[2]) - 0.1534) < 1e-4
    assert abs(float(mass[2] / mass[3]) - 0.2038) < 1e-4
    print(f"   accumulated -log(survivor through 29) = {-log(float(mass[0] / mass[9])):.8f}"
          f"   reported 5.90130609")
    print("   rho_q is the reciprocal l1-mass growth of the chosen grouping,")
    print("   not an operator contraction factor.")


# --------------------------------------------------------------------------
# 4. degree shells
# --------------------------------------------------------------------------

SHELL = [F("510598.977"), F("-1352337.222"), F("1014743.270"), F("80096.189"),
         F("-345576.676"), F("58276.938"), F("21526.179"), F("-1187.797"),
         F("-1099.593"), F("38.485")]


def check_shells():
    print("\n## 4. degree shells at the bottleneck")
    total = sum(SHELL)
    head, tail = sum(SHELL[:5]), sum(SHELL[5:])
    assert total == P2, "the reported shells must reproduce the exact fibre value"
    print(f"   sum of the ten reported shells = {float(total)} = P_2(x_*):      ok")
    print(f"   head E_0..E_4 = {float(head):>12}   tail E_5..E_9 = {float(tail):>11}")
    print(f"   |head|/|P_2| = {float(abs(head) / abs(total)):.4f}"
          f"      |tail|/|P_2| = {float(abs(tail) / abs(total)):.4f}")
    assert abs(head) > 6 * abs(total) and abs(tail) > 5 * abs(total)
    print("   discarding degrees >= 5 overshoots the net by more than 6x:       ok")
    l1 = sum(abs(e) for e in SHELL)
    print(f"   head share of sum_d |E_d| = {float(100 * sum(abs(e) for e in SHELL[:5]) / l1):.4f}%"
          "   (the issue quotes ~95%,")
    print("   which must refer to the per-degree leaf l1 mass, not published here)")
    cum, s = [], F(0)
    for e in SHELL:
        s += e
        cum.append(float(s))
    print("   cumulative:", " -> ".join(f"{c:.0f}" for c in cum))
    print(f"   ternary leaves 3^9 = {3 ** 9}   boolean 2^9 = {2 ** 9}"
          f"   discarded by a boolean model: {3 ** 9 - 2 ** 9}")
    assert sum(nchoosek(9, d) * 2 ** d for d in range(10)) == 3 ** 9
    assert sum(nchoosek(9, d) for d in range(10)) == 2 ** 9
    print("   shell sizes choose(9,d)*2^d sum to 3^9:                           ok")


def nchoosek(n, k):
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


if __name__ == "__main__":
    assert isqrt(4) == 2
    check_anchor_algebra()
    check_block()
    check_bottleneck()
    check_shells()
    print("\nAll checks passed.")
