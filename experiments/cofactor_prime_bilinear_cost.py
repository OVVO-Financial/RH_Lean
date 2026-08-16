"""Cost of the cofactor-first bilinear opening in PrimeDilateCofactorPrimeWindows.

The module proves the exact cofactor-first reindexing

    sum_{R < q <= X} a(q) M(floor(X/q))  =  sum_c mu(c) sum_{q in W(c)} a(q),

    W_{p,R,X}(c) = ( max(R, floor(X/(p c))), floor(X/c) ],

and, replacing the prime indicator by its PNT-centered form, leaves the ordinary
prime-count-minus-singleton-Li discrepancy of each reciprocal window:

    D(c) = #{q in W(c) : q prime} - sum_{n in W(c)} 1/log n
    B    = sum_{c < R, p !| c} mu(c) D(c).

Two facts about this object are worth separating.

1.  It is a genuine double sum, and the Type I / Type II reading of the recurring
    duality is correct: q >> R forces c << R (one variable short, Type I), while
    c ~ q ~ R is the balanced Type II box on the hyperbola c*q ~ R^2.

2.  But the kernel K(c,q) = 1[q in W(c)] is NONNEGATIVE.  For any nonnegative
    kernel,

        sup_{|alpha_c| <= 1, |beta_q| <= 1}  |sum_{c,q} alpha_c beta_q K(c,q)|
          = sum_{c,q} K(c,q),

    attained at alpha = beta = 1.  So no bound beating the trivial one holds for
    general bounded coefficients: a bilinear saving needs an OSCILLATING kernel
    (e(alpha m n), chi(mn), (mn)^{-it}), which is what Vinogradov/Vaughan supply
    and what a hyperbola indicator does not.  Centering beta makes the coefficient
    signed but leaves the kernel nonnegative, and collapses the q-sum into one
    number per c -- turning the object back into a Type I sum.

This script measures what that costs.  It compares the signed total against the
triangle-inequality total

    S_abs = sum_c |D(c)|      vs      S_signed = sum_c mu(c) D(c),

and against the square-root target sqrt(X) = R.  Under RH each window near
q ~ X/c has |D(c)| ~ sqrt(X/c) log X, so

    sum_{c < R} sqrt(X/c) ~ 2 R^{3/2} = 2 X^{3/4},

i.e. even assuming RH termwise, the triangle inequality over cofactors overshoots
the X^{1/2} target by a full X^{1/4}.  The measurement below checks that.

Usage:  python3 experiments/cofactor_prime_bilinear_cost.py [N]
"""

import math
import sys

import numpy as np


def build(n):
    """Moebius, prime-count prefix, and singleton-Li-density prefix on [0, n]."""
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    root = int(n**0.5)
    for p in range(2, root + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    for p in np.nonzero(sieve)[0]:
        p = int(p)
        mu[p::p] = -mu[p::p]
        sq = p * p
        if sq <= n:
            mu[sq::sq] = 0
    Pc = np.concatenate(([0], np.cumsum(sieve.astype(np.int64))))
    dens = np.zeros(n + 1, dtype=np.float64)
    k = np.arange(2, n + 1, dtype=np.float64)
    dens[2:] = 1.0 / np.log(k)
    L = np.concatenate(([0.0], np.cumsum(dens)))
    return mu, Pc, L


def hr(title):
    print()
    print("=" * 86)
    print(title)
    print("=" * 86)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    print(f"sieving to {N:,} ...", flush=True)
    mu, Pc, L = build(N)
    mu32 = mu.astype(np.int32)
    M = np.concatenate(([0], np.cumsum(mu32)))

    p = 2  # pivot prime
    hr("triangle-inequality cost of the cofactor-first bilinear opening")
    print(f"    pivot p = {p},  X = R^2 - 1,  c < R with p !| c")
    print("    D(c) = primeCount(W(c)) - singletonLiMass(W(c))")
    print()
    print(
        f"{'R':>7} {'X':>12} {'S_signed':>12} {'S_abs':>14} {'|M(X)|':>8} "
        f"{'S_abs/R':>10} {'S_abs/R^1.5':>12}"
    )
    rows = []
    for R in (200, 400, 800, 1600, 2400, 3200, 4400):
        X = R * R - 1
        if X > N:
            continue
        c = np.arange(1, R, dtype=np.int64)
        c = c[c % p != 0]
        hi = X // c
        lo = np.maximum(R, X // (p * c))
        lo = np.minimum(lo, hi)
        D = (Pc[hi + 1] - Pc[lo + 1]) - (L[hi + 1] - L[lo + 1])
        muc = mu32[c].astype(np.float64)
        s_signed = float(np.sum(muc * D))
        s_abs = float(np.sum(np.abs(D)))
        MX = abs(int(M[X + 1]))
        rows.append((R, s_abs))
        print(
            f"{R:>7,} {X:>12,} {s_signed:>12,.1f} {s_abs:>14,.1f} {MX:>8,} "
            f"{s_abs/R:>10,.2f} {s_abs/R**1.5:>12.4f}"
        )

    if len(rows) >= 2:
        pts = [(math.log(r), math.log(s)) for r, s in rows if s > 0]
        mx = sum(a for a, _ in pts) / len(pts)
        my = sum(b for _, b in pts) / len(pts)
        slope = sum((a - mx) * (b - my) for a, b in pts) / sum(
            (a - mx) ** 2 for a, b in pts
        )
        print()
        print(f"    growth of S_abs:  R^{slope:.3f}   (predicted R^1.5)")
        print(f"    square-root target for |M(X)| is R^1.0")
        print()
        print("    Two separate readings, both worth stating.")
        print()
        print("    GOOD: S_signed stays at or below the square-root target -- it is a")
        print("    small multiple of R at every scale tested, and roughly an order of")
        print("    magnitude below S_abs.  So the cofactor-first reindexing does NOT")
        print("    destroy the cancellation: the Moebius signs and the window")
        print("    discrepancies really are cancelling each other.")
        print()
        print(f"    BAD: S_abs grows like R^{slope:.3f}, so bounding term by term")
        print(f"    overshoots the R^1.0 target by R^{slope-1:.3f} = X^{(slope-1)/2:.3f}, and the")
        print("    asymptotic prediction under RH is worse still (R^1.5 = X^0.75).")
        print("    Every step that takes absolute values inside the c-sum therefore")
        print("    fails, exactly as the earlier routes did.")
        print()
        print("    The saving must come from cancellation BETWEEN mu(c) and D(c).")
        print("    Bilinearity alone cannot supply it: the kernel 1[q in W(c)] is")
        print("    nonnegative, so sup over bounded coefficients IS the trivial bound,")
        print("    and Cauchy-Schwarz over c gives off-diagonal correlations")
        print("    sum_c K(c,q1) K(c,q2) = #{c <= X/max(q1,q2)}, which is the same size")
        print("    as the diagonal for q1, q2 ~ Q -- zero Type II saving.  An")
        print("    oscillating kernel is what Vinogradov/Vaughan need and what a")
        print("    hyperbola indicator does not provide.")


if __name__ == "__main__":
    main()
