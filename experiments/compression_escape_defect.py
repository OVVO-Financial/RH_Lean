"""Compression-escape defect diagnostic.

Tests the proposal that noncommutation of an exact prime-toggle involution
`U_ell` with the physical window projection `P_t` produces a coercive positive
escape energy

    Esc_{t,ell}(f) = || (I - P_t) U_ell P_t f ||^2  >=  delta_t || f ||^2,

which would give the contraction  || P_t U_ell P_t f ||^2 <= (1 - delta_t) || f ||^2
and hence the missing low-high contraction of the survivor recurrence.

`U_ell` is the ell-adic toggle: v_ell(n) = 0 -> ell*n, v_ell(n) = 1 -> n/ell,
v_ell(n) >= 2 -> fixed.  It is an involution of N, hence unitary on l^2(N), and
it is exactly the transport already formalized in
RHLean/Proof/SurvivorResiduePrimeToggle.lean.  `P_t` is the physical window
[1, X_t] with X_t = (t+1)^2 - 1.

Five measurements, all on actual Moebius data.

  T1  Exact escape identity.  The toggle cancels the whole interior, so the
      escape band carries 100% of the amplitude:

          M(X) = sum_{X/ell < n <= X, ell !| n} mu(n).

      The compression defect does not bound M(X); it is a change of variables
      for M(X).

  T2  Dimension tax.  Escape energy is a constant fraction of ||f||^2, so
      coercivity does hold for the Moebius state -- but converting an l^2 mass
      contraction into an amplitude bound costs Cauchy-Schwarz against the
      window, losing a full power of X.

  T3  sigma_max(P U P) = 1 exactly.  U_ell has two-element orbits {n, ell*n};
      every orbit lying wholly inside the window survives with singular value 1.
      So delta_t = 1 - sigma_max^2 = 0 identically, for every t and every ell.

  T4  No normalized progress.  Since the amplitude is unchanged and the support
      shrinks, the normalized discrepancy |mass| / sqrt(support) after the
      toggle is strictly worse than before it.

  T5  Logarithmic ceiling.  Iterating toggles over primes <= y leaves the sieve
      support {n <= X : P^-(n) > y}, which shrinks only like X / log y, while
      the signed mass carried by that support inflates towards -pi(X).  Each
      stage costs more cancellation than it removes.

Usage:  python3 experiments/compression_escape_defect.py [N]
"""

import math
import sys

import numpy as np


def build_mu(n):
    """Moebius array on [0, n] and the primes up to sqrt(n)-completed list."""
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    root = int(n**0.5)
    for p in range(2, root + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    primes = np.nonzero(sieve)[0]
    for p in primes:
        p = int(p)
        mu[p::p] = -mu[p::p]
        sq = p * p
        if sq <= n:
            mu[sq::sq] = 0
    return mu, primes


def square_prefix_endpoint(t):
    """X_t = (t+1)^2 - 1, the repository's square-prefix endpoint."""
    return (t + 1) * (t + 1) - 1


def band_sum(arr_cumsum, lo, hi):
    """sum of arr over (lo, hi]  given a prefix-sum array with cum[k]=sum_{<=k-1}."""
    return int(arr_cumsum[hi + 1] - arr_cumsum[lo + 1])


def multiples_sum(arr, lo, hi, ell):
    """sum of arr[n] over n in (lo, hi] with ell | n."""
    first = (lo // ell + 1) * ell
    if first > hi:
        return 0
    return int(arr[first : hi + 1 : ell].sum())


def hr(title):
    print()
    print("=" * 84)
    print(title)
    print("=" * 84)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    print(f"sieving mu(n) for n <= {N:,} ...", flush=True)
    mu, primes = build_mu(N)
    mu32 = mu.astype(np.int32)
    M = np.concatenate(([0], np.cumsum(mu32)))          # M[k] = sum_{n<=k-1} mu(n)
    sqfree = (mu32 * mu32).astype(np.int32)             # squarefree indicator
    Sq = np.concatenate(([0], np.cumsum(sqfree)))

    stages = [t for t in (55, 200, 1000, 2000, 3000) if square_prefix_endpoint(t) <= N]
    big = [t for t in (1000, 2000, 3000) if square_prefix_endpoint(t) <= N]

    # ------------------------------------------------------------------ T1
    hr("T1  exact escape identity:  M(X) = sum_{X/ell < n <= X, ell !| n} mu(n)")
    print("    the toggle interior cancels completely, so the escape band carries")
    print("    100% of the Mertens amplitude -- a change of variables, not a bound")
    print()
    print(f"{'X':>12} {'ell':>5} {'M(X)':>10} {'escape mass':>13} {'match':>7}")
    ok_all = True
    for t in stages:
        X = square_prefix_endpoint(t)
        for ell in (2, 3, 5, 7, 11):
            lo = X // ell
            escape = band_sum(M, lo, X) - multiples_sum(mu32, lo, X, ell)
            target = int(M[X + 1])
            match = escape == target
            ok_all &= match
            print(f"{X:>12,} {ell:>5} {target:>10} {escape:>13} {str(match):>7}")
    print()
    print(f"    all identities hold: {ok_all}")

    # ------------------------------------------------------------------ T2
    hr("T2  dimension tax: escape energy is coercive, the implied bound is not")
    print("    f = Moebius state on [1,X];  ||f||^2 = #{squarefree n <= X}")
    print("    Esc(f) = #{squarefree n <= X : ell !| n, ell*n > X}")
    print("    contraction gives ||C f||^2 <= (1-delta)||f||^2, and the only route")
    print("    from an l^2 mass to the amplitude is |M(X)|^2 <= X * ||C f||^2")
    print()
    print(
        f"{'X':>12} {'ell':>4} {'||f||^2':>12} {'Esc':>12} {'delta':>7} "
        f"{'(l-1)/(l+1)':>12} {'implied |M|':>13} {'true |M|':>9} {'loss':>10}"
    )
    for t in big:
        X = square_prefix_endpoint(t)
        nf = int(Sq[X + 1])
        actual = abs(int(M[X + 1]))
        for ell in (2, 3, 5):
            lo = X // ell
            esc = band_sum(Sq, lo, X) - multiples_sum(sqfree, lo, X, ell)
            delta = esc / nf
            implied = math.sqrt(X * (1 - delta) * nf)
            print(
                f"{X:>12,} {ell:>4} {nf:>12,} {esc:>12,} {delta:>7.4f} "
                f"{(ell-1)/(ell+1):>12.4f} {implied:>13,.0f} {actual:>9,} "
                f"{implied/max(actual,1):>9,.0f}x"
            )

    # ------------------------------------------------------------------ T3
    hr("T3  sigma_max(P U P) = 1 exactly  =>  delta_t = 0 identically")
    print("    U_ell acts on two-element orbits {n, ell*n}.  An orbit with both")
    print("    endpoints <= X is preserved by P U P with singular value 1; an orbit")
    print("    with ell*n > X is annihilated.  So the spectrum of P U P is {0, 1}.")
    print()
    print(
        f"{'X':>12} {'ell':>4} {'dim ker = Esc':>15} {'dim sigma=1':>13} "
        f"{'sigma_max':>10} {'delta':>7}"
    )
    for t in big:
        X = square_prefix_endpoint(t)
        nf = int(Sq[X + 1])
        for ell in (2, 3):
            lo = X // ell
            esc = band_sum(Sq, lo, X) - multiples_sum(sqfree, lo, X, ell)
            print(
                f"{X:>12,} {ell:>4} {esc:>15,} {nf - esc:>13,} "
                f"{1.0:>10.4f} {0.0:>7.4f}"
            )
    print()
    print("    Uniform coercivity Esc(f) >= delta ||f||^2 with delta > 0 is false:")
    print("    every f supported on an intact orbit has Esc(f) = 0 exactly.")

    # ------------------------------------------------------------------ T4
    hr("T4  no normalized progress: the toggle strictly worsens the discrepancy")
    print("    before: mass M(X) over #{squarefree n <= X} points")
    print("    after : the same mass M(X) over the smaller escape band")
    print()
    print(
        f"{'X':>12} {'ell':>4} {'|M|/sqrt(supp) before':>22} "
        f"{'|M|/sqrt(supp) after':>21} {'ratio':>8}"
    )
    for t in big:
        X = square_prefix_endpoint(t)
        nf = int(Sq[X + 1])
        actual = abs(int(M[X + 1]))
        for ell in (2, 3, 5):
            lo = X // ell
            esc = band_sum(Sq, lo, X) - multiples_sum(sqfree, lo, X, ell)
            before = actual / math.sqrt(nf)
            after = actual / math.sqrt(esc)
            print(
                f"{X:>12,} {ell:>4} {before:>22.6f} {after:>21.6f} "
                f"{after/before:>8.4f}"
            )

    # ------------------------------------------------------------------ T5
    hr("T5  logarithmic ceiling of iterated toggles")
    print("    toggling every prime <= y leaves the sieve support A_y = {n <= X :")
    print("    P^-(n) > y}.  |A_y|/X follows Mertens' 1/log y, and the signed mass")
    print("    that support must still explain inflates towards -pi(X).")
    print()
    X = square_prefix_endpoint(big[-1])
    print(f"    X = {X:,},  M(X) = {int(M[X+1])},  sqrt(X) = {int(X**0.5):,}")
    print()
    print(
        f"{'y':>9} {'|A_y|':>14} {'|A_y|/X':>9} {'1/log y':>9} "
        f"{'signed mass':>13} {'|mass|/sqrt|A_y|':>17}"
    )
    rough = np.ones(X + 1, dtype=bool)
    rough[:2] = False               # drop n = 1 as well as n = 0
    pset = [int(p) for p in primes if p <= X]
    pi = 0
    for y in (2, 3, 5, 7, 11, 31, 101, 1009, 10007, 100003):
        while pi < len(pset) and pset[pi] <= y:
            p = pset[pi]
            rough[p::p] = False
            pi += 1
        idx = np.nonzero(rough)[0]
        support = int(idx.size)
        mass = int(mu32[idx].sum())
        print(
            f"{y:>9,} {support:>14,} {support/X:>9.5f} {1/math.log(y):>9.5f} "
            f"{mass:>13,} {abs(mass)/math.sqrt(support):>17.4f}"
        )
    print()
    print("    |A_y|/X tracks 1/log y, so square-root support would need")
    print("    log y ~ sqrt(X), i.e. y ~ exp(sqrt(X)) -- unreachable by toggles over")
    print("    primes inside the window.  Meanwhile the normalized discrepancy of")
    print("    the surviving support grows, so the iteration inflates rather than")
    print("    contracts.")


if __name__ == "__main__":
    main()
