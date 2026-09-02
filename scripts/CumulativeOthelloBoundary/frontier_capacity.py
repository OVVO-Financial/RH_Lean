#!/usr/bin/env python3
"""Capacity diagnostics for the covariance route.

Three numbers are printed per scale, and the gap between them is the whole
remaining problem.

1.  **The actual global covariance.**  With
    ``C(x+1) = sum_{1<=a<b<=x} mu(a) mu(b)`` and ``Z(x) = #{n<=x : mu(n)=0}``,
    the exact square expansion gives ``|M(x)|^2 = x - Z(x) + 2 C(x+1)``, so
    ``C(x+1) = (M(x)^2 - x + Z(x)) / 2``.  This is what the route must bound.

2.  **The two thresholds, which must not be conflated.**  Crossing the literal
    ``sqrt x`` line is ``C(x+1) > Z(x)/2 ~ 0.196 x``; that is the threshold of
    the *false* Mertens conjecture and is not a provable target.  The RH
    threshold is the weaker ``C(x) <= x^(1+o(1))``, and an RH-violating
    excursion of exponent ``eps`` needs ``C(x+1) ~ x^(1+2 eps)/2``.

3.  **What the support-only Euler frontier bound currently allows.**  The
    first-failure frontier at pivot ``ell`` is
    ``{n <= X : n squarefree, ell does not divide n, X < ell n}``.  Lean proves
    ``|M(X)| <= F(X, ell)``, hence a covariance capacity ``F (F-1) / 2``.  The
    minimising pivot is ``ell = 2``, whose frontier is the squarefree part of
    the top-half window ``(X/2, X]`` -- the same set as the ``ell = 2`` cutoff
    wall of `PrefixCarrierOthelloWalls` -- and its density tends to ``2/pi^2``.

    python3 scripts/CumulativeOthelloBoundary/frontier_capacity.py [xmax]
"""

from __future__ import annotations

import sys


def moebius_sieve(n_max: int) -> list[int]:
    spf = list(range(n_max + 1))
    primes: list[int] = []
    for i in range(2, n_max + 1):
        if spf[i] == i:
            primes.append(i)
        for p in primes:
            if p > spf[i] or i * p > n_max:
                break
            spf[i * p] = p
    mu = [1] * (n_max + 1)
    mu[0] = 0
    for n in range(2, n_max + 1):
        p = spf[n]
        m = n // p
        mu[n] = 0 if m % p == 0 else -mu[m]
    return mu


def frontier_card(x: int, ell: int, mu: list[int]) -> int:
    """#{n <= x : mu n != 0, ell does not divide n, x < ell * n}."""
    return sum(1 for n in range(x // ell + 1, x + 1) if mu[n] and n % ell)


def report(x: int, mu: list[int]) -> None:
    mertens = sum(mu[1:x + 1])
    zeros = sum(1 for n in range(1, x + 1) if mu[n] == 0)
    squarefree = x - zeros
    covariance = (mertens * mertens - squarefree) / 2
    print(f"x = {x}")
    print(f"  M(x) = {mertens}      sqrt(x) = {x ** 0.5:.1f}"
          f"      x - Z(x) = {squarefree}")
    print(f"  actual C(x+1) = (M^2 - (x - Z)) / 2 = {covariance:.4g}"
          f"   = {covariance / x:.4f} x")
    print(f"  Mertens-conjecture threshold Z(x)/2 = {zeros / 2:.4g}"
          f"   = {zeros / (2 * x):.4f} x   (false conjecture, not a target)")
    print(f"  RH target                            C(x) <= x^(1+eps)"
          f"   ~ {x:.4g}")
    for ell in (2, 3, 5):
        f_card = frontier_card(x, ell, mu)
        capacity = f_card * (f_card - 1) / 2
        print(f"  frontier ell={ell:>2}: F = {f_card:>8}"
              f"  F/x = {f_card / x:.5f}"
              f"  F/sqrt(x) = {f_card / x ** 0.5:8.1f}"
              f"  capacity F(F-1)/2 = {capacity:.4g} = {capacity / x:.1f} x")
    print()


def main(argv: list[str]) -> int:
    x_max = int(argv[1]) if len(argv) > 1 else 200_000
    mu = moebius_sieve(x_max)
    for x in (x_max // 100, x_max // 10, x_max):
        if x >= 100:
            report(x, mu)
    print("Readings:")
    print("  * the minimising frontier is linear in x (F/x -> 2/pi^2 = 0.20264),")
    print("    so its capacity is of order x^2 -- a full power above the RH")
    print("    target x^(1+eps).  Support exhaustion alone cannot close this;")
    print("  * F/sqrt(x) grows, so the frontier is nowhere near square-root size,")
    print("    which is the hypothesis PrimeProductFrontierRootScaleStatement asks")
    print("    for and which this measurement refutes for the raw prime cube;")
    print("  * the actual global covariance is strongly negative, far below every")
    print("    threshold.  The problem is not the true value, it is that no")
    print("    theorem yet bounds it -- and the frontier bound bounds a different")
    print("    object until the domination arrow is proved.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
