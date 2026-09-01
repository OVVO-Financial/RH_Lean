#!/usr/bin/env python3
"""Finite diagnostic for the cumulative Othello boundary route.

Two things are measured, on the prefix carrier ``(0, x]``.

1.  **Invariance of the signed mass under a peel.**  The Lean theorem
    ``RHLean.Proof.sum_moebius_eq_sum_iteratedPrimeEscapePart`` says that
    peeling a distinguished prime leaves the signed Moebius mass unchanged.
    Every row below reprints that mass; it must never move.

2.  **Population of the iterated boundary.**  This is the quantity the open
    multiplicity target ``IteratedPrefixBoundaryBoundedStatement`` has to bound
    by ``x^(1/2+eps)``.  The measurement is the stop criterion of the route: a
    peel order whose boundary stays a fixed positive proportion of ``x`` cannot
    reach RH scale, however many primes are peeled.

The peel used here is the naive increasing one, ``p = 2, 3, 5, ...``, applied
to one fixed carrier.  Run this before proposing any peel-order refinement.

    python3 scripts/CumulativeOthelloBoundary/peel_diagnostic.py [xmax]
"""

from __future__ import annotations

import sys


def mobius_sieve(n_max: int) -> list[int]:
    """Linear sieve for the Moebius function on ``[0, n_max]``."""
    mu = [1] * (n_max + 1)
    mu[0] = 0
    primes: list[int] = []
    composite = [False] * (n_max + 1)
    for i in range(2, n_max + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n_max:
                break
            composite[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def toggle(p: int, n: int) -> int:
    """The carrier toggle of `RHLean.Proof.primeCarrierToggle`."""
    if n % (p * p) == 0:
        return n
    if n % p == 0:
        return n // p
    return n * p


def peel(carrier: set[int], p: int) -> set[int]:
    """The Othello boundary: sites whose `p`-mate has left the carrier."""
    return {n for n in carrier if toggle(p, n) not in carrier}


def report(x: int, primes: list[int], mu: list[int]) -> None:
    carrier = set(range(1, x + 1))
    mass = sum(mu[n] for n in carrier)
    print(f"x={x:>8}  M(x)={mass:>7}  sqrt(x)={x ** 0.5:9.1f}")
    for p in primes:
        carrier = peel(carrier, p)
        peeled_mass = sum(mu[n] for n in carrier)
        flag = "" if peeled_mass == mass else "   <-- MASS MOVED, THEOREM VIOLATED"
        print(
            f"    peel p={p:>3}: |boundary|={len(carrier):>9}"
            f"  |boundary|/x={len(carrier) / x:8.5f}"
            f"  mass={peeled_mass:>7}{flag}"
        )


def main(argv: list[str]) -> int:
    x_max = int(argv[1]) if len(argv) > 1 else 200_000
    primes = [2, 3, 5, 7, 11, 13, 17, 19]
    # A peel can multiply a site by at most the largest peeled prime.
    mu = mobius_sieve(x_max * max(primes) + 1)
    for x in (x_max // 100, x_max // 10, x_max):
        if x >= 100:
            report(x, primes, mu)
    print()
    print("Limit of the naive peel on a fixed carrier: 2/pi^2 = "
          f"{2 / 3.141592653589793 ** 2:.5f} of x.")
    print("That is a fixed proportion, not x^(1/2+eps): the peel order is not")
    print("the free parameter.  The free parameter is the carrier itself, via")
    print("RHLean.Proof.sum_moebius_eq_neg_sdiff_of_toggleClosed.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
