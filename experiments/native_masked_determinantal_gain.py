#!/usr/bin/env python3
"""Exact integer checks of the masked diagonal determinantal divisor.

Enumerate the actual nonzero minors, separately compute the prime-power
count formula, and compare. No floating-point arithmetic and no RH claim.
"""
from itertools import combinations
from math import gcd, prod

PRIMES = (2, 3, 5, 7, 11)


def masks(A, primes, include):
    result = {}
    for p in primes:
        i, power = 1, p
        while power <= A:
            if include(p, i):
                result.setdefault(p, []).append(i)
            i += 1
            power *= p
    return result


def actual_minor_gcd(A, w, mask):
    diagonal = [
        prod(p ** sum(n % p**i == 0 for i in I) for p, I in mask.items())
        for n in range(1, A + 1)
    ]
    g = 0
    for subset in combinations(diagonal, A - w):
        g = gcd(g, prod(subset))
    return g


def predicted_minor_gcd(A, w, mask):
    return prod(
        p ** sum(max(A // p**i - w, 0) for i in I)
        for p, I in mask.items()
    )


def main():
    count = 0
    for A in range(1, 13):
        for w in range(A + 1):
            for primes in (PRIMES, (2, 5), (3, 7), ()):
                for odd in (False, True):
                    I = masks(A, primes, lambda p, i: not odd or i % 2 == 1)
                    assert actual_minor_gcd(A, w, I) == predicted_minor_gcd(A, w, I)
                    count += 1
            for include in (
                lambda p, i: True,
                lambda p, i: i % 2 == 1,
                lambda p, i: (p + i) % 3 != 0,
                lambda p, i: i % 2 == 0,
            ):
                I = masks(A, PRIMES, include)
                assert actual_minor_gcd(A, w, I) == predicted_minor_gcd(A, w, I)
                count += 1
    assert count == 1080
    print(f"{count} exact integer determinantal-divisor checks passed")


if __name__ == "__main__":
    main()
