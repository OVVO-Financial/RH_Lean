#!/usr/bin/env python3
"""Exact regression of genuine (d, 2d, 4d) Mobius packets.

This script is finite verification, not a proof of an asymptotic estimate.
It uses integer/rational arithmetic and independently enumerates original
factor pairs. Run from the repository root with Python 3.10 or newer.
"""
from fractions import Fraction
from math import isqrt
import json


def mobius_sieve(limit: int) -> list[int]:
    if limit < 1:
        raise ValueError("The sieve limit must be positive")
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                prime[n] = False
                mu[n] = -mu[n]
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return mu


def completed_coefficients(limit: int, mu: list[int]) -> list[int]:
    """Enumerate actual strict unordered pairs, without a cubefree shortcut."""
    result = [0] * (limit + 1)
    for a in range(1, isqrt(limit) + 1):
        if mu[a]:
            for b in range(a + 1, limit // a + 1):
                result[a * b] += mu[a] * mu[b]
    return result


def fractional_column(root: int, modulus: int) -> Fraction:
    if root < 1 or modulus < 1:
        raise ValueError("Use positive physical roots and moduli")
    return Fraction((root * root - 1) % modulus, modulus)


def root_mean(modulus: int) -> Fraction:
    # Positive representatives avoid truncated natural subtraction at root 0.
    return Fraction(sum((r * r - 1) % modulus
                        for r in range(1, modulus + 1)), modulus * modulus)


def odd_part(n: int) -> int:
    if n < 1:
        raise ValueError("Odd part is used only for positive products")
    while n % 2 == 0:
        n //= 2
    return n


def main() -> None:
    limit = 1200
    mu = mobius_sieve(4 * limit)
    alpha = completed_coefficients(4 * limit, mu)
    f = fractional_column
    pointwise = 0
    for d in range(1, limit + 1, 2):
        k = isqrt(d)
        exception = mu[k] ** 2 if k * k == d else 0
        assert alpha[2 * d] == -2 * alpha[d] - exception, d
        assert alpha[4 * d] == alpha[d], d
        for root in [1, 2, 3, 7, 17, 33, 317, 1027, 4 * d + 1]:
            kernel = f(root, d) - 2 * f(root, 2 * d) + f(root, 4 * d)
            original = 2 * (alpha[d] * f(root, d)
                            + alpha[2 * d] * f(root, 2 * d)
                            + alpha[4 * d] * f(root, 4 * d))
            closed = 2 * alpha[d] * kernel - 2 * exception * f(root, 2 * d)
            assert original == closed, (d, root)
            pointwise += 1
    for d in range(1, 102, 2):
        assert root_mean(2 * d) == Fraction(1, 4) + root_mean(d) / 2
        uniform = lambda m: Fraction(m - 1, 2 * m)
        assert uniform(d) - 2 * uniform(2 * d) + uniform(4 * d) == Fraction(-1, 8 * d)

    cases = [(17, 3), (35, 8), (64, 15), (317, 17), (1027, 32)]
    for root, cutoff in cases:
        assert 4 * cutoff < root
        original = Fraction(0)
        for b in range(1, root):
            for a in range(1, b):
                if mu[a] and mu[b] and odd_part(a * b) <= cutoff:
                    original += 2 * mu[a] * mu[b] * f(root, a * b)
        reconstructed = sum((2 * (alpha[d] * f(root, d)
                                + alpha[2 * d] * f(root, 2 * d)
                                + alpha[4 * d] * f(root, 4 * d))
                             for d in range(1, cutoff + 1, 2)), Fraction(0))
        assert original == reconstructed, (root, cutoff)

    rows = []
    for height, cutoff in [(64, 8), (127, 11), (317, 17), (1027, 32)]:
        values = [sum((2 * (alpha[d] * f(root, d)
                           + alpha[2 * d] * f(root, 2 * d)
                           + alpha[4 * d] * f(root, 4 * d))
                       for d in range(1, cutoff + 1, 2)), Fraction(0))
                  for root in range(height, 2 * height)]
        principal = sum((2 * (alpha[d] * root_mean(d)
                              + alpha[2 * d] * root_mean(2 * d)
                              + alpha[4 * d] * root_mean(4 * d))
                         for d in range(1, cutoff + 1, 2)), Fraction(0))
        energy = sum((value * value for value in values), Fraction(0))
        rows.append({"H": height, "Q": cutoff, "energy": str(energy),
                     "principal": str(principal)})
    print(json.dumps({"odd_moduli": 600, "pointwise_checks": pointwise,
                      "source_pair_reconstructions": len(cases),
                      "period_mean_checks": 51, "rows": rows,
                      "scope": "FINITE EXACT REGRESSION; no global power claim"}, indent=2))


if __name__ == "__main__":
    main()
