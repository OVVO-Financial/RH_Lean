#!/usr/bin/env python3
"""Original Mobius regression for OAI 7/8 paid square-root nesting.

These are FINITE arithmetic regressions, not a proof of the uniform
asymptotic or any RH-strength bound. Exact Fractions retain q^-1 weights.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt


def mobius_prefix(n: int):
    mu = [0] * (n + 1)
    mu[1] = 1
    lp = [0] * (n + 1)
    primes = []
    for i in range(2, n + 1):
        if not lp[i]:
            lp[i] = i
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            lp[i * p] = p
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    M = [0] * (n + 1)
    for i in range(1, n + 1):
        M[i] = M[i - 1] + mu[i]
    return mu, M, primes


def validate(R: int, mu, M, primes):
    N = R - 1
    X = R * R - 1
    owners = [q for q in primes if q >= 3 and q * q < R]
    U, history, daughter = Fraction(0), Fraction(0), Fraction(0)
    daughter_energy = 0
    for q in owners:
        Y = X // (q * q)
        lower = isqrt(Y)
        root = lower if Y < lower * lower + lower else lower + 1
        endpoint = root * root - 1
        q_child = 2 * M[root - 1] - M[endpoint]
        U += Fraction(M[Y], q)
        history += Fraction(M[root - 1], q)
        daughter += Fraction(q_child, q)
        daughter_energy += q_child * q_child

    parent = 2 * M[N] - M[X]
    B = M[N] - M[X] - U
    Z = parent + daughter
    midpoint_shell = U - 2 * history + daughter
    assert B == Z - M[N] - 2 * history - midpoint_shell
    assert abs(B - Z) <= 3 * R
    assert daughter * daughter <= daughter_energy * Fraction(1, 4)
    lhs = Z * Z - Fraction(9, 4) * daughter_energy
    rhs = (Fraction(9, 8) * parent * parent
           - 8 * (daughter - Fraction(parent, 8)) ** 2
           - Fraction(9, 4) * (daughter_energy - 4 * daughter * daughter))
    assert lhs == rhs

    cutoff = max(2, isqrt(N))
    quotient_head = sum(M[N // q] for q in range(2, cutoff + 1))
    small_a = sum(mu[a] * (N // a) for a in range(1, N // cutoff + 1))
    assert quotient_head + small_a - cutoff * M[N // cutoff] == 1 - M[N]

    print(
        f"R={R} low-owners={len(owners)} "
        f"finiteC-parent={parent} "
        f"CORR4={float(B):.3f} nested={float(Z):.3f} "
        f"bridge-error={float(abs(B-Z)):.3f} "
        "hyperbola=OK square-reserve=OK"
    )


if __name__ == "__main__":
    roots = [56, 317, 1027]
    mu, M, primes = mobius_prefix(max(roots) ** 2)
    for root in roots:
        validate(root, mu, M, primes)
