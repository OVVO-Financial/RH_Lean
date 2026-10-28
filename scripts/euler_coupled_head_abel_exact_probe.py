#!/usr/bin/env python3
"""Exact rational source-fidelity probe for PR #1041's full q-Abel head.

All multiplications, floor boundaries, and divisor punctures use integers.
Every rational phase and signed intermediate total uses fractions.Fraction.
No asymptotic cancellation or RH theorem is inferred from these tests.
"""
from fractions import Fraction
from math import isqrt


def mobius_up_to(n: int) -> list[int]:
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if prime[p]:
            for k in range(p, n + 1, p):
                mu[k] *= -1
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
                prime[k] = False
    return mu


def verify_root(R: int) -> tuple[int, int, list[Fraction]]:
    N, L = R - 1, R + 1
    X = R * R - 1
    H = isqrt(R)
    B = N - H
    Q = next(q for q in range(1, N + 1) if q * (q + 1) >= N)
    mu = mobius_up_to(N)
    M = [0] * (N + 1)
    for n in range(1, N + 1):
        M[n] = M[n - 1] + mu[n]

    sums = [Fraction(0) for _ in range(6)]
    for b in range(1, max(0, B) + 1):
        if mu[b] == 0:
            continue
        Y = X // b

        def r(q: int) -> int:
            return N // q

        def A(q: int) -> int:
            return Y // r(q)

        def E(q: int) -> Fraction:
            return Fraction(A(q)) - Fraction(L * q, b)

        endpoints = E(1) * M[N] - E(Q) * M[r(Q)]
        window = sum(M[Y // m] for m in range(A(1) + 1, A(Q) + 1))
        drift = -Fraction(L, b) * sum(M[r(q + 1)] for q in range(1, Q))
        puncture = -sum(
            E(q) * mu[N // q] for q in range(1, Q) if N % q == 0
        )
        small_a = sum(
            (
                mu[a]
                * (Fraction(X // (a * b)) - Fraction(L * (N // a), b))
                for a in range(1, r(Q) + 1)
                if N % a != 0
            ),
            Fraction(0),
        )
        original = sum(
            (
                mu[a]
                * (Fraction(X // (a * b)) - Fraction(L * (N // a), b))
                for a in range(1, N + 1)
                if N % a != 0
            ),
            Fraction(0),
        )
        components = [endpoints, Fraction(window), drift, puncture, small_a]
        assert sum(components) == original, (R, b, Q, components, original)
        for j, component in enumerate(components + [original]):
            sums[j] += mu[b] * component

    assert sum(sums[:5]) == sums[5]
    return Q, B, sums


if __name__ == "__main__":
    print("R Q B endpoint window smooth_drift punched small_a complete")
    for R in (3, 9, 15, 31, 56, 100, 317, 500, 1000):
        Q, B, v = verify_root(R)
        print(R, Q, B, *(f"{float(z):.6f}" for z in v))
    print("PASS exact original Möbius source = fully coupled Abel head + small-a tail")
