#!/usr/bin/env python3
"""Actual-prime verification of the complete Alpoge Gz/NNS future-tail bound.

This checks the *original* weighted prime-power Gz formula independently
of the NNS Chebyshev-error tail calculation, with the harmonic collar.
Numerics are not evidence of a uniform RH-strength exponent.
"""
from math import fsum, log

EULER_GAMMA = 0.577215664901532860606512090082402431


def von_mangoldt(n: int) -> float:
    if n <= 1:
        return 0.0
    k = n
    p = 2
    while p * p <= k:
        if k % p == 0:
            while k % p == 0:
                k //= p
            return log(p) if k == 1 else 0.0
        p += 1
    return log(k)


def build(limit: int):
    lam = [0.0] + [von_mangoldt(i) for i in range(1, limit + 1)]
    psi = [0.0] * (limit + 1)
    harmonic = [0.0] * (limit + 1)
    for n in range(1, limit + 1):
        psi[n] = fsum((psi[n - 1], lam[n]))
        harmonic[n] = fsum((harmonic[n - 1], 1.0 / n))
    err = [0.0] * (limit + 1)
    for n in range(1, limit + 1):
        err[n] = (psi[n] - n) / (n * (n + 1))
    return lam, psi, harmonic, err


def test_pair(n, m, lam, harmonic, err):
    def physical_gz(k):
        # Exact original Sz(k): final k-th prime-power term vanishes.
        sz = fsum(lam[d] * (k / d - 1.0) for d in range(1, k + 1))
        return sz - k * log(k) + (1.0 + EULER_GAMMA) * k

    g_n = physical_gz(n)
    g_m = physical_gz(m)

    upper = fsum(max(err[k], 0.0) for k in range(n, m))
    lower = fsum(max(-err[k], 0.0) for k in range(n, m))
    tail = upper - lower
    def collar(k):
        return harmonic[k] - log(k) - EULER_GAMMA

    assert -1e-10 <= collar(n) <= 1 / n + 1e-10
    assert -1e-10 <= collar(m) <= 1 / m + 1e-10

    lhs = g_n / n
    rhs = g_m / m - tail + collar(n) - collar(m)
    residual = abs(lhs - rhs)
    assert residual < 3e-8, (n, m, residual)

    bound = n * (g_m / m - tail) + 1
    assert g_n <= bound + 3e-8, (n, m, g_n, bound)

    # Exact if-and-only-if criterion for arbitrary B, both true & false.
    for b in (g_n + 0.12, g_n - 0.12):
        x = g_n <= b
        y = tail >= g_m / m + collar(n) - collar(m) - b / n
        assert x == y, (n, m, b, x, y)

    return residual, bound - g_n, tail


def main():
    lam, psi, harmonic, err = build(4096)
    tests = [
        (1, 2), (2, 49), (19, 250), (317, 1027),
        (549, 1098), (999, 2000), (1027, 4096),
    ]
    for n, m in tests:
        residual, margin, signed_tail = test_pair(
            n, m, lam, harmonic, err
        )
        print(f"N={n:4d} M={m:4d} residual={residual:.2e} "
              f"margin={margin:.8f} signed_tail={signed_tail:+.8f}")
    print("PASS: all actual-prime Gz/NNS future-tail identities and one-unit bounds")


if __name__ == "__main__":
    main()
