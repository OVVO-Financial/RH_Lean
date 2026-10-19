#!/usr/bin/env python3
"""Audit exact rational Mobius covariance / seven-eighths finite contract.

Finite evidence only; NEVER a substitute for the all-X quantifier in
VF919SevenEighthsSignedCovarianceBound.
"""
from math import sqrt


def sieve_mobius(n):
    least = [0] * (n + 1)
    mu = [0] * (n + 1)
    mu[1] = 1
    primes = []
    for v in range(2, n + 1):
        if not least[v]:
            least[v] = v
            mu[v] = -1
            primes.append(v)
        for p in primes:
            if p > least[v] or p * v > n:
                break
            least[p * v] = p
            if p == least[v]:
                mu[p * v] = 0
                break
            mu[p * v] = -mu[v]
    return mu


def audit():
    nmax = 1028**2 - 1
    mu = sieve_mobius(nmax)
    upm = lpm = k = m = c = 0
    record = {}
    cutoffs = {317, 1027, 317**2, 318**2 - 1, 1027**2, 1028**2 - 1}
    for x in range(1, nmax + 1):
        u = mu[x]
        # Each pair (i,x), i<x, contributes exactly once.
        c += u * m
        m += u
        upm += int(u > 0)
        lpm += int(u < 0)
        k += u * u
        assert upm - lpm == m
        assert upm + lpm == k
        assert 2 * c == m*m - k
        assert 4 * upm * lpm == k*k - m*m
        # Integer arithmetic certificate for M(X)^2 <= X^(7/4).
        assert m**8 <= x**7, (x, m)
        if x in cutoffs:
            rho = 2 * c / (k * (k - 1)) if k > 1 else float("nan")
            record[x] = upm, lpm, k, m, c, rho, m*m / x**1.75
    assert record[317][:5] == (95, 99, 194, -4, -89)
    assert record[1027][:5] == (311, 314, 625, -3, -308)
    assert record[318**2 - 1][3] - record[317**2][3] == 11
    assert record[1028**2 - 1][3] - record[1027**2][3] == -20
    for x in sorted(record):
        u, l, k, m, c, rho, score = record[x]
        print(f"X={x:7d} UPM={u:7d} LPM={l:7d} K={k:7d} M={m:5d} "
              f"C={c:10d} 2C={2*c:10d} rho={rho:+.9f} "
              f"M2/X^(7/4)={score:.9g}")
    print(f"PASS exact finite census for every X<= {nmax} "
          f"with M(X)^8 <= X^7")


if __name__ == "__main__":
    audit()
