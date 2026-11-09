#!/usr/bin/env python3
"""Exact four-prime fixed-coordinate square-block certificate.

The only wheel coordinates are 2,3,5,7. Outside primes appear solely in
the actual Mobius regression, never as additional wheel coordinates.
"""
import math
from fractions import Fraction

P = (2, 3, 5, 7)
PERIOD = 44100

def parity(n):
    ans = 1
    for p in P:
        if n % p == 0:
            ans = -ans
    return ans

def squarekill(n):
    ans = 1
    for p in P:
        if n % (p * p) == 0:
            return 0
        if n % p == 0:
            ans = -ans
    return ans

prefix = [0]
for n in range(1, PERIOD + 1):
    prefix.append(prefix[-1] + squarekill(n))
parity_prefix = [0]
for n in range(1, 211):
    parity_prefix.append(parity_prefix[-1] + parity(n))
assert prefix[PERIOD] == 2304
assert parity_prefix[210] == 0
assert Fraction(prefix[PERIOD], PERIOD) == Fraction(64, 1225)

errors = [1225 * prefix[n] - 64 * n for n in range(PERIOD + 1)]
assert min(errors) == -14364 and max(errors) == 14428
assert (min(parity_prefix), max(parity_prefix)) == (-7, 6)

def G(n):
    return (n // PERIOD) * prefix[PERIOD] + prefix[n % PERIOD]

def PG(n):
    return parity_prefix[n % 210]

def block(R):
    return G((R + 1) ** 2 - 1) - G(R * R - 1)

def parity_block(R):
    return PG((R + 1) ** 2 - 1) - PG(R * R - 1)

assert max(abs(parity_block(R)) for R in range(1, 211)) == 13
assert all(-28792 <= 1225 * block(R) - 64 * (2 * R + 1) <= 28792
           for R in range(1, PERIOD + 1))
assert all(block(R) > 0 for R in range(103, 103 + PERIOD))
assert max(R for R in range(1, 103) if block(R) <= 0) == 102
for t in (0, 1, 2, 3, 10, 100, 10000):
    assert block(PERIOD * t) == 4608 * t
for R in range(1, 1000):
    assert block(R + PERIOD) == block(R) + 4608
    assert parity_block(R + 210) == parity_block(R)
assert math.prod(Fraction(p - 1, p) for p in P) == Fraction(8, 35)

# Independently build true mu, retaining all higher prime signs.
N = 1_000_000
mu = [1] * (N + 1)
mu[0] = 0
isprime = bytearray([1]) * (N + 1)
isprime[0] = isprime[1] = 0
for p in range(2, math.isqrt(N) + 1):
    if isprime[p]:
        for n in range(p * p, N + 1, p):
            isprime[n] = 0
for p in range(2, N + 1):
    if isprime[p]:
        for n in range(p, N + 1, p):
            mu[n] *= -1
        if p * p <= N:
            for n in range(p * p, N + 1, p * p):
                mu[n] = 0

S = [0] * 211
for k in range(1, 211):
    S[k] = S[k - 1]
    if 210 % k == 0 and all(k % (r * r) for r in P):
        S[k] += parity(k)
assert S[210] == 0 and max(map(abs, S)) == 2

check = {R * R - 1 for R in (100, 225, 317, 549, 999)}
running = 0
for n in range(1, N + 1):
    running += mu[n]
    if n in check:
        reconstructed = sum(
            mu[m] * S[n // m]
            for m in range(n // 210 + 1, n + 1)
            if math.gcd(m, 210) == 1
        )
        assert reconstructed == running, (n, reconstructed, running)

# Actual physical square-block falsifier for universal negative return.
assert sum(mu[n] for n in range(137 * 137, 138 * 138)) == 44
assert block(137) == 2

print("PASS: parity-only 210 wheel has |every square block| <= 13")
print("PASS: physical four-prime wheel has mean 64/1225")
print("PASS: centred prefix 1225*G(x)-64*x in [-14364,14428]")
print("PASS: physical model square blocks are positive for all R>=103")
print("PASS: square block at R=44100*t is exactly 4608*t")
print("PASS: actual-Mobius 16-corner source reconstruction at 5 roots")
print("PASS: actual-Mobius R=137 block falsifies universal negative return")
