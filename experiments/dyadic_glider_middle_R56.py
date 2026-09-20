#!/usr/bin/env python3
"""Exact R=56 regression for the dyadic Othello/glider-wall split.

This checks:
  * M(3135) = 6;
  * the inert top-prime block has 198 primes;
  * the intermediate prime Mertens tail is -245;
  * the complete R-smooth mass is -41;
  * the exact active-middle residual is -6 = -M(3135).

No asymptotic estimate is used.
"""

import math

R = 56
X = R * R - 1


def mobius_sieve(nmax):
    lp = [0] * (nmax + 1)
    mu = [0] * (nmax + 1)
    mu[1] = 1
    primes = []
    for n in range(2, nmax + 1):
        if lp[n] == 0:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p > lp[n] or n * p > nmax:
                break
            lp[n * p] = p
            if p == lp[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]

    largest = [0] * (nmax + 1)
    for p in primes:
        for m in range(p, nmax + 1, p):
            largest[m] = p
    largest[1] = 1

    mertens = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        mertens[n] = mertens[n - 1] + mu[n]

    return mu, largest, primes, mertens


mu, largest, primes, mertens = mobius_sieve(X)

middle_primes = [q for q in primes if R < q <= X // 2]
top_primes = [q for q in primes if X // 2 < q <= X]

middle_tail = sum(mertens[X // q] for q in middle_primes)
smooth_mass = sum(
    mu[n] for n in range(1, X + 1)
    if largest[n] <= R
)
known_edge_mass = smooth_mass - len(top_primes)
middle_residual = middle_tail - known_edge_mass

assert X == 3135
assert mertens[X] == 6
assert len(top_primes) == 198
assert len(middle_primes) == 231
assert middle_tail == -245
assert smooth_mass == -41
assert known_edge_mass == -239
assert middle_residual == -6
assert middle_residual == -mertens[X]

# Prime-two Othello wall and its iterated odd-prime escape boundary.
def carrier_toggle(p, n):
    if n % (p * p) == 0:
        return n
    if n % p == 0:
        return n // p
    return n * p


def escape_part(p, carrier):
    return {n for n in carrier if carrier_toggle(p, n) not in carrier}


dyadic_wall = {
    n for n in range(1, X + 1)
    if n % 2 == 1 and X < 2 * n
}
assert len(dyadic_wall) == 784
assert sum(mu[n] for n in dyadic_wall) == mertens[X]

glider_boundary = set(dyadic_wall)
for p in [q for q in primes if 3 <= q <= R]:
    glider_boundary = escape_part(p, glider_boundary)

assert len(glider_boundary) == 634
assert sum(mu[n] for n in glider_boundary) == mertens[X]

print("R =", R, "X =", X)
print("M(X) =", mertens[X])
print("middle prime count =", len(middle_primes))
print("top prime count =", len(top_primes))
print("middle Mertens tail =", middle_tail)
print("complete smooth mass =", smooth_mass)
print("known edge mass =", known_edge_mass)
print("active-middle residual =", middle_residual)
print("prime-2 dyadic wall card =", len(dyadic_wall))
print("iterated glider-boundary card =", len(glider_boundary))
print("iterated glider-boundary mass =", sum(mu[n] for n in glider_boundary))
print("PASS: active middle leaves -6 = -M(3135), not zero;")
print("      Othello preserves mass 6 while moving it onto explicit escape walls.")
