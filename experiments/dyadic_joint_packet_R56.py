#!/usr/bin/env python3
"""Exact R=56 regression for the top-annulus smooth/high joint packet.

Checks only finite identities:
  * M(X) equals the odd dyadic annulus mass on X/2 < m <= X;
  * that annulus splits into P+(m) <= R and P+(m) > R pieces;
  * the high shell mass equals the existing dyadic transport source formula;
  * the paper transport orientation is the negative of that source mass.

No asymptotic or contraction claim is made.
"""

R = 56
X = R * R - 1


def sieve(nmax):
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

    mertens = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    return mu, largest, primes, mertens


mu, largest, primes, mertens = sieve(X)

annulus = [
    m for m in range(1, X + 1)
    if m % 2 == 1 and X < 2 * m
]
smooth = [m for m in annulus if largest[m] <= R]
high = [m for m in annulus if R < largest[m]]

annulus_mass = sum(mu[m] for m in annulus)
smooth_mass = sum(mu[m] for m in smooth)
high_mass = sum(mu[m] for m in high)

assert annulus_mass == mertens[X]
assert smooth_mass + high_mass == annulus_mass

# Existing dyadicCanonicalHighSourceMass:
# sum_{R<q<=X, q prime} sum_{c in dyadicBoundary(X/q)} mu(c*q).
dyadic_high_source_mass = 0
paper_transport_boundary_mass = 0
for q in primes:
    if not (R < q <= X):
        continue
    B = X // q
    for c in range(1, B + 1):
        if c % 2 == 1 and B < 2 * c:
            dyadic_high_source_mass += mu[c * q]
            paper_transport_boundary_mass += mu[c]

assert dyadic_high_source_mass == high_mass
assert paper_transport_boundary_mass == -dyadic_high_source_mass

# Locked finite witness for the first production root.
assert mertens[X] == 6
assert smooth_mass == -41
assert high_mass == 47
assert paper_transport_boundary_mass == -47

print("R =", R, "X =", X)
print("M(X) / top odd annulus =", annulus_mass)
print("smooth top-annulus mass =", smooth_mass)
print("high top-annulus source mass =", high_mass)
print("paper transport boundary mass =", paper_transport_boundary_mass)
print("PASS: -41 + 47 = 6, and transport orientation is -47.")
