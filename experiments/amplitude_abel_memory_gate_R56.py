#!/usr/bin/env python3
"""Exact finite diagnostic for the amplitude Abel pushforward gate at R=56.

This script mirrors the literal adaptive zero-factor chronology used by
AMPLITUDE_GLOBAL_PHYSICAL_DEFECT_LEDGER.lean. It is a regression test, not a
substitute for a Lean theorem.

The first assertion is the fidelity check: the prime-scaled physical-defect
ledger equals the compiled rough correlation M(R-1)-M(R^2-1). Only after that
check do we compare chronological Euler memory with the reciprocal low-q^2
Mertens daughter column.
"""

from bisect import bisect_right
from fractions import Fraction
from functools import lru_cache

R = 56
X = R * R - 1


def mobius_sieve(nmax: int):
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


mu, largest, primes, mertens = mobius_sieve(X)


@lru_cache(maxsize=None)
def partners(c: int):
    """Exact squareRootCanonicalRoughPrimePartnerSet membership at fixed R."""
    if c > X:
        return frozenset()
    lower = max(largest[c], (R - 1) // c)
    upper = X // c
    lo = bisect_right(primes, lower)
    hi = bisect_right(primes, upper)
    return frozenset(primes[lo:hi])


def adaptive_defect_ledgers():
    """Return (unscaled defect, prime-scaled defect) on the full chronology."""
    active = [False] * (X + 1)
    coeff = [0] * (X + 1)
    for n in range(1, X + 1):
        active[n] = True
        coeff[n] = 1

    unscaled = Fraction(0)
    scaled = Fraction(0)

    for p in reversed(primes):
        parents = [
            c for c in range(1, X // p + 1)
            if active[c] and largest[c] < p and active[c * p]
        ]

        defect = Fraction(0)
        for c in parents:
            parent_partners = partners(c)
            child_partners = partners(c * p)
            signed_boundary = (
                len(parent_partners - child_partners)
                - len(child_partners - parent_partners)
            )
            # b(c)=c*a(c) cancels c in mu(c)/(c*p).
            defect += Fraction(coeff[c] * mu[c] * signed_boundary, p)

        unscaled += defect
        scaled += p * defect

        for c in parents:
            active[c * p] = False
        for c in parents:
            coeff[c] = 0

    return unscaled, scaled


unscaled_defect, scaled_defect = adaptive_defect_ledgers()
rough_correlation = Fraction(mertens[R - 1] - mertens[X])

# Fidelity gate against amplitudeScaledPhysicalDefectLedger_eq_roughCorrelation.
assert rough_correlation == Fraction(-8)
assert scaled_defect == rough_correlation

low_q2_owners = [
    q for q in primes
    if q <= R - 1 and q != 2 and q * q < R
]
assert low_q2_owners == [3, 5, 7]

reciprocal_q2_column = sum(
    (Fraction(mertens[X // (q * q)], q) for q in low_q2_owners),
    Fraction(0),
)
assert reciprocal_q2_column == Fraction(34, 105)

euler_memory = scaled_defect - unscaled_defect
memory_gap = euler_memory - reciprocal_q2_column
physical_remainder = rough_correlation - reciprocal_q2_column

# Exact consistency with the canonical AMP bridge.
assert physical_remainder == unscaled_defect + memory_gap
assert physical_remainder == Fraction(-874, 105)

# The over-strong pure-defect pushforward would force both equalities.
assert euler_memory != reciprocal_q2_column
assert physical_remainder != unscaled_defect

print("R =", R, "X =", X)
print("M(R-1), M(X) =", mertens[R - 1], mertens[X])
print("scaled defect =", scaled_defect)
print("unscaled defect =", unscaled_defect, "~", float(unscaled_defect))
print("Euler memory =", euler_memory, "~", float(euler_memory))
print("reciprocal low-q^2 column =", reciprocal_q2_column,
      "~", float(reciprocal_q2_column))
print("memory gap =", memory_gap, "~", float(memory_gap))
print("physical AMP remainder =", physical_remainder)
print("PASS: scaled chronology matches the compiled correlation, while")
print("      memory != reciprocal q^2 column at R=56.")
