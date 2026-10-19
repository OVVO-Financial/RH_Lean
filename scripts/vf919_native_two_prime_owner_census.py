#!/usr/bin/env python3
"""Exact rational diagnostic for native R=317,1027 returned-core Mobius weights.

The source is the RHLean.Proof.lowOwnerZeroFrequencyMobiusWeight definition,
NOT an OAI ideal or surrogate smooth-profile weight. The paired prime
identity is checked at every enumerated genuine p-free/q-free parent.

This is a finite regression, not a power saving or uniform analytic theorem.
"""
from fractions import Fraction


def sieve(limit):
    lp = [0] * (limit + 1)
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if not lp[n]:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p > lp[n] or n * p > limit:
                break
            lp[n * p] = p
            if p == lp[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return mu, primes


def chi3(n):
    return {0: 0, 1: 1, 2: -1}[n % 3]


def run(R):
    X = R * R - 1
    mu, primes = sieve(X)
    owners = [q for q in primes if 2 < q and q * q < R]
    if R == 317:
        assert owners == [3, 5, 7, 11, 13, 17], owners
    reciprocal = [(q, X // (q * q)) for q in owners]

    def weight(n):
        return Fraction(int(n >= R)) + sum(
            (Fraction(1, q) for q, cap in reciprocal if n <= cap),
            Fraction(),
        )

    def site(n):
        return weight(n) * mu[n] * chi3(n)

    total = 0
    active = 0
    examples = []
    for p, q in [(5, 7), (7, 13), (5, 13), (7, 19)]:
        for a in range(1, min(5000, X // (p * q)) + 1):
            if a % p == 0 or a % q == 0:
                continue
            lhs = (
                site(a)
                + Fraction(site(p * a), chi3(p))
                + Fraction(site(q * a), chi3(q))
                + Fraction(site(p * q * a), chi3(p) * chi3(q))
            )
            curvature = (
                weight(a) - weight(p * a)
                - weight(q * a) + weight(p * q * a)
            )
            rhs = mu[a] * chi3(a) * curvature
            assert lhs == rhs, (R, p, q, a, lhs, rhs)
            total += 1
            if curvature and mu[a] and chi3(a):
                active += 1
                if len(examples) < 4:
                    examples.append((p, q, a, str(lhs), str(curvature)))

    # The zero row q=3 is never divided by a zero character.
    p, q, a = 7, 3, 47
    base = site(a) + Fraction(site(p * a), chi3(p))
    expected = mu[a] * chi3(a) * (weight(a) - weight(p * a))
    assert base == expected

    print(
        f"R={R} X={X} owners={owners} "
        f"checked={total} active_curvature={active} nonunit_checked=1"
    )
    for p, q, a, lhs, curv in examples:
        print(f"  p={p} q={q} a={a} aligned={lhs} curvature={curv}")


if __name__ == "__main__":
    for root in (317, 1027):
        run(root)
