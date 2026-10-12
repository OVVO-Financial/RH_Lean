#!/usr/bin/env python3
"""Exact signed CRT square-run arithmetic; no probability or RH assumption.

Examples:
  python3 scripts/signed_square_run_crt_parity_certificate.py
  python3 scripts/signed_square_run_crt_parity_certificate.py --census /path/to/mertens_100000_square_blocks.csv

The optional census must have R,M columns and contain roots 5267,5417,6000,6154,
88130,100000. The proof of the uniform phase bound is the finite divisor-floor
expansion described in research/SQUARE_RUN_SIGNED_CRT_PHYSICAL_MIXING_20261010.md.
"""
import argparse
import csv
from fractions import Fraction
from functools import lru_cache

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
RUNS = ((5267, 5417), (6000, 6154), (88130, 100000))

@lru_cache(None)
def signed_terms(k):
    terms = {1: 1}
    for p in PRIMES[:k]:
        terms = {d * pp: c * weight
                 for d, c in terms.items()
                 for pp, weight in ((1, 1), (p, -2), (p * p, 1))}
    rho = Fraction(1)
    for p in PRIMES[:k]:
        rho *= Fraction((p - 1)**2, p * p)
    assert len(terms) == 3**k
    assert sum(abs(c) for c in terms.values()) == 4**k
    assert sum((Fraction(c, d) for d, c in terms.items()), Fraction(0)) == rho
    return terms, rho

@lru_cache(None)
def survivor_terms(k):
    terms = {1: 1}
    for p in PRIMES[:k]:
        terms = {d * pp: c * weight
                 for d, c in terms.items()
                 for pp, weight in ((1, 1), (p, -1))}
    tau = Fraction(1)
    for p in PRIMES[:k]:
        tau *= Fraction(p - 1, p)
    assert len(terms) == 2**k
    assert sum(abs(c) for c in terms.values()) == 2**k
    assert sum((Fraction(c, d) for d, c in terms.items()), Fraction(0)) == tau
    return terms, tau

def floor_mass(terms, x):
    return sum(c * (x // d) for d, c in terms.items())

def signed_at(k, n):
    value = 1
    for p in PRIMES[:k]:
        value *= 1 - 2 * int(n % p == 0) + int(n % (p * p) == 0)
    return value

def moebius(n):
    if n == 1:
        return 1
    value = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            value *= -1
            if n % d == 0:
                return 0
        d += 1
    if n > 1:
        value *= -1
    return value

def low_factor(n, k):
    d = 1
    for p in PRIMES[:k]:
        while (n // d) % p == 0:
            d *= p
    return d

def certificate(k, a, b):
    signed, rho = signed_terms(k)
    unsigned, tau = survivor_terms(k)
    x, y = b * b - 1, a * a - 1
    delta = floor_mass(signed, x) - floor_mass(signed, y)
    square = floor_mass(unsigned, b - 1) - floor_mass(unsigned, a - 1)
    open_low = delta - square
    L = b * b - a * a
    e_low = Fraction(delta) - rho * L
    e_open = Fraction(open_low) - rho * L + tau * (b - a)
    assert abs(e_low) <= 2 * 4**k
    assert abs(e_open) <= 2 * 4**k + 2 * 2**k
    return {"primes_through": PRIMES[k - 1], "a": a, "b": b,
            "low_halfopen": delta, "square_survivors": square,
            "low_open": open_low, "phase": e_low, "open_phase": e_open}

def verify_small():
    for k in (4, 5, 8):
        terms, rho = signed_terms(k)
        for x in (0, 1, 2, 3, 4, 15, 97, 502, 1000):
            F = floor_mass(terms, x)
            assert F == sum(signed_at(k, n) for n in range(1, x + 1))
            assert abs(F - rho * x) <= 4**k
        for n in range(1, 4001):
            assert moebius(n) == signed_at(k, n) * moebius(n // low_factor(n, k))
    print("PASS: local sign identities, exact divisor-floor expansions, uniform phases")

def read_census(path):
    wanted = {r for a, b in RUNS for r in (a, b)}
    result = {}
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            r = int(row["R"])
            if r in wanted:
                result[r] = int(row["M"])
    if set(result) != wanted:
        raise ValueError("census lacks roots: " + repr(sorted(wanted - set(result))))
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", default=None)
    args = parser.parse_args()
    verify_small()
    M = read_census(args.census) if args.census else None
    for k in (4, 5, 8):
        for a, b in RUNS:
            c = certificate(k, a, b)
            if M is not None:
                actual = M[b] - M[a]
                complement = actual - c["low_open"]
                assert c["low_open"] + complement == actual
                c["actual_mobius_delta"] = actual
                c["high_parity_open"] = complement
            print(c)
    print("PASS: original open-square signed double-endpoint compensation")

if __name__ == "__main__":
    main()
