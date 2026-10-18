#!/usr/bin/env python3
"""Full genuine squarefree-pair ancestry and uniform square-wheel census.

Exact finite regression only; no infinite estimate, stochastic model or zeta input.
All cutoffs and prime factorizations are integer arithmetic.
"""
from collections import Counter, defaultdict
from math import gcd, isqrt

MAX_N = 1100


def factorization_sieve(N):
    spf = list(range(N + 1))
    for p in range(2, isqrt(N) + 1):
        if spf[p] == p:
            for n in range(p * p, N + 1, p):
                if spf[n] == n:
                    spf[n] = p
    factors = [()] * (N + 1)
    mu = [0] * (N + 1)
    mu[1] = 1
    for n in range(2, N + 1):
        k = n
        fs = []
        sqfree = True
        while k > 1:
            p = spf[k]
            a = 0
            while k % p == 0:
                k //= p
                a += 1
            fs.append(p)
            if a > 1:
                sqfree = False
        factors[n] = tuple(fs)
        mu[n] = (-1 if len(fs) % 2 else 1) if sqfree else 0
    primes = [p for p in range(2, N + 1) if len(factors[p]) == 1 and factors[p][0] == p]
    return mu, factors, primes


mu, factors, primes = factorization_sieve(MAX_N)
prime_set = set(primes)


def ancestry_census(x):
    sites = [n for n in range(1, x + 1) if mu[n]]
    cells = Counter()
    count_by_shared = Counter()
    signed_by_shared = Counter()
    signed_by_gcd = Counter()
    pos_pairs = neg_pairs = 0
    for i, m in enumerate(sites):
        fm = set(factors[m])
        for n in sites[i + 1:]:
            shared = len(fm.intersection(factors[n]))
            label = (len(factors[m]), len(factors[n]), shared)
            cells[label] += 1
            count_by_shared[shared] += 1
            sign = mu[m] * mu[n]
            signed_by_shared[shared] += sign
            signed_by_gcd[gcd(m, n)] += sign
            if sign == 1:
                pos_pairs += 1
            else:
                neg_pairs += 1
            assert sign == (-1) ** (label[0] + label[1] - 2 * label[2])
    N = sum(mu[n] ** 2 for n in range(1, x + 1))
    M = sum(mu[1:x + 1])
    C = sum(signed_by_shared.values())
    assert N == len(sites)
    assert pos_pairs + neg_pairs == N * (N - 1) // 2
    assert C == pos_pairs - neg_pairs == (M * M - N) // 2
    assert sum(((-1) ** (k + l)) * a
               for (k, l, _), a in cells.items()) == C
    return {
        "M": M, "N": N, "C": C, "cells": cells,
        "signed_shared": signed_by_shared,
        "count_shared": count_by_shared,
        "signed_gcd": signed_by_gcd,
        "positive_pairs": pos_pairs, "negative_pairs": neg_pairs,
    }


def fixed_wheel_test(R, t):
    assert R * R < t < (R + 1) ** 2
    low_primes = [p for p in primes if p <= R]
    # The Euler inclusion-exclusion sum is exactly the wheel survivor.
    wheel_divisors = [(1, 1)]
    for p in low_primes:
        wheel_divisors += [(p * d, -sgn) for d, sgn in wheel_divisors]
    smooth = high = 0
    prime_sites = 0
    for n in range(R * R, (R + 1) ** 2):
        survivor = all(n % p for p in low_primes)
        euler = sum(sgn for d, sgn in wheel_divisors if n % d == 0)
        assert euler == int(survivor) == int(n in prime_set)
        high_factors = [p for p in factors[n] if p > R]
        assert len(high_factors) <= 1
        if mu[n]:
            if not high_factors:
                smooth += mu[n]
            else:
                p, = high_factors
                c = n // p
                assert 1 <= c <= R and mu[n] == -mu[c]
                high += mu[n]
        if n in prime_set:
            prime_sites += 1
    inc = sum(mu[R * R:(R + 1) ** 2])
    assert inc == smooth + high
    partial = sum(mu[R * R:t + 1])
    partial_smooth = sum(mu[n] for n in range(R * R, t + 1)
                         if mu[n] and all(p <= R for p in factors[n]))
    partial_high = partial - partial_smooth
    return inc, smooth, high, prime_sites, partial, partial_smooth, partial_high


def main():
    expected = {
        317: dict(M=-4, N=194, C=-89, shared={0:26, 1:-176, 2:65, 3:-4},
                  positive_pairs=9316, negative_pairs=9405),
        1027: dict(M=-3, N=625, C=-308, shared={0:323, 1:-926, 2:300, 3:-5},
                   positive_pairs=97346, negative_pairs=97654),
    }
    for x in (317, 1027):
        r = ancestry_census(x)
        e = expected[x]
        for key in ("M", "N", "C", "positive_pairs", "negative_pairs"):
            assert r[key] == e[key], (x, key, r[key], e[key])
        assert dict(r["signed_shared"]) == e["shared"]
        print("CENSUS", x, "M", r["M"], "D", r["N"], "C", r["C"],
              "shared", dict(sorted(r["signed_shared"].items())),
              "depth_cells", len(r["cells"]))
    for R, t in ((17, 317), (32, 1027)):
        result = fixed_wheel_test(R, t)
        print("SQUARE_WHEEL", R, t, "full (total,smooth,high,primes)",
              result[:4], "partial (total,smooth,high)", result[4:])
        assert result[4:] == ((3, 0, 3) if R == 17 else (1, 0, 1))
        assert result[:3] == ((4, 0, 4) if R == 17 else (-4, -3, -1))
    for x in (317, 1027):
        Cx = ancestry_census(x)["C"]
        Cprev = (sum(mu[1:x]) ** 2 - sum(mu[n]**2 for n in range(1, x))) // 2
        assert Cx - Cprev == mu[x] * sum(mu[1:x])
        print("PRIME_ADMISSION", x, "delta_C", Cx-Cprev)
    print("PASS genuine Möbius sign, tensor, gcd, square wheel, cofactor tests")


if __name__ == "__main__":
    main()
