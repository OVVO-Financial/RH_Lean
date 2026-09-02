#!/usr/bin/env python3
"""Numeric check of the fresh-prime family covariance descent.

Validates, over many primes and cutoffs, the two arithmetic theorems in
`RHLean/Analysis/BlockCovarianceRefinement.lean`:

```text
largePrimeFamilyPrefix  p K = - realMertensLength K              (K <= p)
largePrimeFamilyPairSum p K =   realMertensPositiveLagPairSum K  (K <= p)
```

so that for a post-root prime (p*p > W, K = W//p + 1) the covariance carried
strictly inside the p-family is exactly the global Moebius covariance at the
reduced scale.  Also checks the square-block energy identity

```text
E - Q = 2 * sum_j C_j.
```

    python3 scripts/CumulativeOthelloBoundary/family_descent_check.py [wmax]
"""

from __future__ import annotations

import sys


def moebius_sieve(n_max: int) -> tuple[list[int], list[int]]:
    spf = list(range(n_max + 1))
    primes: list[int] = []
    for i in range(2, n_max + 1):
        if spf[i] == i:
            primes.append(i)
        for p in primes:
            if p > spf[i] or i * p > n_max:
                break
            spf[i * p] = p
    mu = [1] * (n_max + 1)
    mu[0] = 0
    for n in range(2, n_max + 1):
        p = spf[n]
        m = n // p
        mu[n] = 0 if m % p == 0 else -mu[m]
    return mu, primes


def mertens_length(K: int, mu: list[int]) -> int:
    return sum(mu[:K])


def pair_sum(K: int, mu: list[int]) -> int:
    total = 0
    run = 0
    for n in range(K):
        total += mu[n] * run
        run += mu[n]
    return total


def family_prefix(p: int, K: int, mu: list[int]) -> int:
    return sum(mu[p * c] for c in range(K))


def family_pair_sum(p: int, K: int, mu: list[int]) -> int:
    total = 0
    run = 0
    for d in range(K):
        total += mu[p * d] * run
        run += mu[p * d]
    return total


def main(argv: list[str]) -> int:
    w_max = int(argv[1]) if len(argv) > 1 else 20000
    mu, primes = moebius_sieve(w_max + 1)
    checked = 0
    for W in (w_max // 4, w_max // 2, w_max):
        root = int(W ** 0.5)
        post = [p for p in primes if p * p > W and p <= W]
        for p in post:
            K = W // p + 1
            assert K <= p, (p, K)
            if family_prefix(p, K, mu) != -mertens_length(K, mu):
                print(f"MASS MISMATCH p={p} W={W}")
                return 1
            if family_pair_sum(p, K, mu) != pair_sum(K, mu):
                print(f"COVARIANCE MISMATCH p={p} W={W}")
                return 1
            checked += 1
        # square-block energy identity
        R = root
        blocks = [sum(mu[j * j:(j + 1) * (j + 1)]) for j in range(R)]
        energy = sum(b * b for b in blocks)
        diagonal = sum(mu[k] * mu[k] for k in range(R * R))
        inner = 0
        for j in range(R):
            run = 0
            for k in range(j * j, (j + 1) * (j + 1)):
                inner += mu[k] * run
                run += mu[k]
        status = "OK" if energy - diagonal == 2 * inner else "MISMATCH"
        print(f"W = {W:>7}  post-root primes checked: {len(post):>5}"
              f"   E - Q = {energy - diagonal:>8}"
              f"   2*sum_j C_j = {2 * inner:>8}   {status}")
        if status != "OK":
            return 1
    print()
    print(f"All {checked} post-root prime families matched exactly:")
    print("  family mass       = - M(reduced scale)")
    print("  family covariance =   C(reduced scale)")
    print("A post-root prime family is an isometric copy of a lower-scale")
    print("prefix for pair covariance: the two sign flips cancel in every")
    print("product, so covariance descends without loss.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
