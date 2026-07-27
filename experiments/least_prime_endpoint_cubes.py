#!/usr/bin/env python3
"""Reproduce the least-prime and double-endpoint finite identities.

This script is diagnostic only. It does not produce a Lean certificate and its
output must not be treated as a theorem in the compiled library.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True)
class SieveData:
    spf: list[int]
    mu: list[int]
    omega: list[int]
    primes: list[int]


def build_sieve(limit: int) -> SieveData:
    if limit < 2:
        raise ValueError("limit must be at least 2")

    spf = list(range(limit + 1))
    primes: list[int] = []

    for n in range(2, limit + 1):
        if spf[n] == n:
            primes.append(n)
            if n * n <= limit:
                for multiple in range(n * n, limit + 1, n):
                    if spf[multiple] == multiple:
                        spf[multiple] = n

    mu = [0] * (limit + 1)
    omega = [0] * (limit + 1)
    mu[1] = 1

    for n in range(2, limit + 1):
        p = spf[n]
        quotient = n // p
        if quotient % p == 0:
            mu[n] = 0
            omega[n] = omega[quotient]
        else:
            mu[n] = -mu[quotient]
            omega[n] = omega[quotient] + 1

    return SieveData(spf=spf, mu=mu, omega=omega, primes=primes)


def distinct_prime_factors(n: int, spf: list[int]) -> list[int]:
    factors: list[int] = []
    while n > 1:
        p = spf[n]
        factors.append(p)
        n //= p
    return factors


def first_hit_twice_height(n: int, spf: list[int]) -> int:
    """Return 2*Y_1 = r^2-p^2, avoiding half-integer arithmetic."""
    p = spf[n]
    r = n // p
    return r * r - p * p


def run(limit: int) -> None:
    data = build_sieve(limit)

    prime_count = len(data.primes)
    mertens = sum(data.mu[1:])
    signed_composite_sum = 0
    depth_counts: dict[int, int] = defaultdict(int)
    core_weights: dict[int, int] = defaultdict(int)

    even_half_integral_failures = 0
    odd_four_lattice_failures = 0

    for n in range(4, limit + 1):
        if data.mu[n] == 0 or data.omega[n] < 2:
            continue

        signed_composite_sum += data.mu[n]
        depth_counts[data.omega[n]] += 1

        factors = distinct_prime_factors(n, data.spf)
        core = 1
        for p in factors[1:-1]:
            core *= p
        core_weights[core] += 1

        twice_height = first_hit_twice_height(n, data.spf)
        if n % 2 == 0:
            # Y is a half-integer exactly when 2Y is odd.
            if twice_height % 2 != 1:
                even_half_integral_failures += 1
        else:
            # Y in 4Z exactly when 2Y is divisible by 8.
            if twice_height % 8 != 0:
                odd_four_lattice_failures += 1

    weighted_core_sum = sum(
        data.mu[core] * weight for core, weight in core_weights.items()
    )

    reconstructed_mertens = 1 - prime_count + signed_composite_sum

    print(f"X = {limit}")
    print(f"pi(X) = {prime_count}")
    print(f"M(X) = {mertens}")
    print(f"signed squarefree-composite sum = {signed_composite_sum}")
    print(f"1 - pi(X) + composite sum = {reconstructed_mertens}")
    print(f"weighted endpoint-core sum = {weighted_core_sum}")
    print()

    print("lattice checks")
    print(f"  even half-integral failures: {even_half_integral_failures}")
    print(f"  odd 4Z failures: {odd_four_lattice_failures}")
    print()

    print("squarefree-composite depth counts")
    for depth in sorted(depth_counts):
        count = depth_counts[depth]
        sign = -1 if depth % 2 else 1
        print(f"  omega={depth}: count={count}, contribution={sign * count}")
    print()

    print("largest endpoint-core weights")
    for core, weight in sorted(
        core_weights.items(), key=lambda item: item[1], reverse=True
    )[:20]:
        print(
            f"  core={core}: W_X={weight}, "
            f"mu(core)*W_X={data.mu[core] * weight}"
        )

    assert mertens == reconstructed_mertens
    assert signed_composite_sum == weighted_core_sum
    assert even_half_integral_failures == 0
    assert odd_four_lattice_failures == 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=2_000_000)
    args = parser.parse_args()
    run(args.limit)
