#!/usr/bin/env python3
"""Reproduce Issue #163's primorial-wheel smooth-core experiment.

For the successive primorial blocks

    B_k = (W_{k-1}, W_k],    W_k = product_{j <= k} p_j,

this dependency-free diagnostic computes:

    A_k     = sum of the -1-initialized wheel states sigma_k(n),
    C_k     = the signed mass of the squarefree sqrt(W_k)-smooth core,
    Delta_k = sum_{n in B_k} mu(n),

and checks the exact finite identity

    Delta_k = A_k - 2 C_k.

It also reports the numerical failure of the proposed |Delta_k| <= 2^k
extension bound. In particular, the eighth block has |Delta_8| = 303 > 256,
and its actual smooth-core reversal has magnitude 2 |C_8| = 86,698.

This script is diagnostic only. It does not produce a Lean certificate and its
output must not be treated as a theorem in the compiled library.
"""

from __future__ import annotations

import argparse
import math
import sys
from array import array
from dataclasses import dataclass


EXPECTED_ROWS = (
    # k, lower, upper, A_k, C_k, Delta_k
    (1, 1, 2, -1, 0, -1),
    (2, 2, 6, -1, 0, -1),
    (3, 6, 30, -4, -1, -2),
    (4, 30, 210, 6, 2, 2),
    (5, 210, 2_310, 86, 43, 0),
    (6, 2_310, 30_030, 677, 330, 17),
    (7, 30_030, 510_510, 7_047, 3_544, -41),
    (8, 510_510, 9_699_690, 87_001, 43_349, 303),
)


@dataclass(frozen=True)
class SieveData:
    mu: array
    omega: bytearray
    largest_prime_factor: array


@dataclass(frozen=True)
class BlockRow:
    k: int
    lower: int
    upper: int
    raw_mass: int
    smooth_core_mass: int
    delta: int

    @property
    def length(self) -> int:
        return self.upper - self.lower

    @property
    def corrected_mass(self) -> int:
        return self.raw_mass - 2 * self.smooth_core_mass

    @property
    def extension_bound(self) -> int:
        return 1 << self.k

    @property
    def reversal_magnitude(self) -> int:
        return 2 * abs(self.smooth_core_mass)


def first_primes(count: int) -> list[int]:
    """Return the first ``count`` primes by dependency-free trial division."""
    if count < 1:
        raise ValueError("blocks must be at least 1")

    primes: list[int] = []
    candidate = 2
    while len(primes) < count:
        is_prime = True
        root = math.isqrt(candidate)
        for p in primes:
            if p > root:
                break
            if candidate % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(candidate)
        candidate = 3 if candidate == 2 else candidate + 2
    return primes


def primorial_endpoints(primes: list[int]) -> list[int]:
    endpoints = [1]
    value = 1
    for p in primes:
        value *= p
        endpoints.append(value)
    return endpoints


def linear_sieve(limit: int) -> SieveData:
    """Linear sieve of mu, omega, and largest prime factor through ``limit``.

    Compact standard-library arrays keep the default eight-block run comfortably
    below the memory required by four Python ``list[int]`` objects of length ten
    million.
    """
    if limit < 2:
        raise ValueError("limit must be at least 2")

    composite = bytearray(limit + 1)
    mu = array("b", [0]) * (limit + 1)
    omega = bytearray(limit + 1)
    largest_prime_factor = array("I", [0]) * (limit + 1)
    primes = array("I")
    mu[1] = 1

    for n in range(2, limit + 1):
        if composite[n] == 0:
            primes.append(n)
            mu[n] = -1
            omega[n] = 1
            largest_prime_factor[n] = n

        for p in primes:
            multiple = n * p
            if multiple > limit:
                break

            composite[multiple] = 1
            # In the Euler sieve loop p never exceeds the least prime factor of
            # n, so the largest prime factor of n*p is already P+(n).
            largest_prime_factor[multiple] = largest_prime_factor[n]

            if n % p == 0:
                mu[multiple] = 0
                omega[multiple] = omega[n]
                break

            mu[multiple] = -mu[n]
            omega[multiple] = omega[n] + 1

    return SieveData(
        mu=mu,
        omega=omega,
        largest_prime_factor=largest_prime_factor,
    )


def initialized_state(
    n: int,
    cutoff: int,
    data: SieveData,
) -> int:
    """Return the final -1-initialized state after processing primes <= cutoff."""
    if data.mu[n] == 0:
        return 0

    large_prime_count = int(data.largest_prime_factor[n] > cutoff)
    small_prime_count = data.omega[n] - large_prime_count
    return -1 if small_prime_count % 2 == 0 else 1


def evaluate_blocks(endpoints: list[int], data: SieveData) -> list[BlockRow]:
    rows: list[BlockRow] = []

    for k in range(1, len(endpoints)):
        lower = endpoints[k - 1]
        upper = endpoints[k]
        cutoff = math.isqrt(upper)
        raw_mass = 0
        smooth_core_mass = 0
        delta = 0

        for n in range(lower + 1, upper + 1):
            delta += data.mu[n]
            state = initialized_state(n, cutoff, data)
            raw_mass += state
            if state != 0 and data.largest_prime_factor[n] <= cutoff:
                smooth_core_mass += state

        row = BlockRow(
            k=k,
            lower=lower,
            upper=upper,
            raw_mass=raw_mass,
            smooth_core_mass=smooth_core_mass,
            delta=delta,
        )
        assert row.corrected_mass == row.delta, (
            f"identity failed in block {k}: "
            f"A-2C={row.corrected_mass}, Delta={row.delta}"
        )
        rows.append(row)

    return rows


def verify_published_table(rows: list[BlockRow]) -> None:
    for row, expected in zip(rows, EXPECTED_ROWS):
        actual = (
            row.k,
            row.lower,
            row.upper,
            row.raw_mass,
            row.smooth_core_mass,
            row.delta,
        )
        assert actual == expected, f"published row mismatch: {actual} != {expected}"


def print_report(rows: list[BlockRow]) -> None:
    header = (
        f"{'k':>2}  {'block':>22}  {'length':>10}  {'A_k':>8}  {'C_k':>8}  "
        f"{'A_k-2C_k':>10}  {'Delta_k':>8}  {'2^k bound':>11}"
    )
    print(header)
    print("-" * len(header))

    for row in rows:
        bound_status = "PASS" if abs(row.delta) <= row.extension_bound else "FAIL"
        block = f"({row.lower:,}, {row.upper:,}]"
        print(
            f"{row.k:>2}  {block:>22}  {row.length:>10,}  "
            f"{row.raw_mass:>8,}  {row.smooth_core_mass:>8,}  "
            f"{row.corrected_mass:>10,}  {row.delta:>8,}  "
            f"{row.extension_bound:>5,} {bound_status:>5}"
        )

    print("\nExact identity: Delta_k = A_k - 2 C_k in every displayed block.")

    failures = [row for row in rows if abs(row.delta) > row.extension_bound]
    if failures:
        print("\nCounterexamples to the proposed |Delta_k| <= 2^k bound:")
        for row in failures:
            print(
                f"  k={row.k}: |Delta_k|={abs(row.delta):,} > "
                f"2^{row.k}={row.extension_bound:,}"
            )

    last = rows[-1]
    cumulative_boolean_correction = 2 * ((1 << last.k) - 1)
    print("\nSmooth-core correction diagnostic at the final block:")
    print(
        f"  actual reversal magnitude 2|C_{last.k}| = "
        f"{last.reversal_magnitude:,}"
    )
    print(
        f"  2(2^{last.k}-1) Boolean-subset comparison = "
        f"{cumulative_boolean_correction:,}"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce Issue #163's primorial-wheel block identity."
    )
    parser.add_argument(
        "--blocks",
        type=int,
        default=8,
        help="number of successive primorial blocks to evaluate (default: 8)",
    )
    parser.add_argument(
        "--max-limit",
        type=int,
        default=10_000_000,
        help="refuse a run whose final primorial exceeds this value",
    )
    parser.add_argument(
        "--skip-published-check",
        action="store_true",
        help="do not assert equality with the eight published table rows",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = first_primes(args.blocks)
    endpoints = primorial_endpoints(primes)
    limit = endpoints[-1]

    if limit > args.max_limit:
        print(
            f"refusing to sieve through {limit:,}; increase --max-limit explicitly",
            file=sys.stderr,
        )
        raise SystemExit(2)

    print(f"primes: {primes}")
    print(f"final primorial W_{args.blocks} = {limit:,}")
    print("building dependency-free linear sieve...")
    data = linear_sieve(limit)
    rows = evaluate_blocks(endpoints, data)

    if not args.skip_published_check:
        verify_published_table(rows)

    print_report(rows)


if __name__ == "__main__":
    main()
