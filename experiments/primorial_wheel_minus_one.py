#!/usr/bin/env python3
"""Reproduce the -1 initialized primorial-wheel block experiment.

For each successive primorial endpoint

    W_k = product_{j <= k} p_j,
    B_k = (W_{k-1}, W_k],

this script computes:

    A_k = sum_{n in B_k} sigma_k(n),

where every n starts at -1, each distinct prime p <= sqrt(W_k) flips the
sign, and every multiple of p^2 is killed (set to zero);

    C_k = sum sigma_k(n)

restricted to squarefree n in B_k whose largest prime factor is at most
sqrt(W_k); and

    Delta_k = sum_{n in B_k} mu(n).

The pointwise classification implies the exact identity

    Delta_k = A_k - 2 C_k.

By default the script runs the first eight primorial blocks, ending at
W_8 = 9,699,690, and checks the values reported in GitHub issue #163.

Dependency:
    numpy

Example:
    python experiments/primorial_wheel_minus_one.py
    python experiments/primorial_wheel_minus_one.py --blocks 6
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Iterable

import numpy as np


FIRST_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)


@dataclass(frozen=True)
class BlockResult:
    """Computed statistics for one successive primorial block."""

    k: int
    prime: int
    lower: int
    upper: int
    length: int
    raw_minus_one_sum: int
    smooth_core_sum: int
    reconstructed_delta: int
    true_mobius_delta: int
    smooth_core_count: int


EXPECTED_FIRST_EIGHT = (
    # k, lower, upper, A_k, C_k, Delta_k, smooth-core count
    (1, 1, 2, -1, 0, -1, 0),
    (2, 2, 6, -1, 0, -1, 0),
    (3, 6, 30, -4, -1, -2, 3),
    (4, 30, 210, 6, 2, 2, 20),
    (5, 210, 2_310, 86, 43, 0, 261),
    (6, 2_310, 30_030, 677, 330, 17, 3_682),
    (7, 30_030, 510_510, 7_047, 3_544, -41, 68_894),
    (8, 510_510, 9_699_690, 87_001, 43_349, 303, 1_388_687),
)


def primorial_endpoints(primes: Iterable[int]) -> list[int]:
    """Return cumulative products of the supplied prime sequence."""

    endpoints: list[int] = []
    product = 1
    for prime in primes:
        product *= prime
        endpoints.append(product)
    return endpoints


def prime_sieve(limit: int) -> np.ndarray:
    """Return all primes <= limit as a NumPy integer array."""

    is_prime = np.ones(limit + 1, dtype=np.bool_)
    is_prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            is_prime[p * p :: p] = False
    return np.flatnonzero(is_prime)


def mobius_and_largest_prime_factor(
    limit: int, primes: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Compute mu(n) and the largest prime factor of n for n <= limit."""

    mobius = np.ones(limit + 1, dtype=np.int8)
    mobius[0] = 0
    largest_prime_factor = np.zeros(limit + 1, dtype=np.int32)

    for prime_value in primes:
        p = int(prime_value)
        mobius[p::p] *= -1
        largest_prime_factor[p::p] = p

        square = p * p
        if square <= limit:
            mobius[square::square] = 0

    return mobius, largest_prime_factor


def minus_one_states(
    lower: int,
    upper: int,
    primes: np.ndarray,
) -> np.ndarray:
    """Compute final -1 initialized states on (lower, upper]."""

    first = lower + 1
    states = np.full(upper - lower, -1, dtype=np.int8)
    cutoff = math.isqrt(upper)

    for prime_value in primes[primes <= cutoff]:
        p = int(prime_value)

        first_multiple_offset = (-first) % p
        states[first_multiple_offset::p] *= -1

        square = p * p
        first_square_offset = (-first) % square
        states[first_square_offset::square] = 0

    return states


def run_experiment(blocks: int) -> list[BlockResult]:
    """Compute the requested number of successive primorial blocks."""

    if blocks < 1 or blocks > len(FIRST_PRIMES):
        raise ValueError(
            f"blocks must be between 1 and {len(FIRST_PRIMES)}; got {blocks}"
        )

    chosen_primes = FIRST_PRIMES[:blocks]
    endpoints = primorial_endpoints(chosen_primes)
    maximum = endpoints[-1]

    primes = prime_sieve(maximum)
    mobius, largest_prime_factor = mobius_and_largest_prime_factor(
        maximum, primes
    )

    results: list[BlockResult] = []

    for index, upper in enumerate(endpoints):
        k = index + 1
        lower = 1 if index == 0 else endpoints[index - 1]
        first = lower + 1
        stop = upper + 1
        cutoff = math.isqrt(upper)

        states = minus_one_states(lower, upper, primes)

        squarefree = mobius[first:stop] != 0
        smooth = squarefree & (largest_prime_factor[first:stop] <= cutoff)

        raw_sum = int(states.sum())
        smooth_sum = int(states[smooth].sum())
        reconstructed = raw_sum - 2 * smooth_sum
        true_delta = int(mobius[first:stop].sum())

        if reconstructed != true_delta:
            raise AssertionError(
                "Exact identity failed on block "
                f"{k}: {reconstructed} != {true_delta}"
            )

        results.append(
            BlockResult(
                k=k,
                prime=chosen_primes[index],
                lower=lower,
                upper=upper,
                length=upper - lower,
                raw_minus_one_sum=raw_sum,
                smooth_core_sum=smooth_sum,
                reconstructed_delta=reconstructed,
                true_mobius_delta=true_delta,
                smooth_core_count=int(smooth.sum()),
            )
        )

    return results


def verify_reported_values(results: list[BlockResult]) -> None:
    """Check computed values against the issue #163 numerical table."""

    for result, expected in zip(results, EXPECTED_FIRST_EIGHT, strict=False):
        observed = (
            result.k,
            result.lower,
            result.upper,
            result.raw_minus_one_sum,
            result.smooth_core_sum,
            result.true_mobius_delta,
            result.smooth_core_count,
        )
        if observed != expected:
            raise AssertionError(
                f"Reported-value mismatch for block {result.k}:\n"
                f"  observed={observed}\n"
                f"  expected={expected}"
            )


def print_results(results: list[BlockResult]) -> None:
    """Print a Markdown-compatible results table."""

    print(
        "| k | p_k | block B_k | length | A_k | C_k | "
        "A_k - 2 C_k | true Delta_k | smooth count |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")

    for result in results:
        print(
            f"| {result.k} | {result.prime} | "
            f"({result.lower:,}, {result.upper:,}] | "
            f"{result.length:,} | "
            f"{result.raw_minus_one_sum:,} | "
            f"{result.smooth_core_sum:,} | "
            f"{result.reconstructed_delta:,} | "
            f"{result.true_mobius_delta:,} | "
            f"{result.smooth_core_count:,} |"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--blocks",
        type=int,
        default=8,
        help="number of successive primorial blocks to compute (default: 8)",
    )
    parser.add_argument(
        "--skip-reported-check",
        action="store_true",
        help="skip comparison with the issue #163 reported values",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    results = run_experiment(args.blocks)

    if not args.skip_reported_check:
        verify_reported_values(results)

    print_results(results)
    print("\nVerified: Delta_k = A_k - 2 C_k on every computed block.")


if __name__ == "__main__":
    main()
