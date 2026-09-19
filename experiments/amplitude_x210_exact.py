#!/usr/bin/env python3
"""Exact finite regression for the x=210 amplitude-space cancellation example.

This script is dependency-free.  It verifies the finite census documented in

    research/AMPLITUDE_X210_EXACT_EXAMPLE.md

The example is structural: x=210 with root cutoff floor(sqrt(210))=14.  It is
not a literal specialization of the production endpoint X_R = R^2 - 1 and it
does not assert an asymptotic Mertens bound.
"""

from __future__ import annotations

import math


X = 210
ROOT = math.isqrt(X)

EXPECTED_PAIRS = [
    (17, 34),
    (19, 38),
    (23, 46),
    (29, 58),
    (31, 62),
    (37, 74),
    (41, 82),
    (43, 86),
    (47, 94),
    (51, 102),
    (53, 106),
    (57, 114),
    (59, 118),
    (61, 122),
    (67, 134),
    (69, 138),
    (71, 142),
    (73, 146),
    (79, 158),
    (83, 166),
    (85, 170),
    (87, 174),
    (89, 178),
    (93, 186),
    (95, 190),
    (97, 194),
    (101, 202),
    (103, 206),
]

EXPECTED_NEGATIVE_SURVIVORS = [
    107,
    109,
    113,
    127,
    131,
    137,
    139,
    149,
    151,
    157,
    163,
    167,
    173,
    179,
    181,
    191,
    193,
    197,
    199,
]

EXPECTED_POSITIVE_BY_COFACTOR = {
    3: [111, 123, 129, 141, 159, 177, 183, 201],
    5: [115, 145, 155, 185, 205],
    7: [119, 133, 161, 203],
    11: [187, 209],
}

EXPECTED_H_TABLE = {
    1: (40, 21, 19),
    3: (13, 5, 8),
    5: (7, 2, 5),
    7: (4, 0, 4),
    11: (2, 0, 2),
}


def primes_upto(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    sieve[0:2] = [False, False]
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = False
    return [n for n, is_prime in enumerate(sieve) if is_prime]


PRIMES = primes_upto(X)
PRIME_SET = set(PRIMES)


def factorization(n: int) -> list[tuple[int, int]]:
    """Return the prime factorization of n as (prime, exponent) pairs."""
    if n < 1:
        raise ValueError("n must be positive")
    if n == 1:
        return []

    result: list[tuple[int, int]] = []
    remaining = n
    for p in PRIMES:
        if p * p > remaining:
            break
        if remaining % p != 0:
            continue
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        result.append((p, exponent))
    if remaining > 1:
        result.append((remaining, 1))
    return result


def mobius(n: int) -> int:
    factors = factorization(n)
    if any(exponent > 1 for _, exponent in factors):
        return 0
    return -1 if len(factors) % 2 else 1


def largest_prime_factor(n: int) -> int:
    factors = factorization(n)
    return 1 if not factors else factors[-1][0]


def H(c: int) -> int:
    """Count high primes p>ROOT with c*p <= X."""
    return sum(1 for p in PRIMES if p > ROOT and c * p <= X)


def main() -> None:
    assert ROOT == 14

    squarefree = [n for n in range(1, X + 1) if mobius(n) != 0]
    smooth = [n for n in squarefree if largest_prime_factor(n) <= ROOT]
    outer = [n for n in squarefree if largest_prime_factor(n) > ROOT]

    mertens = sum(mobius(n) for n in range(1, X + 1))
    smooth_amplitude = sum(mobius(n) for n in smooth)
    outer_amplitude = sum(mobius(n) for n in outer)

    assert len(squarefree) == 129
    assert len(smooth) == 35
    assert len(outer) == 94
    assert mertens == -1
    assert smooth_amplitude == -1
    assert outer_amplitude == 0
    assert mertens == smooth_amplitude + outer_amplitude

    outer_set = set(outer)
    pairs = [
        (m, 2 * m)
        for m in outer
        if m % 2 == 1 and m <= X // 2 and 2 * m in outer_set
    ]
    assert pairs == EXPECTED_PAIRS
    assert len(pairs) == 28

    paired_states = {n for pair in pairs for n in pair}
    assert len(paired_states) == 56
    for parent, child in pairs:
        assert mobius(parent) + mobius(child) == 0

    survivors = [n for n in outer if n not in paired_states]
    assert len(survivors) == 38
    assert survivors == [n for n in outer if n % 2 == 1 and n > X // 2]

    negative_survivors = [n for n in survivors if mobius(n) == -1]
    positive_survivors = [n for n in survivors if mobius(n) == 1]

    assert negative_survivors == EXPECTED_NEGATIVE_SURVIVORS
    assert all(n in PRIME_SET for n in negative_survivors)
    assert len(negative_survivors) == 19

    expected_positive = [
        n
        for c in (3, 5, 7, 11)
        for n in EXPECTED_POSITIVE_BY_COFACTOR[c]
    ]
    assert sorted(positive_survivors) == sorted(expected_positive)
    assert len(positive_survivors) == 19

    for c, states in EXPECTED_POSITIVE_BY_COFACTOR.items():
        reconstructed = [
            c * p
            for p in PRIMES
            if p > ROOT and X // 2 < c * p <= X
        ]
        assert reconstructed == states
        assert all(mobius(n) == 1 for n in states)

    h_table = {
        c: (H(c), H(2 * c), H(c) - H(2 * c))
        for c in (1, 3, 5, 7, 11)
    }
    assert h_table == EXPECTED_H_TABLE

    block_amplitudes = [
        -(H(1) - H(2)),
        H(3) - H(6),
        H(5) - H(10),
        H(7) - H(14),
        H(11) - H(22),
    ]
    assert block_amplitudes == [-19, 8, 5, 4, 2]
    assert sum(block_amplitudes) == 0

    l1_mass = sum(abs(value) for value in block_amplitudes)
    diagonal_energy = sum(value * value for value in block_amplitudes)
    cross_term = 2 * sum(
        block_amplitudes[i] * block_amplitudes[j]
        for i in range(len(block_amplitudes))
        for j in range(i + 1, len(block_amplitudes))
    )

    assert l1_mass == 38
    assert diagonal_energy == 470
    assert cross_term == -470
    assert diagonal_energy + cross_term == 0

    assert sum(mobius(n) for n in survivors) == 0
    assert sum(mobius(n) for n in paired_states) == 0
    assert sum(mobius(n) for n in outer) == 0

    print("x=210 amplitude regression: PASS")
    print(f"root cutoff: {ROOT}")
    print(f"M(210): {mertens}")
    print(
        "squarefree census: "
        f"{len(squarefree)} = {len(smooth)} smooth + {len(outer)} outer"
    )
    print(
        "outer matching: "
        f"{len(outer)} = {len(paired_states)} paired states "
        f"+ {len(survivors)} critical survivors"
    )
    print(
        "critical boundary amplitude: "
        f"{block_amplitudes} -> {sum(block_amplitudes)}"
    )
    print(
        "premature norms: "
        f"L1={l1_mass}, diagonal_energy={diagonal_energy}, "
        f"cross_term={cross_term}"
    )


if __name__ == "__main__":
    main()
