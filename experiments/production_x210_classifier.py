#!/usr/bin/env python3
"""Production square-endpoint analogue of the x=210 amplitude census.

This script keeps the same first exact parent/child pairing used by
research/AMPLITUDE_X210_EXACT_EXAMPLE.md, but evaluates it at the actual
production endpoints X_R = R^2 - 1.

For every squarefree state n <= X_R with unique large prime p > R, write
n = c*p. Since p > R and n <= R^2 - 1, necessarily c < R. Pair the odd
state c*p with its 2-child 2*c*p whenever that child is still physical.
The unpaired states are exactly those with

    X_R/2 < c*p <= X_R,

and their signed amplitude is

    - sum_{c<R, c odd, squarefree} mu(c) * (H_R(c) - H_R(2c)),

where H_R(c) counts primes p > R with c*p <= X_R.

The x=210 hand model has zero survivor amplitude. The purpose here is to
check whether that last cancellation persists at genuine square endpoints.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class Row:
    c: int
    mu_c: int
    H_c: int
    H_2c: int
    survivor_count: int
    amplitude: int


def primes_upto(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    if limit >= 0:
        sieve[0] = False
    if limit >= 1:
        sieve[1] = False
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            for m in range(p * p, limit + 1, p):
                sieve[m] = False
    return [n for n, flag in enumerate(sieve) if flag]


def mobius_and_lpf(n: int, primes: list[int]) -> tuple[int, int]:
    if n == 1:
        return 1, 1
    x = n
    parity = 0
    lpf = 1
    for p in primes:
        if p * p > x:
            break
        if x % p:
            continue
        x //= p
        parity ^= 1
        lpf = p
        if x % p == 0:
            return 0, lpf
        while x % p == 0:
            x //= p
    if x > 1:
        parity ^= 1
        lpf = x
    return (-1 if parity else 1), lpf


def production_census(R: int) -> dict[str, object]:
    X = R * R - 1
    primes = primes_upto(X)
    high_primes = [p for p in primes if p > R]
    data = {n: mobius_and_lpf(n, primes) for n in range(1, X + 1)}

    outer = [n for n, (mu_n, lp) in data.items() if mu_n != 0 and lp > R]
    outer_set = set(outer)

    pairs = [
        (n, 2 * n)
        for n in outer
        if n % 2 == 1 and 2 * n in outer_set
    ]
    paired_states = {n for pair in pairs for n in pair}
    survivors = [n for n in outer if n not in paired_states]

    # Production analogue of the H(c)-H(2c) table in the x=210 note.
    rows: list[Row] = []
    for c in range(1, R):
        mu_c, _ = data[c]
        if mu_c == 0 or c % 2 == 0:
            continue
        H_c = sum(1 for p in high_primes if c * p <= X)
        H_2c = sum(1 for p in high_primes if 2 * c * p <= X)
        d = H_c - H_2c
        if d:
            rows.append(Row(c, mu_c, H_c, H_2c, d, -mu_c * d))

    # Exact reconstruction of every unpaired outer state by its unique high prime.
    reconstructed = []
    for row in rows:
        for p in high_primes:
            n = row.c * p
            if X // 2 < n <= X:
                reconstructed.append(n)

    assert sorted(reconstructed) == survivors
    assert all(X // 2 < n <= X and n % 2 == 1 for n in survivors)

    outer_amp = sum(data[n][0] for n in outer)
    survivor_amp = sum(data[n][0] for n in survivors)
    row_amp = sum(row.amplitude for row in rows)

    assert sum(data[a][0] + data[b][0] for a, b in pairs) == 0
    assert outer_amp == survivor_amp == row_amp

    return {
        "R": R,
        "X": X,
        "outer_count": len(outer),
        "pair_count": len(pairs),
        "paired_state_count": len(paired_states),
        "survivor_count": len(survivors),
        "survivor_negative": sum(data[n][0] == -1 for n in survivors),
        "survivor_positive": sum(data[n][0] == 1 for n in survivors),
        "outer_amplitude": outer_amp,
        "rows": rows,
    }


def print_census(result: dict[str, object]) -> None:
    print(f"R={result['R']} X_R={result['X']}")
    print(
        "outer="
        f"{result['outer_count']} = {result['paired_state_count']} paired "
        f"+ {result['survivor_count']} survivors"
    )
    print(
        "survivors: "
        f"{result['survivor_negative']} negative, "
        f"{result['survivor_positive']} positive, "
        f"signed amplitude={result['outer_amplitude']}"
    )
    print("c  mu(c)  H(c)  H(2c)  delta  amplitude")
    for row in result["rows"]:
        print(
            f"{row.c:2d} {row.mu_c:6d} {row.H_c:5d} {row.H_2c:6d} "
            f"{row.survivor_count:6d} {row.amplitude:10d}"
        )
    print()


def main() -> None:
    r15 = production_census(15)
    r56 = production_census(56)

    # Locked regression values for the first genuine square endpoint near 210
    # and for the repository's standard R >= 56 production threshold.
    assert r15["X"] == 224
    assert r15["outer_count"] == 104
    assert r15["pair_count"] == 31
    assert r15["survivor_count"] == 42
    assert r15["outer_amplitude"] == 4

    assert r56["X"] == 3135
    assert r56["outer_count"] == 1475
    assert r56["pair_count"] == 459
    assert r56["survivor_count"] == 557
    assert r56["outer_amplitude"] == 47

    print_census(r15)
    print_census(r56)
    print("production x=210 classifier regression: PASS")


if __name__ == "__main__":
    main()
