#!/usr/bin/env python3
"""Diagnose canonical-parent congestion on the saturated #629 carrier.

Diagnostic only: numerical evidence is a route filter, never a proof.

The saturated frozen second-contact carrier from #629 can be written without
Boolean-face bookkeeping as squarefree integers

    n = q*m <= X,                 X = R^2 - 1,
    q = P+(n) < R,
    m = n/q > R,
    q*n > X.

Equivalently, for fixed owner q the canonical core m satisfies

    max(R, floor(X/q^2)) < m <= floor(X/q),
    P+(m) < q.

`CanonicalGapAncestryBridge.sourceParent` keeps q fixed and repeatedly strips
the largest prime factor of the core while core > q.  Hence an ancestry edge is
uniquely identified by its smooth child `(q,c)`; its parent is forced.

This script measures two different quantities:

1. raw edge multiplicity: how many saturated #629 seeds traverse `(q,c)`;
2. q^-2 weighted congestion: sum over traversed edges of 1/q^2.

The distinction is essential.  Raw pointwise multiplicity is empirically not
bounded or polylogarithmic, while the q^-2 weighted total is the quantity that
matches the compiled daughter-scale budget in
`SquareRootLowPrimeTSectorQ2Renormalization` and the complete-period first-
moment bound in `OutsidePrimeCompleteDeletionFirstMoment`.

Examples
--------
Exact full-carrier sweeps (memory is O(R^2)):

    python3 scripts/FrozenSecondContactReassembly/canonical_ancestry_congestion.py \
        100 200 500 1000 2000

Exact multiplicity of one chosen edge, without sieving to R^2:

    python3 scripts/FrozenSecondContactReassembly/canonical_ancestry_congestion.py \
        --edge 10000 103 105

The edge mode counts all squarefree ancestor products directly and is useful at
much larger R (for example 1e5 or 1e6) when a candidate congested edge is known.
"""

from __future__ import annotations

import argparse
import math
from array import array
from collections import Counter
from functools import lru_cache


def sieve_lpf_squarefree(n_max: int) -> tuple[array, bytearray, list[int]]:
    """Largest prime factor, squarefree flag, and primes through n_max."""
    lpf = array("I", [0]) * (n_max + 1)
    squarefree = bytearray([1]) * (n_max + 1)
    if n_max >= 0:
        squarefree[0] = 0
    primes: list[int] = []
    for p in range(2, n_max + 1):
        if lpf[p] != 0:
            continue
        primes.append(p)
        for k in range(p, n_max + 1, p):
            lpf[k] = p
        pp = p * p
        for k in range(pp, n_max + 1, pp):
            squarefree[k] = 0
    return lpf, squarefree, primes


def percentile(sorted_values: list[int], p: float) -> int:
    if not sorted_values:
        return 0
    i = min(len(sorted_values) - 1, math.ceil(p * len(sorted_values)) - 1)
    return sorted_values[max(i, 0)]


def exact_congestion(R: int) -> dict[str, object]:
    """Enumerate the exact saturated #629 carrier and all parent trajectories."""
    if R < 2:
        raise ValueError("R must be at least 2")
    X = R * R - 1
    lpf, squarefree, _primes = sieve_lpf_squarefree(X)
    edge_counts: Counter[tuple[int, int]] = Counter()
    seeds = 0
    total_steps = 0
    weighted = 0.0

    # n=q*m is the physical squarefree child integer.  These four tests are the
    # closed saturated #629 conditions from second_contact_window_scale.py.
    for n in range(R + 1, X + 1):
        if not squarefree[n]:
            continue
        q = lpf[n]
        if q == 0 or q >= R or n * q <= X:
            continue
        m = n // q
        if m <= R:
            continue

        seeds += 1
        c = m
        depth = 0
        while c > q:
            # c is squarefree and positive.  The canonical parent strips P+(c).
            edge_counts[(q, c)] += 1
            depth += 1
            c //= lpf[c]
        total_steps += depth
        weighted += depth / (q * q)

    counts = sorted(edge_counts.values())
    repeated = sum(v > 1 for v in counts)
    max_edge, max_mult = ((0, 0), 0)
    if edge_counts:
        max_edge, max_mult = max(edge_counts.items(), key=lambda kv: kv[1])

    return {
        "R": R,
        "X": X,
        "seeds": seeds,
        "edges": len(edge_counts),
        "steps": total_steps,
        "max_multiplicity": max_mult,
        "max_edge": max_edge,
        "mean_multiplicity": (total_steps / len(edge_counts)) if edge_counts else 0.0,
        "p50": percentile(counts, 0.50),
        "p95": percentile(counts, 0.95),
        "p99": percentile(counts, 0.99),
        "fraction_repeated": repeated / len(edge_counts) if edge_counts else 0.0,
        "weighted_congestion": weighted,
        "weighted_over_R": weighted / R,
    }


def primes_below(n: int) -> list[int]:
    if n <= 2:
        return []
    is_prime = bytearray([1]) * n
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n - 1) + 1):
        if is_prime[p]:
            is_prime[p * p : n : p] = b"\x00" * (((n - 1 - p * p) // p) + 1)
    return [p for p in range(2, n) if is_prime[p]]


def factor_squarefree_lpf(n: int) -> tuple[bool, int]:
    """Return (squarefree, largest prime factor), by trial division."""
    if n <= 0:
        return False, 0
    x = n
    largest = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            largest = p
            if x % p == 0:
                return False, largest
            while x % p == 0:
                x //= p
        p = 3 if p == 2 else p + 2
    if x > 1:
        largest = x
    return True, largest


def edge_multiplicity(R: int, q: int, c: int) -> int:
    """Exact number of #629 seeds whose canonical trajectory traverses (q,c).

    If `(q,c)` is a legal smooth ancestry child, every seed that reaches it is
    uniquely `m=c*d`, where d is squarefree and all prime factors of d lie
    strictly between P+(c) and q.  This avoids an O(R^2) sieve.
    """
    if R < 2 or q < 2 or c <= q:
        return 0
    q_squarefree, q_lpf = factor_squarefree_lpf(q)
    if not q_squarefree or q_lpf != q:
        return 0
    c_squarefree, c_lpf = factor_squarefree_lpf(c)
    if not c_squarefree or c_lpf >= q:
        return 0

    X = R * R - 1
    lower_m = max(R, X // (q * q))
    upper_m = X // q
    if c > upper_m:
        return 0

    # Count products d of eligible primes with lower_m < c*d <= upper_m.
    d_lo = lower_m // c + 1
    d_hi = upper_m // c
    if d_lo > d_hi:
        return 0
    eligible = [p for p in primes_below(q) if c_lpf < p < q]

    @lru_cache(maxsize=None)
    def count_le(i: int, limit: int) -> int:
        if limit < 1:
            return 0
        if i < 0:
            return 1  # empty product
        p = eligible[i]
        total = count_le(i - 1, limit)
        if p <= limit:
            total += count_le(i - 1, limit // p)
        return total

    return count_le(len(eligible) - 1, d_hi) - count_le(len(eligible) - 1, d_lo - 1)


def print_full_row(d: dict[str, object]) -> None:
    q, c = d["max_edge"]
    print(
        f"{d['R']:>7} {d['seeds']:>11} {d['edges']:>11} "
        f"{d['max_multiplicity']:>7} ({q:>5},{c:<8}) "
        f"{d['p50']:>4} {d['p95']:>4} {d['p99']:>4} "
        f"{100*d['fraction_repeated']:>8.3f}% "
        f"{d['weighted_congestion']:>12.5f} {d['weighted_over_R']:>10.6f}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "R", nargs="*", type=int, default=[100, 200, 500, 1000],
        help="exact full-carrier R values (requires O(max(R)^2) memory)",
    )
    parser.add_argument(
        "--edge", nargs=3, type=int, metavar=("R", "Q", "C"),
        help="count exact multiplicity of one edge (q,c) without an R^2 sieve",
    )
    args = parser.parse_args()

    if args.edge is not None:
        R, q, c = args.edge
        mult = edge_multiplicity(R, q, c)
        print(f"R={R} edge=({q},{c}) exact_multiplicity={mult}")
        return 0

    print(
        f"{'R':>7} {'seeds':>11} {'edges':>11} {'max':>7} {'edge(q,c)':>16} "
        f"{'p50':>4} {'p95':>4} {'p99':>4} {'repeat':>9} "
        f"{'sum depth/q^2':>12} {'/R':>10}"
    )
    for R in args.R:
        print_full_row(exact_congestion(R))
    print()
    print(
        "Interpretation: reject pointwise multiplicity bounds if `max` grows, but "
        "judge the cascade on `sum depth/q^2`, the scale-compatible congestion "
        "budget.  No numerical result is used as a proof."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
