#!/usr/bin/env python3
"""Exact finite controls; these are separate from the universal Lean proofs."""

from collections import defaultdict
from math import isqrt


def prime(q):
    return q >= 2 and all(q % d for d in range(2, isqrt(q) + 1))


def cube_root(n):
    q = 0
    while (q + 1) ** 3 <= n:
        q += 1
    return q


def main():
    total_events = 0
    total_double_columns = 0
    for h in (1, 2, 10, 56, 128, 300, 556, 1024):
        for qmax in {cube_root(2 * h), cube_root(4 * h)}:
            columns = defaultdict(list)
            for root in range(h, 2 * h):
                for q in range(3, qmax + 1, 2):
                    if prime(q) and q * q < root and root % q:
                        n = (root * root - 1) // (q * q)
                        assert n * q * q < root * root <= (n + 1) * q * q
                        columns[n].append((root, q))
                        total_events += 1
            for events in columns.values():
                if qmax ** 3 <= 2 * h:
                    assert len(events) == 1
                assert len(events) <= 2
                if len(events) == 2:
                    (r, p), (s, q) = events
                    assert abs(r * q - s * p) == 1
                    assert r % 2 != s % 2
                    total_double_columns += 1
            occurrence_sum = sum(len(es) * (n % 7 + 1) for n, es in columns.items())
            image_sum = sum(n % 7 + 1 for n in columns)
            assert occurrence_sum <= 2 * image_sum
    assert 13 ** 3 <= 4 * 556
    assert (556 ** 2 - 1) // 11 ** 2 == (657 ** 2 - 1) // 13 ** 2 == 2554
    assert 11 ** 2 < 556 and 13 ** 2 < 657 and 556 % 11 and 657 % 13
    assert 556 * 13 == 657 * 11 + 1
    # Rays cannot be dropped from the hypotheses: two legal roots repeat a cutoff.
    assert (4400 ** 2 - 1) // 11 ** 2 == (5200 ** 2 - 1) // 13 ** 2
    assert 20 ** 3 <= 2 * 4000
    print(f"PASS finite controls: {total_events} events; {total_double_columns} double columns")
    print("PASS accepted collision and excluded-ray controls; no minimality claim")


if __name__ == "__main__":
    main()
