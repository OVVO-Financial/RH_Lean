#!/usr/bin/env python3
"""Exact rational matrix-rank stress test for #919's *unmasked* AMP weights.

The rank of a sum of q unmasked separable centered rectangles
  sum_{j=1}^q [f_j(a) g_j(b) - u_j(a) v_j(b)]
is at most 2q. The tests below therefore give FINITE lower bounds for
that restricted occurrencewise representation. They say nothing about
coupled OAI masks, norm-fiber summation, or the genuine ideal Hecke row.
"""
from fractions import Fraction
from math import isqrt


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def exact_rank(matrix: list[list[Fraction]]) -> int:
    """Fraction-preserving Gaussian elimination; no floating tolerance."""
    a = [row[:] for row in matrix]
    nrows, ncols = len(a), len(a[0])
    pivot = 0
    for col in range(ncols):
        index = next((i for i in range(pivot, nrows) if a[i][col]), None)
        if index is None:
            continue
        a[pivot], a[index] = a[index], a[pivot]
        scale = a[pivot][col]
        a[pivot] = [x / scale for x in a[pivot]]
        for i in range(pivot + 1, nrows):
            if a[i][col]:
                multiplier = a[i][col]
                a[i] = [x - multiplier * y
                        for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == nrows:
            break
    return pivot


def native_weight(root: int, norm: int, owners: list[int]) -> Fraction:
    endpoint = root * root - 1
    return Fraction(norm >= root) + sum(
        (Fraction(1, q) for q in owners if norm <= endpoint // (q * q)),
        Fraction(0),
    )


def check(root: int, size: int, expected_parent: int, expected_centered: int) -> None:
    endpoint = root * root - 1
    owners = [q for q in range(3, isqrt(root) + 1, 2)
              if prime(q) and q * q < root]
    primes = [p for p in range(7, 1000) if prime(p) and p % 3 == 1]
    rows, cols = primes[:size], primes[size:2 * size]
    assert len(cols) == size
    assert set(rows).isdisjoint(cols)
    assert 2 * max(rows) * max(cols) <= endpoint
    assert all(prime(p) and p % 3 == 1 for p in rows + cols)
    # Each site is a squarefree odd semiprime, hence a genuine native
    # owner-two unmasked parent/returned-child occurrence on this slice.
    parent = [[native_weight(root, a * b, owners) for b in cols]
              for a in rows]
    centered = [[native_weight(root, a * b, owners) -
                 native_weight(root, 2 * a * b, owners) for b in cols]
                for a in rows]
    rp, rc = exact_rank(parent), exact_rank(centered)
    assert (rp, rc) == (expected_parent, expected_centered), (root, rp, rc)
    print(f'R={root}, size={size}, parent_rank={rp}, '
          f'centered_rank={rc}, '
          f'min_unmasked_centered_rectangles={(rc + 1) // 2}')


def main() -> None:
    check(317, 10, 9, 9)
    check(548, 16, 10, 13)
    check(1027, 16, 13, 14)
    check(3000, 16, 12, 15)
    print('Finite unmasked-rank lower bounds only; no OAI masked-row impossibility theorem.')


if __name__ == '__main__':
    main()
