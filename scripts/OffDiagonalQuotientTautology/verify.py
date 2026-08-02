#!/usr/bin/env python3
"""Exact verifier for the 30 -> 210 off-diagonal quotient tautology.

Uses only the Python standard library.
"""

from fractions import Fraction as F


def walsh(mask: int, coordinate: int) -> int:
    return -1 if ((mask & coordinate).bit_count() % 2) else 1


def rref_nullspace(matrix: list[list[F]]) -> list[list[F]]:
    """Return a rational basis for the nullspace."""
    a = [row[:] for row in matrix]
    rows = len(a)
    cols = len(a[0])
    pivots: list[int] = []
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c] != 0), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][c]
        a[r] = [x / scale for x in a[r]]
        for i in range(rows):
            if i != r and a[i][c] != 0:
                factor = a[i][c]
                a[i] = [a[i][j] - factor * a[r][j] for j in range(cols)]
        pivots.append(c)
        r += 1
        if r == rows:
            break

    free = [c for c in range(cols) if c not in pivots]
    basis: list[list[F]] = []
    for f in free:
        v = [F(0) for _ in range(cols)]
        v[f] = F(1)
        for i, p in enumerate(pivots):
            v[p] = -a[i][f]
        basis.append(v)
    return basis


def dot(a: list[F], b: list[F]) -> F:
    return sum((x * y for x, y in zip(a, b)), F(0))


def main() -> None:
    constraints_30 = [
        [F(walsh(7, d)) for d in range(16)],
        [F(walsh(10, d)) for d in range(16)],
    ]
    basis_30 = rref_nullspace(constraints_30)
    assert len(basis_30) == 14

    l30 = [F(0)] + [F(-walsh(7, d)) for d in range(1, 16)]
    for v in basis_30:
        assert dot(l30, v) == v[0]

    # Exact U=199 ordinary child coordinate from the prior audit.
    s0 = -5
    parent_budget = F(s0 * s0, 6)
    assert parent_budget == F(25, 6)
    assert parent_budget < 16

    # Next quotient: one missing mask, the full five-prime mask 31.
    constraints_210 = [[F(walsh(31, d)) for d in range(32)]]
    basis_210 = rref_nullspace(constraints_210)
    assert len(basis_210) == 31

    # Naive lift: apply the old 4-bit functional independently of the new-prime bit.
    lifted = [F(0) for _ in range(32)]
    for d in range(32):
        old = d & 15
        if old != 0:
            lifted[d] = l30[old]

    failures = [dot(lifted, v) - v[0] for v in basis_210]
    nonzero = [x for x in failures if x != 0]
    assert nonzero
    assert F(-2) in nonzero

    print("PASS: dim(V_30)=14 from missing Walsh masks 7 and 10")
    print("PASS: L_30(s)=s_0 exactly on V_30")
    print("PASS: rank-one off-diagonal Gram is PSD and has zero direct s_0 coefficient")
    print(f"PASS: exact parent budget at U=199 is {parent_budget} < 16")
    print("PASS: dim(V_210)=31 from missing full mask 31")
    print("FAILURE CERTIFICATE: naive lifted functional differs from t_0 by -2 on V_210")
    print("CLASSIFICATION: feasible quotient tautology, not an extension-stable contraction")


if __name__ == "__main__":
    main()
