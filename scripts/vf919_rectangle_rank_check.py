"""Exact native AMP coefficient witness; this checks finite arithmetic only."""

from fractions import Fraction
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def determinant3(m):
    a, b, c = m
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


def main():
    root = 317
    endpoint = root * root - 1
    owners = [q for q in range(3, root) if prime(q) and q * q < root]
    assert owners == [3, 5, 7, 11, 13, 17]
    denominator = prod(owners)
    assert denominator == 255255
    rows, columns = [7, 13, 19], [31, 37, 61]
    assert all(prime(p) and p % 3 == 1 for p in rows + columns)

    def physical_weight(n):
        return Fraction(n >= root) + sum(
            (Fraction(1, q) for q in owners if n <= endpoint // (q * q)),
            Fraction(),
        )

    for a in rows:
        for b in columns:
            assert a != b and a * b % 2 == 1 and 2 * a * b <= endpoint
    matrix = [[denominator * physical_weight(a * b) for b in columns] for a in rows]
    assert all(x.denominator == 1 for row in matrix for x in row)
    matrix = [[int(x) for x in row] for row in matrix]
    expected = [
        [230456, 230456, 470696],
        [470696, 470696, 451061],
        [470696, 451061, 427856],
    ]
    assert matrix == expected, matrix
    det = determinant3(matrix)
    assert det == -2309174383131000, det
    print(f"Native owners: {owners}; denominator: {denominator}")
    print(f"Native scaled AMP coefficient matrix: {matrix}")
    print(f"Determinant: {det}; excludes one occurrencewise centered rectangle.")


if __name__ == "__main__":
    main()
