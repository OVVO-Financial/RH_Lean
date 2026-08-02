#!/usr/bin/env python3
"""Exact rational verifier for the non-circular 30 -> 210 diagonal no-go.

No third-party dependencies are required.
"""

from fractions import Fraction as F
from math import isqrt

PRIMES = (2, 3, 5, 7)
MISSING_WALSH_MASKS = (7, 10)


def mobius(n: int) -> int:
    """Return the Möbius function by exact trial division."""
    x = n
    value = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            value = -value
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        value = -value
    return value


def divisibility_mask(n: int) -> int:
    return sum((1 << i) for i, p in enumerate(PRIMES) if n % p == 0)


def walsh(mask: int, coordinate: int) -> int:
    return -1 if ((mask & coordinate).bit_count() % 2) else 1


def compatible(vector: tuple[int, ...]) -> bool:
    assert len(vector) == 16
    return all(
        sum(walsh(mask, coordinate) * vector[coordinate] for coordinate in range(16)) == 0
        for mask in MISSING_WALSH_MASKS
    )


def prefix_budget_coefficients(U: int) -> tuple[int, ...]:
    """Return A_C(U)^2 + B_C(U)^2 for C subseteq {2,3,5}."""
    s = [0] * 16
    for n in range(31, U + 1):
        mu = mobius(n)
        if mu == 0:
            continue
        mask = divisibility_mask(n)
        for D in range(16):
            s[D] += mu * walsh(mask, D)

    coefficients = []
    for C in range(8):
        low = s[C]
        hit = s[C + 8]
        assert (low + hit) % 2 == 0
        assert (hit - low) % 2 == 0
        A = (low + hit) // 2
        B = (hit - low) // 2
        coefficients.append(A * A + B * B)
    return tuple(coefficients)


OUTPUT_TESTS: tuple[tuple[F, tuple[int, ...]], ...] = (
    (F(35, 24), (2, 0, -2, 0, 0, -2, 0, 2, 0, 2, 0, -2, -2, 0, 2, 0)),
    (F(35, 24), (2, 2, 0, 0, -2, -2, 0, 0, 0, 0, -2, -2, 0, 0, 2, 2)),
    (F(37, 24), (3, -3, 3, -3, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1)),
    (F(55, 24), (3, -1, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 3, -1, 3)),
    (F(55, 24), (3, -3, 1, -1, -1, 1, -3, 3, -1, 1, 1, -1, -1, 1, 1, -1)),
    (F(49, 48), (3, -1, 1, 1, -1, -1, -3, 1, -1, 3, 1, 1, -1, -1, 1, -3)),
    (F(25, 48), (3, -1, -1, -1, -1, -1, -1, 3, -1, 3, -1, -1, -1, -1, 3, -1)),
    (F(25, 48), (3, 1, 3, 1, -1, 1, -1, 1, -1, -3, -1, -3, -1, 1, -1, 1)),
    (F(4, 3), (3, 1, -1, 1, -1, -3, -1, 1, -1, 1, -1, -3, -1, 1, 3, 1)),
    (F(25, 24), (3, 1, 1, -1, -1, -3, 1, -1, -1, 1, -3, -1, -1, 1, 1, 3)),
    (F(85, 48), (3, -1, 1, -3, -1, -1, 1, 1, -1, 3, -3, 1, -1, -1, 1, 1)),
)

EXTENSION_TESTS: tuple[tuple[F, tuple[int, ...]], ...] = (
    (F(23, 6), (0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, 0, -2)),
    (F(23, 6), (0, 0, 2, -2, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, 2, -2)),
    (F(23, 6), (0, -2, 2, 0, 0, 2, -2, 0, 0, 2, -2, 0, 0, -2, 2, 0)),
    (F(1, 2), (0, -2, 0, 2, 2, 0, -2, 0, 0, 2, 0, -2, -2, 0, 2, 0)),
    (F(37, 24), (0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 0, -2, -2, 0, 0, 2)),
    (F(37, 24), (0, 0, -2, -2, -2, -2, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2)),
    (F(5, 2), (0, -2, -2, 0, 2, 0, 0, 2, 0, 2, 2, 0, -2, 0, 0, -2)),
)


def main() -> None:
    q = prefix_budget_coefficients(199)
    expected_q = (37, 565, 281, 3681, 109, 1813, 793, 7753)
    assert q == expected_q, (q, expected_q)

    for _, vector in OUTPUT_TESTS + EXTENSION_TESTS:
        assert compatible(vector), vector

    output_x = [F(0) for _ in range(16)]
    extension_x = [F(0) for _ in range(16)]
    extension_y = [F(0) for _ in range(8)]
    output_constant = F(0)

    for multiplier, vector in OUTPUT_TESTS:
        output_constant += multiplier * vector[0] * vector[0]
        for D in range(16):
            output_x[D] += multiplier * vector[D] * vector[D]

    for multiplier, vector in EXTENSION_TESTS:
        for D in range(16):
            extension_x[D] += multiplier * vector[D] * vector[D]
        for C in range(8):
            pair_energy = vector[C] * vector[C] + vector[C + 8] * vector[C + 8]
            extension_y[C] += 3 * multiplier * pair_energy

    assert output_constant == F(368, 3)

    # The non-circular condition is x_0 = 0. Every other child coefficient
    # produced by the weighted extension inequalities dominates the weighted
    # output coefficient exactly.
    assert extension_x[0] - output_x[0] == -F(368, 3)
    for D in range(1, 16):
        assert extension_x[D] >= output_x[D], (D, extension_x[D], output_x[D])

    # The weighted parent coefficients fit under the exact U=199 budget row.
    for C in range(8):
        assert extension_y[C] <= q[C], (C, extension_y[C], q[C])

    seed_budget = 2 * 8  # 2 * phi(30)
    assert output_constant > seed_budget

    print("PASS: all 18 test vectors lie in the exact 14-dimensional quotient")
    print(f"PASS: U=199 parent coefficients are {q}")
    print("PASS: child coefficient domination holds for D=1,...,15")
    print("PASS: the only child deficit is D=0, removed by x_0=0")
    print("PASS: weighted parent coefficients are bounded by the U=199 budget row")
    print(f"CERTIFICATE: every non-circular diagonal family requires budget >= {output_constant}")
    print(f"CONTRADICTION: {output_constant} > 2*phi(30) = {seed_budget}")


if __name__ == "__main__":
    main()
