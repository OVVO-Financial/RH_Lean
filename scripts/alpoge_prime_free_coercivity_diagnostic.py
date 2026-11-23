#!/usr/bin/env python3
"""Exact prime-free stress test of the existing square-clock difference algebra.

This is a diagnostic, not a theta-cover constructor or an RH implication.
All identities and sign choices below use integer arithmetic.  The finite
Rademacher average exhausts the uniform sign cube; the seeded sign sequence
is only a reproducible empirical sample, not a proof about randomness.

Keep separate: lattice side L, derivative order k, site count L^2, raw sign
sum, pointwise jet, and the complete additive/floor commutator telescope.
The jet at L^2-1 uses its explicit k-site halo beyond the square clock.
No prime factorization, Mobius function, Euler product or zeta input occurs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from math import comb, gcd, isqrt
from pathlib import Path
import random


def coefficients(k: int) -> list[int]:
    return [(-1 if (k - j) % 2 else 1) * comb(k, j) for j in range(k + 1)]


def jet(values: list[int], k: int, start: int) -> int:
    return sum(c * values[start + j] for j, c in enumerate(coefficients(k)))


def recursive_jet(values: list[int]) -> int:
    row = values[:]
    while len(row) > 1:
        row = [b - a for a, b in zip(row, row[1:])]
    return row[0]


def quadratic_rotation_sign(n: int) -> int:
    # For n>0, exactly sgn(sin(pi*sqrt(2)*n^2)); the value at 0 is set to +1.
    # sqrt(2)*n^2 is irrational for n>0, so no numerical near-zero decision.
    return -1 if isqrt(2 * n**4) % 2 else 1


def rotation_half_mask(n: int) -> int:
    # 1_{frac(sqrt(3)*n)<1/2}, evaluated exactly by integer square roots.
    return int(isqrt(12 * n * n) - 2 * isqrt(3 * n * n) == 0)


def commutator(values: list[int], p: int, n: int) -> int:
    def floor_difference(t: int) -> int:
        return values[t] - values[t // p]

    def difference(t: int) -> int:
        return values[t + 1] - values[t]

    return (floor_difference(n + 1) - floor_difference(n)) - (
        difference(n) - difference(n // p)
    )


def max_window_sum(values: list[int], width: int) -> int:
    current = sum(values[:width])
    result = abs(current)
    for i in range(width, len(values)):
        current += values[i] - values[i - width]
        result = max(result, abs(current))
    return result


def finite_cube_audit(k: int) -> dict:
    c = coefficients(k)
    total_square = 0
    maximum = 0
    count = 0
    for signs in product((-1, 1), repeat=k + 1):
        value = sum(a * b for a, b in zip(c, signs))
        assert value == recursive_jet(list(signs))
        total_square += value * value
        maximum = max(maximum, abs(value))
        count += 1
    mean_square = Fraction(total_square, count)
    assert mean_square == sum(a * a for a in c) == comb(2 * k, k)
    assert maximum == sum(abs(a) for a in c) == 2**k
    return {
        "k": k,
        "sign_assignments": count,
        "maximum_absolute_jet": maximum,
        "exact_mean_square_jet": int(mean_square),
        "binomial_2k_k": comb(2 * k, k),
    }


def covariance_audit(k: int) -> dict:
    c = coefficients(k)
    values = []
    for h in range(k + 1):
        value = sum(c[j] * c[j - h] for j in range(h, k + 1))
        assert value == (-1)**h * comb(2 * k, k + h)
        values.append(value)
    return {"k": k, "shift_covariances_0_through_k": values}


def matrix_product(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[sum(A[i][s] * B[s][j] for s in range(2)) for j in range(2)]
            for i in range(2)]


def hs(A: list[list[Fraction]]) -> Fraction:
    # Upstream Formalism.REAL.hs is the SQUARED Frobenius norm.
    return sum(value * value for row in A for value in row)


def coercivity_conditioning_audit(k: int) -> dict:
    t = Fraction(1, 2**k)
    X = [[Fraction(0), Fraction(0)], [t, Fraction(0)]]
    A = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    AX = matrix_product(A, X)
    XA = matrix_product(X, A)
    comm = [[AX[i][j] - XA[i][j] for j in range(2)] for i in range(2)]
    assert comm == X
    assert hs(A) == 1 and hs(comm) == t * t
    assert hs(A) / hs(comm) == 4**k
    # The general coordinate proof is in the report.  These rational samples
    # verify its matrix expansion without asserting an exhaustive proof.
    for a in range(-3, 4):
        for b in range(-3, 4):
            B = [[Fraction(0), Fraction(a)], [Fraction(0), Fraction(b)]]
            BX, XB = matrix_product(B, X), matrix_product(X, B)
            C = [[BX[i][j] - XB[i][j] for j in range(2)] for i in range(2)]
            assert C == [[t * a, Fraction(0)], [t * b, -t * a]]
            assert hs(C) == t * t * (2 * a * a + b * b)
            assert hs(B) <= 4**k * hs(C)
    return {
        "k": k, "t": str(t), "matrix_dimension": 2,
        "hs_witness": str(hs(A)), "hs_commutator": str(hs(comm)),
        "sharp_squared_norm_coercivity_constant": 4**k,
        "sharp_norm_coercivity_constant": 2**k,
        "matrix_entry_denominator": 2**k,
        "cyclic_pair_determinant": str(t),
    }


def square_audit(L: int) -> dict:
    k = L
    N = L * L
    start = N - 1
    length = N + k  # explicit jet halo, with no periodic extension
    rng = random.Random(20261122 + L)
    signals = {
        "alternating": [1 if n % 2 == 0 else -1 for n in range(length)],
        "quadratic_rotation_sqrt2": [quadratic_rotation_sign(n) for n in range(length)],
        "seeded_sign_sample": [rng.choice((-1, 1)) for _ in range(length)],
        "constant_nullmode_control": [1] * length,
    }
    mask = [rotation_half_mask(n) for n in range(length)]
    signals["half_masked_quadratic_rotation"] = [
        mask[n] * signals["quadratic_rotation_sqrt2"][n] for n in range(length)]
    signals["half_masked_seeded_sign_sample"] = [
        mask[n] * signals["seeded_sign_sample"][n] for n in range(length)]
    rows = []
    for name, values in signals.items():
        raw_sum = sum(values[:N])
        point_jet = jet(values, k, start)
        assert point_jet == recursive_jet(values[start:start + k + 1])
        rectangle = sum(commutator(values, L, L * m + r)
                        for m in range(L) for r in range(L))
        endpoint = (L - 1) * (values[L] - values[0])
        assert rectangle == endpoint
        assert abs(rectangle) <= 2 * (L - 1)
        if name == "alternating":
            assert abs(point_jet) == 2**k
            assert raw_sum == 0  # every displayed L is even
            assert max_window_sum(values[:N], L) == 0
        if name == "constant_nullmode_control":
            assert raw_sum == N and point_jet == rectangle == 0
        rows.append({
            "signal": name,
            "raw_square_sum": raw_sum,
            "max_absolute_L_window_sum_inside_square": max_window_sum(values[:N], L),
            "signed_point_jet_at_X_L": point_jet,
            "absolute_point_jet_at_X_L": abs(point_jet),
            "signed_complete_commutator_rectangle": rectangle,
            "exact_endpoint_expression": endpoint,
        })
    c = coefficients(k)
    coefficient_gcd = 0
    for value in c:
        coefficient_gcd = gcd(coefficient_gcd, abs(value))
    assert coefficient_gcd == 1
    normalized_denominators = [Fraction(value, 2**k).denominator for value in c]
    assert max(normalized_denominators) == 2**k
    # Interior rows of the exact k-th-difference matrix on N input sites.
    response_rows = N - k
    return {
        "L": L, "k": k, "site_count": N, "X_L": start,
        "input_length_including_halo": length,
        "coefficient_l1": 2**k,
        "coefficient_squared_l2": comb(2 * k, k),
        "coefficient_gcd": coefficient_gcd,
        "denominator_after_dividing_jet_by_2_to_k": max(normalized_denominators),
        "interior_response_rows": response_rows,
        "independent_sign_expected_total_response_energy": response_rows * comb(2 * k, k),
        "rotation_half_mask_active_sites": sum(mask[:N]),
        "masked_independent_sign_exact_point_jet_second_moment": sum(
            c[j] * c[j] * mask[start + j] for j in range(k + 1)),
        "signals": rows,
    }


def run() -> dict:
    # A concrete failure of multiplicativity for the rotation sequence.
    witness = next((a, b) for a in range(2, 30) for b in range(2, 30)
                   if gcd(a, b) == 1 and quadratic_rotation_sign(a * b)
                   != quadratic_rotation_sign(a) * quadratic_rotation_sign(b))
    a, b = witness
    return {
        "schema": "alpoge-prime-free-coercivity-diagnostic-v1",
        "arithmetic": "exact integers and rational finite averages; no prime factorization",
        "uniform_sign_cube": [finite_cube_audit(k) for k in range(1, 11)],
        "overlapping_jet_covariances": [covariance_audit(k) for k in (1, 2, 4, 8)],
        "two_by_two_coercivity_conditioning": [coercivity_conditioning_audit(k)
                                               for k in (1, 4, 8, 16, 32, 64)],
        "quadratic_rotation_nonmultiplicative_witness": {
            "a": a, "b": b, "sign_ab": quadratic_rotation_sign(a * b),
            "sign_a_times_sign_b": quadratic_rotation_sign(a) * quadratic_rotation_sign(b),
        },
        "density_control": "deterministic half-density circle-rotation mask; no claim to match the actual Gz weights",
        "squares": [square_audit(L) for L in (4, 8, 16, 32, 64)],
        "conclusions": {
            "pointwise_uniform_polynomial_jet_bound": "REFUTED_BY_EXACT_ALTERNATING_CONTROL",
            "independent_sign_jet_second_moment": "EXACT_BINOMIAL_2K_K_RETAINS_EXPONENTIAL_COST",
            "complete_floor_commutator_telescope": "EXACT_LINEAR_BOUND_ON_THIS_DIFFERENT_OBSERVABLE",
            "finite_dimensional_coercivity": "HOLDS_WITH_SHARP_PARAMETER_DEPENDENT_CONSTANT_4_TO_K",
            "theta_cover_hypotheses": "NOT_INSTANTIATED_BY_THIS_DIAGNOSTIC",
            "coercivity_theorem_refutation": False,
            "rh_implication": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="save the exact reproducible JSON result")
    args = parser.parse_args()
    result = run()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
        print(json.dumps({"output": str(args.output), "exact_sign_cube_orders": 10,
                          "square_sides": [4, 8, 16, 32, 64],
                          "status": "EXACT_DIAGNOSTIC_CHECKS_PASSED"}))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
