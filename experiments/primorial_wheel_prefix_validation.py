#!/usr/bin/env python3
"""Exhaustive validation for the seeded prime-comb prefix mechanism.

This companion to ``primorial_wheel_smooth_core.py`` tests Issue #166 at four
independent levels:

1. cross-check the linear sieve against trial division;
2. compare the fast seeded state with literal prime-operator composition;
3. verify exact Euler-product means on complete square-sensitive wheels;
4. verify the corrected state and nested-prefix identity at every integer in
   the first eight primorial blocks.

The default run checks 9,699,689 sites and prefixes, ending at W_8=9,699,690.
It is diagnostic evidence, not a Lean certificate or an asymptotic proof.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass

from primorial_wheel_smooth_core import (
    EXPECTED_ROWS,
    first_primes,
    initialized_state,
    linear_sieve,
    primorial_endpoints,
)


# Exact maximal-prefix results from the exhaustive default run.
# k, max|R_k(x)|, x, R_k(x), A_k(x), 2C_k(x)
EXPECTED_PREFIX_MAXIMA = (
    (1, 1, 2, -1, -1, 0),
    (2, 2, 5, -2, -2, 0),
    (3, 2, 13, -2, -4, -2),
    (4, 5, 95, 5, -1, -6),
    (5, 15, 1_637, -15, 49, 64),
    (6, 71, 24_185, -71, 513, 584),
    (7, 274, 355_733, -274, 4_966, 5_240),
    (8, 1_085, 6_481_601, 1_085, 59_095, 58_010),
)


@dataclass(frozen=True)
class OracleValue:
    mu: int
    omega: int
    largest_prime_factor: int


@dataclass(frozen=True)
class WheelRow:
    r: int
    cutoff: int
    period: int
    observed_sum: int
    expected_sum: int
    observed_mean: float
    product_mean: float


@dataclass(frozen=True)
class PrefixRow:
    k: int
    lower: int
    upper: int
    raw_mass: int
    smooth_core_mass: int
    delta: int
    euler_product: float
    max_abs: int
    max_x: int
    max_value: int
    raw_at_max: int
    twice_smooth_at_max: int
    max_ratio_x: float
    max_ratio_sqrt_x: float
    max_ratio_sqrt_local: float
    global_mertens_at_upper: int
    max_abs_global_mertens: int
    max_abs_global_mertens_x: int

    @property
    def length(self) -> int:
        return self.upper - self.lower

    @property
    def corrected_mass(self) -> int:
        return self.raw_mass - 2 * self.smooth_core_mass

    @property
    def euler_scale(self) -> float:
        return self.length * self.euler_product

    @property
    def alpha(self) -> float:
        return self.raw_mass / (2.0 * self.euler_scale)

    @property
    def beta(self) -> float:
        return self.smooth_core_mass / self.euler_scale


def trial_division_oracle(n: int) -> OracleValue:
    if n == 1:
        return OracleValue(mu=1, omega=0, largest_prime_factor=0)

    remaining = n
    omega = 0
    largest = 0
    squareful = False
    p = 2
    while p * p <= remaining:
        if remaining % p:
            p = 3 if p == 2 else p + 2
            continue
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        omega += 1
        largest = p
        squareful = squareful or exponent >= 2
        p = 3 if p == 2 else p + 2

    if remaining > 1:
        omega += 1
        largest = remaining

    mu = 0 if squareful else (-1 if omega % 2 else 1)
    return OracleValue(mu=mu, omega=omega, largest_prime_factor=largest)


def verify_oracle(data, limit: int) -> None:
    for n in range(1, limit + 1):
        expected = trial_division_oracle(n)
        actual = OracleValue(
            mu=int(data.mu[n]),
            omega=int(data.omega[n]),
            largest_prime_factor=int(data.largest_prime_factor[n]),
        )
        assert actual == expected, f"sieve oracle mismatch at n={n}"


def direct_operator_state(n: int, cutoff: int, primes: list[int]) -> int:
    """Literal composition of the seed and all genuine T_p through cutoff."""
    state = -1
    for p in primes:
        if p > cutoff:
            break
        if n % (p * p) == 0:
            return 0
        if n % p == 0:
            state = -state
    return state


def verify_operator_samples(
    endpoints: list[int],
    data,
    primes: list[int],
    samples_per_block: int,
) -> int:
    checks = 0
    for k in range(1, len(endpoints)):
        lower, upper = endpoints[k - 1], endpoints[k]
        cutoff = math.isqrt(upper)
        stride = max(1, (upper - lower) // samples_per_block)
        points = list(range(lower + 1, upper + 1, stride))
        if points[-1] != upper:
            points.append(upper)
        for n in points:
            assert initialized_state(n, cutoff, data) == direct_operator_state(
                n, cutoff, primes
            ), f"literal operator mismatch in block {k} at n={n}"
            checks += 1
    return checks


def verify_complete_wheels(
    data,
    primes: list[int],
    prime_count: int,
) -> list[WheelRow]:
    rows: list[WheelRow] = []
    primorial = 1
    expected_sum = -1
    product_mean = -1.0

    for r, p in enumerate(primes[:prime_count], start=1):
        primorial *= p
        period = primorial * primorial
        if period >= len(data.mu):
            raise ValueError(f"Q({p})={period:,} exceeds sieve limit")

        expected_sum *= (p - 1) ** 2
        product_mean *= (1.0 - 1.0 / p) ** 2
        observed_sum = sum(
            direct_operator_state(n, p, primes) for n in range(1, period + 1)
        )
        observed_mean = observed_sum / period

        assert observed_sum == expected_sum
        assert math.isclose(observed_mean, product_mean, rel_tol=1e-14, abs_tol=1e-14)
        rows.append(
            WheelRow(
                r=r,
                cutoff=p,
                period=period,
                observed_sum=observed_sum,
                expected_sum=expected_sum,
                observed_mean=observed_mean,
                product_mean=product_mean,
            )
        )
    return rows


def truncated_product(cutoff: int, primes: list[int]) -> float:
    product = 1.0
    for p in primes:
        if p > cutoff:
            break
        product *= (1.0 - 1.0 / p) ** 2
    return product


def evaluate_all_prefixes(
    endpoints: list[int],
    data,
    primes: list[int],
) -> list[PrefixRow]:
    rows: list[PrefixRow] = []
    global_mertens = int(data.mu[1])

    for k in range(1, len(endpoints)):
        lower, upper = endpoints[k - 1], endpoints[k]
        cutoff = math.isqrt(upper)
        raw = smooth = delta = 0
        max_abs = -1
        max_x = lower + 1
        max_value = raw_at_max = twice_smooth_at_max = 0
        max_ratio_x = max_ratio_sqrt_x = max_ratio_sqrt_local = 0.0
        max_abs_global = abs(global_mertens)
        max_abs_global_x = lower

        for n in range(lower + 1, upper + 1):
            mu_n = int(data.mu[n])
            state = initialized_state(n, cutoff, data)
            is_smooth_live = state != 0 and data.largest_prime_factor[n] <= cutoff
            corrected = -state if is_smooth_live else state

            # Pointwise squareful / unique-large-prime / smooth-core classification.
            assert corrected == mu_n, f"pointwise correction failed at n={n}"

            raw += state
            if is_smooth_live:
                smooth += state
            delta += mu_n
            global_mertens += mu_n

            residual = raw - 2 * smooth
            # Exact nested-prefix identity from Issue #166.
            assert residual == delta, f"prefix identity failed at x={n}"

            if abs(residual) > max_abs:
                max_abs = abs(residual)
                max_x = n
                max_value = residual
                raw_at_max = raw
                twice_smooth_at_max = 2 * smooth

            max_ratio_x = max(max_ratio_x, abs(residual) / n)
            max_ratio_sqrt_x = max(max_ratio_sqrt_x, abs(residual) / math.sqrt(n))
            max_ratio_sqrt_local = max(
                max_ratio_sqrt_local,
                abs(residual) / math.sqrt(n - lower),
            )

            if abs(global_mertens) > max_abs_global:
                max_abs_global = abs(global_mertens)
                max_abs_global_x = n

        row = PrefixRow(
            k=k,
            lower=lower,
            upper=upper,
            raw_mass=raw,
            smooth_core_mass=smooth,
            delta=delta,
            euler_product=truncated_product(cutoff, primes),
            max_abs=max_abs,
            max_x=max_x,
            max_value=max_value,
            raw_at_max=raw_at_max,
            twice_smooth_at_max=twice_smooth_at_max,
            max_ratio_x=max_ratio_x,
            max_ratio_sqrt_x=max_ratio_sqrt_x,
            max_ratio_sqrt_local=max_ratio_sqrt_local,
            global_mertens_at_upper=global_mertens,
            max_abs_global_mertens=max_abs_global,
            max_abs_global_mertens_x=max_abs_global_x,
        )
        assert row.corrected_mass == row.delta
        rows.append(row)

    return rows


def verify_regressions(rows: list[PrefixRow]) -> None:
    for row, endpoint in zip(rows, EXPECTED_ROWS):
        actual = (
            row.k,
            row.lower,
            row.upper,
            row.raw_mass,
            row.smooth_core_mass,
            row.delta,
        )
        assert actual == endpoint, f"endpoint regression mismatch: {actual}"

    for row, expected in zip(rows, EXPECTED_PREFIX_MAXIMA):
        actual = (
            row.k,
            row.max_abs,
            row.max_x,
            row.max_value,
            row.raw_at_max,
            row.twice_smooth_at_max,
        )
        assert actual == expected, f"prefix regression mismatch: {actual}"


def print_report(wheels: list[WheelRow], rows: list[PrefixRow]) -> None:
    print("\nComplete square-sensitive wheels")
    print(" r   p       Q(p)    sum sigma      mean/product")
    for row in wheels:
        print(
            f"{row.r:2d} {row.cutoff:3d} {row.period:10,d} "
            f"{row.observed_sum:12,d} {row.observed_mean:17.9e}"
        )

    print("\nPrimorial endpoints and Euler-product scale")
    print(" k        A_k       C_k   Delta          L*P    alpha     beta")
    for row in rows:
        print(
            f"{row.k:2d} {row.raw_mass:10,d} {row.smooth_core_mass:9,d} "
            f"{row.delta:7,d} {row.euler_scale:12.3f} "
            f"{row.alpha:8.4f} {row.beta:8.4f}"
        )

    print("\nExhaustive nested-prefix maxima")
    print(
        " k    max|R|         at x       A(x)      2C(x)       R(x) "
        " maxR/x      maxR/sqrt(x) maxR/sqrt(t)"
    )
    for row in rows:
        print(
            f"{row.k:2d} {row.max_abs:10,d} {row.max_x:12,d} "
            f"{row.raw_at_max:10,d} {row.twice_smooth_at_max:10,d} "
            f"{row.max_value:10,d} {row.max_ratio_x:11.4e} "
            f"{row.max_ratio_sqrt_x:12.6f} {row.max_ratio_sqrt_local:12.6f}"
        )

    print("\nGlobal Mertens path")
    print(" k     M(W_k)  max|M(x)|         at x")
    for row in rows:
        print(
            f"{row.k:2d} {row.global_mertens_at_upper:10,d} "
            f"{row.max_abs_global_mertens:10,d} "
            f"{row.max_abs_global_mertens_x:12,d}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blocks", type=int, default=8)
    parser.add_argument("--max-limit", type=int, default=10_000_000)
    parser.add_argument("--oracle-limit", type=int, default=100_000)
    parser.add_argument("--complete-wheel-primes", type=int, default=5)
    parser.add_argument("--operator-samples-per-block", type=int, default=5_000)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    block_primes = first_primes(args.blocks)
    endpoints = primorial_endpoints(block_primes)
    limit = endpoints[-1]
    if limit > args.max_limit:
        print(f"final primorial {limit:,} exceeds --max-limit", file=sys.stderr)
        raise SystemExit(2)
    if args.oracle_limit > limit:
        print("--oracle-limit exceeds sieve limit", file=sys.stderr)
        raise SystemExit(2)

    # The literal operators and Euler products need every prime through sqrt(W_k).
    operator_primes = first_primes(1)
    candidate = 3
    while operator_primes[-1] <= math.isqrt(limit):
        root = math.isqrt(candidate)
        if all(candidate % p for p in operator_primes if p <= root):
            operator_primes.append(candidate)
        candidate += 2
    if operator_primes[-1] > math.isqrt(limit):
        operator_primes.pop()

    print(f"building sieve through W_{args.blocks}={limit:,}...")
    data = linear_sieve(limit)

    print(f"cross-checking {args.oracle_limit:,} values by trial division...")
    verify_oracle(data, args.oracle_limit)

    operator_checks = verify_operator_samples(
        endpoints,
        data,
        operator_primes,
        args.operator_samples_per_block,
    )
    wheels = verify_complete_wheels(
        data,
        operator_primes,
        args.complete_wheel_primes,
    )
    rows = evaluate_all_prefixes(endpoints, data, operator_primes)
    verify_regressions(rows)
    print_report(wheels, rows)

    sites = limit - 1
    print("\nValidation summary")
    print(f" pointwise corrected-state checks: {sites:,}")
    print(f" exact nested-prefix checks:       {sites:,}")
    print(f" independent oracle checks:        {args.oracle_limit:,}")
    print(f" literal operator checks:          {operator_checks:,}")
    print(f" complete-wheel checks:            {len(wheels)}")
    print(" regression mismatches:            0")
    print(" failures:                         0")


if __name__ == "__main__":
    main()
