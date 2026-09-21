#!/usr/bin/env python3
"""Exact arithmetic for STOKES_LOWER_MERTENS_SYNTHESIS_OBSTRUCTION.md.

This verifies finite sums, explicit series tails, the squarefree wheel density,
and the final rational constant comparisons. It does NOT formalize the analytic
argument, prove Ramare's or Hurst's external theorems, or produce a finite
counterexample to the synthesis. Decimal output is display-only.

Run from the repository root:
    python3 scripts/stokes_lower_mertens_synthesis_audit.py
"""

from array import array
from fractions import Fraction as F
from math import factorial, isqrt, prod


SCALE = 10**18
COEFFICIENT_CUTOFF = 2_000_000
PRIME_SUM_CUTOFF = 100_000
KAPPA_CUTOFF = 1_000
WHEEL_CUTOFF = 2_000


def ceil_div(n: int, d: int) -> int:
    return (n + d - 1) // d


def primes_and_mobius(limit: int) -> tuple[list[int], array]:
    prime = bytearray(b"\x01") * (limit + 1)
    prime[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p * p :: p] = b"\x00" * len(prime[p * p :: p])
    primes = [p for p in range(2, limit + 1) if prime[p]]
    mu = array("b", [1]) * (limit + 1)
    mu[0] = 0
    for p in primes:
        for n in range(p, limit + 1, p):
            mu[n] = -mu[n]
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    return primes, mu


def verify_mobius_divisor_identity(mu: array, limit: int = 2_000) -> None:
    """Check the defining Dirichlet-convolution identity independently."""
    convolution = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for n in range(d, limit + 1, d):
            convolution[n] += mu[d]
    assert convolution[1] == 1
    assert all(v == 0 for v in convolution[2:])


def verify_odd_rounding(primes: list[int]) -> None:
    """Finite regression for the all-R algebraic lemma proved in the note."""
    for root in range(56, 3_001):
        for q in primes:
            if q * q >= root:
                break
            if q == 2:
                continue
            nearest = (root + q // 2) // q
            daughter = (root * root - 1) // (q * q)
            distance = abs(daughter - (nearest * nearest - 1))
            assert distance * q * q <= root * (q - 1) + 2 * q * q


def main() -> None:
    primes, mu = primes_and_mobius(COEFFICIENT_CUTOFF)
    verify_mobius_divisor_identity(mu)
    verify_odd_rounding(primes)

    # Each rounded summand is an upper bound, with exact integer arithmetic.
    coefficient_units = 0
    mertens = 0
    prime_index = 0
    for n in range(1, COEFFICIENT_CUTOFF + 1):
        if prime_index < len(primes) and n == primes[prime_index]:
            if n != 2:
                coefficient_units += ceil_div(SCALE * (mertens - 1) ** 2, n**3)
            prime_index += 1
        mertens += mu[n]
    coefficient_prefix_upper = F(coefficient_units, SCALE)

    # Ramare, Theorem 1.1, gives |M(x)| < .013*x/log(x) above 1,078,853.
    # For p > 2,000,000, |M(p-1)-1| <= .014*p/log(p).
    # Enlarge the prime tail to all integers and integrate from the cutoff.
    # log(2,000,000) > 13 follows from e < 3 and 3**13 < 2,000,000.
    assert 3**13 < COEFFICIENT_CUTOFF
    coefficient_upper = coefficient_prefix_upper + F(14, 1_000) ** 2 / 13
    assert coefficient_upper < F(92, 1_000)

    odd = [p for p in primes if 2 < p <= PRIME_SUM_CUTOFF]
    rho_upper = F(sum(ceil_div(SCALE, p**2) for p in odd), SCALE)
    rho_upper += F(1, PRIME_SUM_CUTOFF)
    tau_lower = F(sum(SCALE // p**3 for p in odd), SCALE)
    tau_upper = F(sum(ceil_div(SCALE, p**3) for p in odd), SCALE)
    tau_upper += F(1, 2 * PRIME_SUM_CUTOFF**2)
    assert rho_upper < F(2_023, 10_000)
    assert F(497, 10_000) < tau_lower
    assert tau_upper < F(498, 10_000)

    # kappa = sum_q q^-4 + 2*sum_q q^-3*sum_{p<q} p^-1.
    # For q>L, sum_{p<q}1/p <= 1+log(q), and the tail is at most
    # 1/(3*L^3) + (log(L)+3/2)/L^2. Use log(1000)<7.
    assert sum((F(7**k, factorial(k)) for k in range(12)), F(0)) > 1_000
    harmonic_units = 0
    kappa_units = 0
    for p in odd:
        if p > KAPPA_CUTOFF:
            break
        kappa_units += ceil_div(SCALE, p**4)
        kappa_units += ceil_div(2 * harmonic_units, p**3)
        harmonic_units += ceil_div(SCALE, p)
    kappa_upper = F(kappa_units, SCALE)
    kappa_upper += F(1, 3 * KAPPA_CUTOFF**3)
    kappa_upper += F(17, 2 * KAPPA_CUTOFF**2)
    assert kappa_upper < F(27, 1_000)

    # A finite squarefree mask gives a uniform bound on every interval.
    # Its (possibly enormous) period contributes only a fixed endpoint error.
    density = prod(F(p * p - 1, p * p) for p in primes if p <= WHEEL_CUTOFF)
    delta = F(608, 1_000)
    assert density < delta

    diagonal_upper = delta * (1 + 2 * F(498, 10_000) + F(27, 1_000))
    gap_bound = F(882, 1_000)
    assert diagonal_upper + F(92, 1_000) < gap_bound**2
    rho = F(2_023, 10_000)
    tau = F(497, 10_000)
    square_limsup_upper = (gap_bound + delta * (rho - tau)) / (1 - rho)
    assert square_limsup_upper < F(1_223, 1_000)
    assert F(1_223, 1_000) + delta == F(1_831, 1_000)
    assert F(1_831, 1_000) < F(1_837_625, 1_000_000)

    print("All finite and rational checks passed. Not a Lean disproof.")
    for label, value in (
        ("coefficient prefix upper", coefficient_prefix_upper),
        ("coefficient full-series upper (using Ramare)", coefficient_upper),
        ("rho upper", rho_upper),
        ("tau lower", tau_lower),
        ("tau upper", tau_upper),
        ("kappa upper", kappa_upper),
        ("finite wheel density", density),
        ("asymptotic diagonal upper", diagonal_upper),
        ("square-endpoint limsup upper if synthesis holds", square_limsup_upper),
    ):
        print(f"{label}: {float(value):.15f}")


if __name__ == "__main__":
    main()
