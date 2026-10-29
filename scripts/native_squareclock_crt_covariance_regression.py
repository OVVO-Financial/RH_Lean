#!/usr/bin/env python3
"""Exact original-integer square-clock covariance and #919-kernel checks.

No randomness, floating point, OAI import, or zero-free hypothesis. Exact
Fractions ensure CRT cancellations are checked as equalities rather than
near-zero samples.

This test does NOT establish a new global Mobius exponent. It demonstrates
what the ordinary-integer CRT pays, and also identifies what it DOES NOT pay:
shared-factor correlations and the original #919 principal mean.
"""
from fractions import Fraction
from math import gcd, lcm


def mu_sieve(N: int):
    mu = [1] * (N + 1)
    mu[0] = 0
    for p in range(2, N + 1):
        if any(p % q == 0 for q in range(2, int(p**0.5) + 1)):
            continue
        for m in range(p, N + 1, p):
            mu[m] = -mu[m]
        for m in range(p*p, N + 1, p*p):
            mu[m] = 0
    return mu


def root_fraction(r: int, d: int) -> Fraction:
    return Fraction((r*r - 1) % d, d)


def centered_root_fraction(r: int, d: int) -> Fraction:
    mean = sum((root_fraction(s, d) for s in range(d)), Fraction()) / d
    return root_fraction(r, d) - mean


def square_clock_covariance(d: int, e: int) -> Fraction:
    return sum(
        (centered_root_fraction(r, d) *
         centered_root_fraction(r, e) for r in range(lcm(d, e))),
        Fraction(),
    )


def kernel36(t: int) -> int:
    c = lambda j: int(j % 3 == 1)
    return c(t) - c(t // 3) - c(t // 4) + c(t // 12)


def check():
    mu = mu_sieve(100)
    for d, e in ((5, 7), (7, 11), (15, 21), (21, 35), (35, 55),
                 (33, 77), (6, 35), (10, 21)):
        full = square_clock_covariance(d, e)
        if gcd(d, e) == 1:
            assert full == 0, (d, e, full)
        else:
            assert full != 0, (d, e, full)
        print(
            f"CRT d={d:>2} e={e:>2} gcd={gcd(d,e):>2}"
            f" mu_product={mu[d]*mu[e]:+d} covariance={full}"
        )

    # Incomplete interval bound, because the product is de-periodic,
    # every complete period cancels when gcd(d,e)=1 and each term has
    # norm <= 1. Hence the remainder is controlled by de.
    for d, e in ((5, 7), (7, 11), (6, 35), (10, 21)):
        assert gcd(d, e) == 1
        for start, L in ((0, 300), (31, 417), (123, 2000)):
            partial = sum(
                (centered_root_fraction(r, d) *
                 centered_root_fraction(r, e)
                 for r in range(start, start+L)), Fraction(),
            )
            assert abs(partial) <= d * e
    # The native period-36 quotient decoder has mean zero in its
    # quotient variable, but NOT after the physical root-square clock.
    assert sum(kernel36(j) for j in range(36)) == 0
    m = 7  # genuine split prime: a6(7) = -2
    physical_sum = sum(kernel36(((r*r-1) % (36*m)) // m)
                       for r in range(36*m))
    assert physical_sum == -36
    print("Original #919 m=7 physical root mean:", Fraction(physical_sum, 36*m))
    print("SUCCESS: coprime centered CRT covariance exact; "
          "shared factors nonzero; K36 square-root principal bias retained")


if __name__ == "__main__":
    check()
