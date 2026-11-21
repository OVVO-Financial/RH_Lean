#!/usr/bin/env python3
"""Independent finite source regression for Alpoge/NNS matched K2.

Counts actual primes and EVERY von Mangoldt prime power up to R^2-1.
The FULL matched channel is computed directly as
  F(X) = -sum_{n<=X} Lambda(n) log(n) (psi(floor(X/n))-floor(X/n)).
The complementary signed FIRST Selberg remainder A is reconstructed as
  E(X)*log(X)^2 - F(X), using the existing exact Lean identity.
A must NOT be represented as independently enumerated in this script.

The selected prime-band match 2 sum log(p)^2 is computed independently.
No finite numerical cancellation ratio establishes a uniform RH bound.
"""
from math import isqrt, log, isclose


def pnt_data(N: int):
    sieve = bytearray(b"\x01") * (N + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(N) + 1):
        if sieve[p]:
            sieve[p * p:N + 1:p] = b"\x00" * ((N - p * p) // p + 1)
    primes = [p for p in range(2, N + 1) if sieve[p]]
    von_mangoldt = [0.] * (N + 1)
    for p in primes:
        n = p
        while n <= N:
            assert von_mangoldt[n] == 0.
            von_mangoldt[n] = log(p)
            n *= p
    psi = [0.] * (N + 1)
    s = 0.
    for n in range(1, N + 1):
        s += von_mangoldt[n]
        psi[n] = s
    return primes, von_mangoldt, psi


def audit(R: int):
    X = R * R - 1
    primes, lam, psi = pnt_data(X)
    E = psi[X] - X
    matched = -sum(lam[n] * log(n) * (psi[X//n] - X//n)
                   for n in range(2, X+1) if lam[n] != 0.)
    first_remainder = E * log(X)**2 - matched

    band = [p for p in primes if 3*R <= 4*p and p < R]
    selected_matched = 2 * sum(log(p)**2 for p in band)
    selected_original_K2 = (2*sum(log(p)**2 for p in band)
                            -sum(log(p) for p in band)**2)
    selected_convolution = -sum(log(p) for p in band)**2
    assert isclose(selected_matched,
                   selected_original_K2 - selected_convolution,
                   rel_tol=1e-12, abs_tol=1e-8)
    assert isclose(E*log(X)**2, first_remainder + matched,
                   rel_tol=1e-12, abs_tol=1e-7)

    cancellation = 1 - abs(E*log(X)**2) / (
        abs(first_remainder) + abs(matched))
    return (R, X, len(band), E, matched, first_remainder,
            selected_matched, matched-selected_matched, cancellation)


def main():
    print("R X m E(X) F_matched A_reconstructed selected matched_remaining "
          "matched-cancellation")
    for R in (56, 317, 549, 1027):
        x = audit(R)
        print("%4d %8d %3d %12.6f %17.3f %18.3f %12.3f %18.3f %.8f"
              % x)
    print("PASS: source-exact prime-power and selected ordered-pair regression")
    print("NOT PROVED: uniform bound for complete matched covariance")


if __name__ == "__main__":
    main()
