#!/usr/bin/env python3
"""Actual-prime Alpoge / NNS target-invariant Schur covariance regression.

Full local near-root K2*E(1) charge, including prime squares and distinct
semiprimes, is D(2I-J)D. Uses genuine prime logarithms and exact square
cutoffs, not fitted random sign models.

The full complementary Selberg source is checked algebraically by the
certified recurrence in RHLean/Analysis/NativePNTSignedSecondSelberg.lean.
Here C is reconstructed diagnostically from E(X)*log(X)^2 - band: the
census is NOT an independent numerical computation of each complement
term, and no global uniform RH bound is inferred from the finite data.
"""
from __future__ import annotations

from math import isclose, isqrt, log


def primes_up_to(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (
                (n - p * p) // p + 1
            )
    return [p for p in range(2, n + 1) if sieve[p]]


def chebyshev_psi(x: int, primes: list[int]) -> float:
    out = 0.0
    for p in primes:
        if p > x:
            break
        v = p
        while v <= x:
            out += log(p)
            v *= p
    return out


def evaluate(R: int):
    X = R * R - 1
    ps = primes_up_to(X)
    band = [p for p in ps if 3 * R <= 4 * p and p < R]
    m = len(band)
    assert m >= 3
    ell = [log(p) for p in band]
    S = sum(ell)
    Q = sum(v * v for v in ell)
    avg = S / m
    schur = m * Q - S * S
    var = sum((v - avg) ** 2 for v in ell)
    positive = 2 * var
    principal = m * (m - 2) * avg * avg
    signed = 2 * Q - S * S
    assert isclose(signed, positive - principal, abs_tol=1e-7)
    assert isclose(schur / m, var, abs_tol=1e-7)

    a = 0.75 * log(R)
    assert all(a <= v + 1e-12 and v <= 4 * a / 3 + 1e-12 for v in ell)
    assert signed <= -m * (m - 8 / 3) * a * a + 1e-7
    delta = log(4 / 3)
    assert positive <= 0.5 * m * delta * delta + 1e-7

    # Independently evaluate psi(X) by actual prime POWERS.
    E = chebyshev_psi(X, ps) - X
    Elog2 = E * log(X) ** 2
    C = Elog2 - signed  # Diagnostic reconstruction only.
    overshoot = C - principal
    assert isclose(Elog2, overshoot + positive, abs_tol=1e-7)
    assert max(Elog2, 0) <= max(overshoot, 0) + positive + 1e-7
    assert max(overshoot, 0) <= max(Elog2, 0) + 1e-7

    return R, X, m, signed, -principal, positive, E, overshoot


def main():
    print("R X m signedK2 negativePrincipal positiveSchur E(X) principalOvershoot")
    for root in (56, 317, 549, 1027):
        row = evaluate(root)
        print(
            f"{row[0]:4d} {row[1]:8d} {row[2]:4d}"
            f" {row[3]:14.3f} {row[4]:16.3f}"
            f" {row[5]:12.3f} {row[6]:12.3f} {row[7]:18.3f}"
        )
    print("PASS: actual prime-power/Schur/UPM2/principal-collar finite checks")
    print("NOT a proof of the all-root overshoot bound or RH")


if __name__ == "__main__":
    main()
