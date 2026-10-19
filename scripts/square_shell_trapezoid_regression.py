#!/usr/bin/env python3
"""Exact Fraction regression for the corrected square-shell trapezoid.

No global Mertens energy estimate is inferred from the finite checks.
"""
from fractions import Fraction


def moebius_sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if prime[p]:
            for m in range(p, n + 1, p):
                mu[m] *= -1
                if m > p:
                    prime[m] = False
            for m in range(p * p, n + 1, p * p):
                mu[m] = 0
    return mu


def shell(mu, a, b):
    return sum(mu[n] for n in range(a + 1, b + 1))


def saw(mu, j, t):
    a = j * j
    upper = sum((t + 1 - m) * mu[a + m] for m in range(1, t + 1))
    lower = sum((t - m) * mu[a - m] for m in range(1, t + 1))
    return Fraction(upper - lower, 2 * t + 1)


def invalid_unsigned_saw(mu, j, t):
    a = j * j
    return Fraction(sum((t + 1 - abs(m)) * mu[a + m]
                        for m in range(-t, t + 1) if m), 2 * t + 1)


def main(max_root=64):
    mu = moebius_sieve((max_root + 1)**2 + max_root + 4)
    checks = 0
    invalid_cases = []
    for r in range(3, max_root + 1):
        for t in range(1, min(r - 2, 12) + 1):
            a, b = r*r, (r+1)**2
            sharp = shell(mu, a, b)
            assert sharp == sum(mu[n] for n in range(a+1, b))
            average = Fraction(sum(shell(mu, a+s, b+s)
                                   for s in range(-t, t+1)), 2*t+1)
            residual = sharp - average
            assert residual == saw(mu, r, t) - saw(mu, r+1, t)
            assert abs(saw(mu, r, t)) <= Fraction(t, 2)
            assert abs(saw(mu, r+1, t)) <= Fraction(t, 2)
            invalid = invalid_unsigned_saw(mu, r, t) - invalid_unsigned_saw(mu, r+1, t)
            if residual != invalid:
                invalid_cases.append((r, t, residual, invalid))
            checks += 1
    assert (5, 2, Fraction(4,5), Fraction(-1,5)) in invalid_cases
    H, T = 32, 5
    collar = sum(
        (shell(mu, r*r, (r+1)**2) -
         Fraction(sum(shell(mu, r*r+s, (r+1)**2+s)
                      for s in range(-T,T+1)),2*T+1))**2
        for r in range(H,2*H))
    assert collar <= H*T*T
    print(f"PASS: {checks} exact half-open Mobius shell telescopes")
    print(f"PASS: |B|<=T/2; {len(invalid_cases)} unsigned-saw failures")
    print("Witness r=5,T=2: corrected residual 4/5, invalid saw -1/5")
    print(f"PASS: H=32,T=5 collar energy {collar} <= {H*T*T}")


if __name__ == "__main__":
    main()
