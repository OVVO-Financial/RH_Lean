#!/usr/bin/env python3
"""Preregistered exact finite regression, not a Lean or asymptotic certificate.

Domain: m=210, H=35..42. Compare trial-factor/divisor and independent sieve
floor-sum constructions. Retain the strict cutoff and equality endpoints.
Check original quadratic admission and an omitted-divisor negative control.
"""

from fractions import Fraction


def trial_mu(n):
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def divisor_jump(h, m):
    result = Fraction(1)
    for d in range(h + 1, m + 1):
        if m % d == 0:
            result *= Fraction(d, h) ** trial_mu(d)
    return result


def main():
    mu = [1] * 211
    mu[0] = 0
    prime = [True] * 211
    for p in range(2, 211):
        if prime[p]:
            for n in range(p, 211, p):
                mu[n] *= -1
                if n > p:
                    prime[n] = False
            for n in range(p * p, 211, p * p):
                mu[n] = 0
    assert all(mu[n] == trial_mu(n) for n in range(1, 211))

    def floor_tail(h, m):
        product = Fraction(1)
        for k in range(h + 1, m + 1):
            product *= Fraction(h, k) ** (mu[k] * (m // k))
        return product

    assert [p for p in range(2, 211) if prime[p] and 210 % p == 0] == [2, 3, 5, 7]
    assert mu[210] == 1
    for h in range(35, 43):
        ratio = divisor_jump(h, 210)
        assert ratio == Fraction(h * h, 1470)
        assert floor_tail(h, 210) / floor_tail(h, 209) == 1 / ratio
        n = 6 * ((h * h + 5) // 6)
        assert 8 * h < n and 4 * h <= 210 <= n // 2
    assert divisor_jump(38, 210) == Fraction(722, 735) < 1
    assert divisor_jump(39, 210) == Fraction(507, 490) > 1
    # Dropping the actual d=42 term reverses the first sign.
    assert divisor_jump(38, 210) * Fraction(42, 38) > 1
    print("PASS: 210 Mobius coefficients agree by two constructions")
    print("PASS: all eight strict-cutoff profiles, original floor steps and admissions")
    print("PASS: same m=210; exp(J_38)=722/735<1<507/490=exp(J_39)")
    print("PASS: omitted-divisor negative control changes the sign")
    print("Scope: all-head local obstruction; no selected membership or norm conclusion")


if __name__ == "__main__":
    main()
