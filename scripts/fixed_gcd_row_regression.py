#!/usr/bin/env python3
"""Independent exact checks for FR4; finite evidence, not Lean certification."""

from math import gcd


def trial_mobius(n):
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


def main():
    r = 139
    x = r * r - 1
    mu = [0] + [trial_mobius(n) for n in range(1, x + 1)]
    rows = {}
    for a in range(1, r):
        for b in range(1, r):
            g = gcd(a, b)
            rows[g] = rows.get(g, 0) + mu[a] * mu[b] * (x // (a * b))
    assert [rows[g] for g in (1, 2, 3, 6)] == [74, -102, -32, 0]
    assert sum(mu[1:r]) == -3
    assert sum(mu) == 43
    assert sum(rows.values()) == -49 == 2 * sum(mu[1:r]) - sum(mu)
    # A second construction uses only the divisor identity, not factorization.
    inverse = [0] * (x + 1)
    inverse[1] = 1
    for d in range(1, x + 1):
        for n in range(2 * d, x + 1, d):
            inverse[n] -= inverse[d]
    assert inverse == mu
    print("PASS: R=139; gcd rows (1,2,3,6)=(74,-102,-32,0)")
    print("PASS: M(138)=-3; Q_139=-49; M(19320)=43")
    print("PASS: all 19320 Mobius coefficients agree by two constructions")
    print("Scope: no pointwise constant; no refutation of all-scale growth or RH")


if __name__ == "__main__":
    main()
