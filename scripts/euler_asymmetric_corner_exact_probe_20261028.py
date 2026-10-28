#!/usr/bin/env python3
"""Original-Mobius regression for asymmetric floor, root corner, signed Gram.

All tests use exact integers.  No external analytic estimate is assumed,
and no finite test is interpreted as an asymptotic theorem.
"""
from math import isqrt


def mobius(n):
    mu = [0] * (n + 1)
    mu[1] = 1
    primes = []
    composite = bytearray(n + 1)
    for k in range(2, n + 1):
        if not composite[k]:
            primes.append(k)
            mu[k] = -1
        for p in primes:
            if k * p > n:
                break
            composite[k * p] = 1
            if k % p == 0:
                mu[k * p] = 0
                break
            mu[k * p] = -mu[k]
    return mu


def verify(R):
    assert R >= 2
    N, H, X = R - 1, isqrt(R), R * R - 1
    B = N - H
    mu = mobius(X)
    M = [0] * (X + 1)
    for n in range(1, X + 1):
        M[n] = M[n - 1] + mu[n]

    def kernel(a, b):
        return X // (a * b)

    corner = sum(mu[b] * (M[X // b] - M[N])
                 for b in range(B + 1, N + 1))
    literal_corner = sum(mu[a] * mu[b]
                         for b in range(B + 1, N + 1)
                         for a in range(N + 1, X // b + 1))
    assert corner == literal_corner
    assert abs(corner) <= H * (H + 2) <= 2 * R

    for b in range(B + 1, N + 1):
        assert R <= X // b <= R + H + 1
        for a in range(N + 1, X // b + 1):
            assert kernel(a, b) == 1
        row = sum(mu[a] * kernel(a, b) for a in range(1, N + 1))
        assert row == 1 - (M[X // b] - M[N])

    full = sum(mu[b] * sum(mu[a] * kernel(a, b)
                           for a in range(1, N + 1))
               for b in range(1, N + 1))
    asym = sum(mu[b] * sum(mu[a] * kernel(a, b)
                           for a in range(1, N + 1))
               for b in range(1, B + 1))
    omitted = full - asym
    diagonal = sum(M[b] ** 2 *
                   (kernel(b, b) - kernel(b + 1, b + 1))
                   for b in range(1, N + 1))
    signed_cross = sum(
        mu[b] * sum(
            M[a] * (kernel(a, b) - kernel(a + 1, b))
            for a in range(1, b)
        )
        for b in range(1, N + 1)
    )

    assert full == 2 * M[N] - M[X]
    assert full == diagonal + 2 * signed_cross
    assert omitted == M[N] - M[B] - corner
    assert asym == M[N] + M[B] - M[X] + corner
    assert asym == diagonal + 2 * signed_cross - omitted
    assert asym == (diagonal + 2 * signed_cross -
                    (M[N] - M[B]) + corner)
    return R, B, M[X], corner, asym, diagonal, signed_cross


if __name__ == "__main__":
    for R in (*range(2, 76), 100, 317, 500, 1000, 1027):
        outcome = verify(R)
        if R in {2, 3, 4, 5, 56, 100, 317, 500, 1000, 1027}:
            print("R=%s B=%s M(X)=%s corner=%s asym=%s D=%s cross=%s" % outcome)
    print("PASS exact asymmetric inversion, O(R) corner, signed diagonal/cross")
