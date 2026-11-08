#!/usr/bin/env python3
"""Exact original-Mobius audit for the complete 2ab reciprocal-parent renewal.

No approximation, random signs, symbolic stand-ins, or fitted coefficients.
Independent physical replacement coefficients use a direct truncated-divisor
sieve, not the asserted quotient-fibre formula. Runs with Python stdlib only.
"""

from math import isqrt


def mobius_and_prefix(n):
    mu = [0] * (n + 1)
    mu[1] = 1
    is_composite = bytearray(n + 1)
    primes = []
    for v in range(2, n + 1):
        if not is_composite[v]:
            primes.append(v)
            mu[v] = -1
        for p in primes:
            j = v * p
            if j > n:
                break
            is_composite[j] = 1
            if v % p == 0:
                break
            mu[j] = -mu[v]
    M = [0] * (n + 1)
    s = 0
    for v in range(1, n + 1):
        s += mu[v]
        M[v] = s
    return mu, M


def audit(R):
    assert R >= 2
    X = R * R - 1
    mu, M = mobius_and_prefix(X)

    # The physical replacement kernel C_R(n) = sum_{d|n, d<R} mu(d)
    # is built independently of the quotient-renewal dictionary.
    C = [0] * (X + 1)
    for d in range(1, R):
        md = mu[d]
        if md:
            for n in range(d, X + 1, d):
                C[n] += md

    b = [0] * R
    for n in range(R, X + 1):
        b[X // n] += C[n]
    W = [0] * R
    for y in range(1, R):
        W[y] = (1 if y == R - 1 else 0) - b[y]

    assert sum(W[y] * M[y] for y in range(1, R)) == M[X]

    t = [0] * R
    for z in range(1, R):
        t[z] = M[X // z] - M[X // (z + 1)]
        # Complete EVERY quotient child: the finite Mobius-unit renewal.
        assert sum(M[z // k] for k in range(1, z + 1)) == 1

    # Independent physical coefficient and diagonal-kernel validation.
    for y in range((R + 1) // 2, R):
        assert W[y] == (y == R - 1) + t[y]
        assert abs(t[y]) <= 4
        for z in range((R + 1) // 2, R):
            K = sum(z // k == y for k in range(1, z + 1))
            assert K == int(z == y)

    assert sum(t[1:]) == M[X] - M[R - 1]
    good_A = [1, max(1, isqrt(R)), (R + 1) // 2]
    for A in good_A:
        completed = sum(t[z] * sum(M[z // k] for k in range(1, z + 1))
                        for z in range(A, R))
        expected = M[X // A] - M[R - 1]
        assert completed == expected
        diagonal = sum(t[z] * M[z] for z in range(A, R))
        abs_diagonal = sum(abs(t[z] * M[z]) for z in range(A, R))
        print(
            f"R={R} A={A} full_M={M[X]} completed={completed} "
            f"diagonal={diagonal} diagonal_L1={abs_diagonal}"
        )

    print(
        f"R={R} coefficient identity OK; high-half max |W|="
        f"{max(abs(W[y]) for y in range((R+1)//2, R))}"
    )


if __name__ == "__main__":
    for R in [56, 57, 317, 1027]:
        audit(R)
    print("PASS: exact original-Mobius twoAB renewal and physical coefficients")
