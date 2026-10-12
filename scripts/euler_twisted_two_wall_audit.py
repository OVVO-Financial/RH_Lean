#!/usr/bin/env python3
"""Audit the exact twisted Euler two-wall identity for the finite-C kernel.

Runs against actual Mobius coefficients with a standalone sieve.
    python3 scripts/euler_twisted_two_wall_audit.py
All assertions are integer-exact except printed decimal normalizations.
No finite C/A theorem or RH result is asserted.
"""
from math import isqrt, sqrt


def sieve_mobius(N):
    prime = bytearray(b"\x01") * (N + 1)
    prime[0] = prime[1] = 0
    for p in range(2, isqrt(N) + 1):
        if prime[p]:
            for n in range(p*p, N+1, p):
                prime[n] = 0
    primes = [p for p in range(2, N + 1) if prime[p]]
    mu = [1] * (N + 1)
    mu[0] = 0
    for p in primes:
        for n in range(p, N + 1, p):
            mu[n] = -mu[n]
        for n in range(p*p, N + 1, p*p):
            mu[n] = 0
    M = [0] * (N + 1)
    for n in range(1, N + 1):
        M[n] = M[n-1] + mu[n]
    return primes, mu, M


def two_walls(R, p, mu):
    X = R*R - 1
    if not 2 <= p <= X:
        raise ValueError((R, p))
    # Cross the historical wall, with the p child still in range.
    cross = sum(2*mu[n]
                for n in range(1, min(R-1, X//p) + 1)
                if n % p != 0 and R <= p*n)
    # Exit the physical product cutoff: no p child remains.
    exit_ = sum((1 if n < R else -1) * mu[n]
                for n in range(X//p + 1, X + 1) if n % p != 0)
    return cross, exit_


def main():
    roots = (10, 56, 317)
    primes, mu, M = sieve_mobius(max(R*R-1 for R in roots))
    prime_set = set(primes)
    print("root,p,historical_cross,upper_exit,Q_R")
    for R in roots:
        X = R*R-1
        Q = 2*M[R-1] - M[X]
        K = max((M[y]-1)**2/(y+1) for y in range(R))
        isolated = sum(X//2 < p <= X for p in primes)
        pnext = next(p for p in primes if p >= R)
        pivot_list = [2, pnext]
        if R == 317:
            pivot_list.extend([439, 1009])
        for p in pivot_list:
            assert p in prime_set
            cross, exit_ = two_walls(R, p, mu)
            assert cross + exit_ == Q, (R, p, cross, exit_, Q)
            if p < R:
                assert cross == 2*M[R-1] and exit_ == -M[X]
            else:
                assert cross == 2*M[X//p]
            print(f"{R},{p},{cross},{exit_},{Q}")
        print(f"R={R} X={X} isolated_upper_half_primes={isolated} "
              f"K_R={K:.8g} R_sqrt_K={R*sqrt(K):.8f} "
              f"C_R={abs(Q)/(R*sqrt(K)):.9f}")
    print("PASS: all finite twisted Euler two-wall identities checked.")


if __name__ == "__main__":
    main()
