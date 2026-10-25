#!/usr/bin/env python3
"""Optional accelerated RH_Lean CORR-4 physical remainder stress test.

Dependencies: numpy, numba. Genuine Mobius through max_root^2-1,
exact odd q^2<R daughters, historical K_R. Finite evidence only.
Typical use: python3 scripts/corr4_oai_remainder_numba_20261024.py 10000
"""
import sys
import time

import numpy as np
from numba import njit


@njit
def mertens_sieve(n):
    least = np.zeros(n + 1, np.int32)
    mu = np.zeros(n + 1, np.int8)
    M = np.zeros(n + 1, np.int32)
    primes = np.zeros(n // 2 + 1, np.int32)
    mu[1] = 1
    ct = 0
    for i in range(2, n + 1):
        if least[i] == 0:
            least[i] = i
            primes[ct] = i
            ct += 1
            mu[i] = -1
        j = 0
        while j < ct:
            p = primes[j]
            z = i * p
            if z > n:
                break
            least[z] = p
            if i % p == 0:
                mu[z] = 0
                break
            mu[z] = -mu[i]
            j += 1
    for i in range(1, n + 1):
        M[i] = M[i - 1] + mu[i]
    return M, primes[:ct]


@njit
def scan(max_root, M, primes):
    historical = 0.0
    for y in range(55):
        historical = max(historical, (M[y] - 1) ** 2 / (y + 1))
    max_ratio = -1e30
    max_root_witness = 0
    failures_without_boundary = 0
    watch = np.array([56, 64, 244, 317, 1027, 5561, max_root])
    witnesses = np.zeros((len(watch), 8), np.float64)
    for R in range(56, max_root + 1):
        historical = max(historical, (M[R - 1] - 1) ** 2 / R)
        X = R * R - 1
        U = 0.0
        E = 0.0
        for p in primes:
            if p == 2:
                continue
            if p * p >= R:
                break
            y = X // (p * p)
            val = M[y]
            U += val / p
            E += val * val
        rough = M[R - 1] - M[X]
        B = rough - U
        ratio = (B * B - 2.25 * E) / (R * R * historical)
        if ratio > 0:
            failures_without_boundary += 1
        if ratio > max_ratio:
            max_ratio = ratio
            max_root_witness = R
        for j in range(len(watch)):
            if R == watch[j]:
                witnesses[j] = np.array([R, M[X], rough, U, B, E, historical, ratio])
    return max_ratio, max_root_witness, failures_without_boundary, witnesses


def main():
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    if R < 56:
        raise ValueError("root must be >=56")
    start = time.time()
    M, primes = mertens_sieve(R * R - 1)
    print("sieved", R * R - 1, "integers", round(time.time() - start, 3), "seconds")
    max_ratio, witness, failures, rows = scan(R, M, primes)
    print("roots", R - 55, "required C max", max_ratio,
          "at R", witness, "C=0 failures", failures)
    print("R, M(R^2-1), rough, U, B, E_low, historical K, required C")
    for row in rows:
        if row[0] > 0:
            print(", ".join(f"{v:.9f}" for v in row))
    print("total seconds", round(time.time() - start, 3))


if __name__ == "__main__":
    main()
