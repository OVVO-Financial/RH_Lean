#!/usr/bin/env python3
"""Falsifiable finite census for the actual CORR-4 compensated physical remainder.

This is not an all-root proof. Uses X=R^2-1, only genuine odd prime q with
q*q<R, a historical envelope K=max_{0<=y<R}(M(y)-1)^2/(y+1), and exact
squarefree diagonal/cross terms. No independent-sign approximations.
"""
from array import array
from math import isclose
import argparse
import json


def sieve(N):
    lp = array("I", [0]) * (N + 1)
    mu = array("b", [0]) * (N + 1)
    M = array("i", [0]) * (N + 1)
    Q = array("I", [0]) * (N + 1)
    mu[1] = 1
    primes = []
    for n in range(2, N + 1):
        if not lp[n]:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            x = p * n
            if x > N:
                break
            lp[x] = p
            if n % p == 0:
                mu[x] = 0
                break
            mu[x] = -mu[n]
    for n in range(1, N + 1):
        M[n] = M[n - 1] + mu[n]
        Q[n] = Q[n - 1] + (mu[n] != 0)
    return mu, M, Q, primes


def measure(R, M, Q, primes, K):
    X = R * R - 1
    daughters = [(p, X // (p * p)) for p in primes if p != 2 and p * p < R]
    U = sum(M[y] / p for p, y in daughters)
    E = sum(M[y] ** 2 for p, y in daughters)
    corr = M[R - 1] - M[X]
    B = corr - U
    # Exact diagonal: squarefree count of (tail + reciprocal daughters)^2.
    D = float(Q[X] - Q[R - 1])
    D += 2 * sum((Q[y] - Q[R - 1]) / p for p, y in daughters)
    D += sum(Q[min(y, z)] / (p * q)
             for p, y in daughters for q, z in daughters)
    return {
        "R": R, "X": X, "K": K, "low_owners": len(daughters),
        "corr": int(corr), "U": U, "B": B, "daughter_energy": E,
        "diagonal": D, "signed_offdiagonal_twice": B * B - D,
        "required_boundary_C": (B * B - 2.25 * E) / (R * R * K),
    }


def verify_physical_clock(row, mu, M, Q, primes):
    R = row["R"]
    X = row["X"]
    daughters = [(p, X // (p * p)) for p in primes if p != 2 and p * p < R]
    signed = 0.0
    diagonal = 0.0
    for n in range(1, X + 1):
        w = (1.0 if n >= R else 0.0)
        w += sum(1.0 / p for p, y in daughters if n <= y)
        signed -= mu[n] * w
        diagonal += mu[n] * mu[n] * w * w
    assert isclose(signed, row["B"], rel_tol=1e-11, abs_tol=1e-7)
    assert isclose(diagonal, row["diagonal"], rel_tol=1e-11, abs_tol=2e-6)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-root", type=int, default=317)
    parser.add_argument("--assert-identity", action="store_true")
    a = parser.parse_args()
    if a.max_root < 56:
        raise ValueError("max-root must be at least 56")
    mu, M, Q, primes = sieve(a.max_root * a.max_root - 1)
    # Include all historical y<R, including 0..54; K_R is NOT always 1.
    K = max((M[y] - 1) ** 2 / (y + 1) for y in range(55))
    records = []
    for R in range(56, a.max_root + 1):
        y = R - 1
        K = max(K, (M[y] - 1) ** 2 / (y + 1))
        row = measure(R, M, Q, primes, K)
        records.append(row)
        if a.assert_identity and R in (56, 64, 97, 244, 317):
            verify_physical_clock(row, mu, M, Q, primes)
    worst = max(records, key=lambda row: row["required_boundary_C"])
    print(json.dumps({
        "status": "FINITE_ONLY_NO_UNIFORM_BOUND",
        "max_root": a.max_root, "tested_roots": len(records),
        "max_required_boundary_C": worst,
        "daughter_only_C_zero_fails":
            sum(r["required_boundary_C"] > 0 for r in records),
        "selected": [r for r in records if r["R"] in
                     (56, 64, 97, 244, 317, 1027, a.max_root)],
    }, indent=2))


if __name__ == "__main__":
    main()
