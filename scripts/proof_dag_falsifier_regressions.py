#!/usr/bin/env python3
"""Standard-library regressions for falsifiers recorded in the proof DAG.

CORR-4 (exact Fractions, literal PR #1021 carrier, X_R = R^2 - 1):
  R=56  the daughter-only remainder |B_R|^2 <= (9/4) E_R already fails;
  R=57  c_R > 0 together with C_R U_R > 0 (local sign necessity is false);
  R=244 reproduces the exact discovery maximum c_244.
JOH (claim 20261024-owner-1): blocks r=4 and r=7 have zero count defect and
first-moment displacement +4 and -2. Li_2 is evaluated by Ramanujan's series
in double precision; every value used is asserted to lie >= 0.05 from an
integer, far beyond the floating error, so each floor is determined.

Finite certificates only: they refute the stated universal shortcuts and
prove no uniform estimate. The R=549 BLOCK falsifier lives in
vf_block_capture_counterexample_549.py.
"""
from fractions import Fraction
import math

LIMIT = 244 ** 2


def mobius_prefix(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = [True] * (limit + 1)
    prime[0] = prime[1] = False
    for p in range(2, limit + 1):
        if prime[p]:
            for m in range(2 * p, limit + 1, p):
                prime[m] = False
            for m in range(p, limit + 1, p):
                mu[m] = -mu[m]
            for m in range(p * p, limit + 1, p * p):
                mu[m] = 0
    mertens = [0] * (limit + 1)
    for n in range(1, limit + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    return mertens, prime


def corr4(R, M, prime):
    X = R * R - 1
    owners = [q for q in range(3, R) if prime[q] and q * q < R]
    C = M[R - 1] - M[X]
    U = sum(Fraction(M[X // (q * q)], q) for q in owners)
    E = sum(M[X // (q * q)] ** 2 for q in owners)
    K = max(Fraction((M[y] - 1) ** 2, y + 1) for y in range(R))
    B = C - U
    return C, U, E, K, (B * B - Fraction(9, 4) * E) / (R * R * K)


def li(x):
    """Ramanujan's series for the principal-value logarithmic integral."""
    L = math.log(x)
    total, factorial = 0.0, 1.0
    for n in range(1, 90):
        factorial *= n
        inner = sum(1.0 / (2 * k + 1) for k in range((n - 1) // 2 + 1))
        total += (-1) ** (n - 1) * L ** n / (factorial * 2 ** (n - 1)) * inner
    return 0.5772156649015329 + math.log(L) + math.sqrt(x) * total


def joh_block(r, prime):
    li2 = li(2.0)
    lo, hi = r * r, (r + 1) ** 2
    values = {n: li(n) - li2 for n in range(lo - 1, hi + 1)}
    margin = min(abs(v - round(v)) for v in values.values())
    assert margin >= 0.05, f"Li_2 too close to an integer near r={r}: {margin}"
    Q = {n: math.floor(v) for n, v in values.items()}
    primes = [k for k in range(lo + 1, hi) if prime[k]]
    model = [k for k in range(lo + 1, hi) for _ in range(Q[k] - Q[k - 1])]
    eta = {k: int(prime[k]) - (Q[k] - Q[k - 1]) for k in range(lo + 1, hi)}
    J = sum((hi - k) * eta[k] for k in eta)
    D = (Q[hi] - Q[lo]) - sum(prime[k] for k in range(lo + 1, hi + 1))
    return primes, model, D, J


def main():
    M, prime = mobius_prefix(LIMIT)
    *_, c56 = corr4(56, M, prime)
    assert c56 > 0, "R=56 should violate the daughter-only bound"
    C, U, E, K, c57 = corr4(57, M, prime)
    assert (C, U, E, K) == (-19, Fraction(-71, 105), 3, Fraction(3, 2))
    assert c57 == Fraction(14509429, 214921350) and C * U > 0
    *_, c244 = corr4(244, M, prime)
    assert c244 == Fraction(1075442834449, 8948269730400)
    print(f"CORR4 R=56 c={float(c56):.6f}>0; R=57 c={c57} with C*U>0; R=244 c={float(c244):.17f}")
    assert abs(li(2.0) - 1.0451637801174927) < 1e-12
    expected = {4: ([17, 19, 23], [18, 21, 24], 0, 4), 7: ([53, 59, 61], [53, 57, 61], 0, -2)}
    for r, want in expected.items():
        got = joh_block(r, prime)
        assert got == want, (r, got)
        print(f"JOH r={r} primes={got[0]} floor-Li={got[1]} D_r={got[2]} J_r={got[3]:+d}")
    print("PASS: CORR-4 local shortcuts and JOH count-only bridge are refuted on exact fixtures")


if __name__ == "__main__":
    main()
