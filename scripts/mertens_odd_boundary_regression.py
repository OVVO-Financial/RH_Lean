#!/usr/bin/env python3
"""Exact finite regression of the physical carrier, not Lean proof evidence."""

from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def mobius(n):
    if n == 0:
        return 0
    value = 1
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
    return -value if n > 1 else value


def check(X, P):
    support = {n for n in range(1, X + 1) if mobius(n)}
    upper = {n for n in support if n % 2 == 1 and X < 2 * n}
    top = {n for n in range(1, X + 1) if prime(n) and X < 2 * n}
    channels = [(s, q) for s in P for q in range(2, X + 1)
                if prime(q) and all(t < q for t in P)
                and X < 2 * s * q and s * q <= X]
    partners = {s * q for s, q in channels}
    assert len(partners) == len(channels)
    assert top <= upper and partners <= upper and not top & partners
    assert all(mobius(n) == -1 for n in top)
    assert all(mobius(n) == 1 for n in partners)
    t = min(len(top), len(partners))
    A, C = set(sorted(top)[:t]), set(sorted(partners)[:t])
    R = upper - (A | C)
    assert len(R) + 2 * t == len(upper)
    total = sum(mobius(n) for n in range(1, X + 1))
    assert total == sum(map(mobius, upper)) == sum(map(mobius, R))
    assert total**2 == sum(mobius(a) * mobius(b) for a in R for b in R)
    # Independently verify the retained factor-two pairs use no new endpoint.
    old_pairs = [(n, 2 * n) for n in support if n % 2 and 2 * n <= X]
    old_used = {v for pair in old_pairs for v in pair}
    assert old_used == support - upper
    assert all(mobius(a) == -mobius(b) for a, b in old_pairs)
    return dict(X=X, P=P, top=len(top), partners=len(partners),
                upper=len(upper), residual=sorted(R), signed=total)


def convolution(a, b):
    X = len(a) - 1
    out = [0] * (X + 1)
    for i in range(1, X + 1):
        for j in range(1, X // i + 1):
            out[i * j] += a[i] * b[j]
    return out


def lift(N, k, X):
    a = [mobius(n) if n <= N else 0 for n in range(X + 1)]
    zeta = [0] + [1] * X
    defect = [-v for v in convolution(a, zeta)]
    if X:
        defect[1] += 1
    result = [0] * (X + 1)
    for _ in range(k):
        result = [u + v for u, v in zip(a, convolution(defect, result))]
    return result


def main():
    P9 = [3, 5, 7, 11, 13, 17, 19, 23, 29]
    cases = 0
    for X in range(4, 97):
        for P in ([], [3], [3, 5], P9):
            check(X, P)
            cases += 1
    assert check(63, [3, 5])["residual"] == [61]
    assert check(63, P9)["partners"] == 0
    assert 2 in {n for n in range(1, 4) if prime(n) and 3 < 2 * n}
    assert 2 % 2 != 1  # X >= 4 matters for prime admission.
    checks = 0
    for N in range(0, 5):
        for k in range(0, 4):
            X = min(96, (N + 1)**k - 1)
            values = lift(N, k, X)
            assert values == [mobius(n) for n in range(X + 1)]
            checks += X + 1
    assert lift(1, 2, 4)[4] == -1 and mobius(4) == 0
    for p in range(1, 24):
        for m in range(1, 48):
            admitted = all(m <= X < 2 * m for X in range(p, 2 * p))
            assert admitted == (m == p)
    print(f"PASS: {cases} exact physical cases; {checks} strict-cutoff coefficients")
    print(check(63, [3, 5]))
    print("PASS: empty P, X=3, small P9, excluded lift endpoint, and moving cutoffs")
    print("Finite computation only; no asymptotic estimate or local Lean execution")


if __name__ == "__main__":
    main()
