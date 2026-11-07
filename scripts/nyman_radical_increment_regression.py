#!/usr/bin/env python3
"""Exact rational prime-log identities, not local Lean or analytic estimates."""

from fractions import Fraction as F
from functools import cache


class LinearLog:
    """Key 0 denotes a rational constant; key p denotes log of prime p."""

    def __init__(self, terms=None):
        self.terms = {p: F(c) for p, c in (terms or {}).items() if c}

    def __add__(self, other):
        if not isinstance(other, LinearLog):
            other = LinearLog({0: other})
        terms = self.terms.copy()
        for p, c in other.terms.items():
            terms[p] = terms.get(p, F(0)) + c
        return LinearLog(terms)

    __radd__ = __add__

    def __neg__(self):
        return self * -1

    def __sub__(self, other):
        return self + -other

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, scalar):
        return LinearLog({p: c * scalar for p, c in self.terms.items()})

    __rmul__ = __mul__

    def __eq__(self, other):
        if not isinstance(other, LinearLog):
            other = LinearLog({0: other})
        return self.terms == other.terms


@cache
def factor(n):
    result = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            result.append((p, e))
        p += 1
    if n > 1:
        result.append((n, 1))
    return tuple(result)


@cache
def log(n):
    assert n >= 1
    return LinearLog(dict(factor(n)))


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


def radical(n):
    result = 1
    for p, _ in factor(n):
        result *= p
    return result


@cache
def kernel(H, k):
    return mu(k) * (log(H) - log(k))


def jump(H, m):
    return -sum((kernel(H, d) for d in range(H + 1, m + 1) if m % d == 0),
                LinearLog())


def defect(H):
    return 1 - sum((kernel(H, k) * F(1, k) for k in range(1, H + 1)), LinearLog())


@cache
def psi(m):
    return sum((log(factor(n)[0][0]) for n in range(2, m + 1)
                if len(factor(n)) == 1), LinearLog())


def arithmetic_residual(H, m):
    return m - psi(m) - log(H) - sum(
        (kernel(H, k) * F(m % k, k) for k in range(1, H + 1)), LinearLog())


def flat_kernel(N, H, k):
    return kernel(N, k) - (kernel(H, k) if k <= H else LinearLog())


def scaled_residual(N, H, h, m):
    return log(N) - log(H) - sum(
        ((h[k] - flat_kernel(N, H, k)) * F(m % k, k)
         for k in range(2, N + 1)), LinearLog())


def flat_defect(N, H, h):
    return sum((flat_kernel(N, H, k) * F(1, k) for k in range(1, N + 1)),
               LinearLog()) - sum((h[k] / k for k in range(2, N + 1)), F(0))


def correction_jump(N, h, m):
    return sum((h[k] for k in range(2, N + 1) if m % k == 0), F(0))


def main():
    arithmetic = same_radical = small_radical = complete_flat = 0
    for H in range(1, 17):
        seen = {}
        for m in range(2, 81):
            actual = arithmetic_residual(H, m) - arithmetic_residual(H, m - 1)
            assert actual == defect(H) + jump(H, radical(m))
            assert jump(H, m) == jump(H, radical(m))
            if radical(m) in seen:
                assert actual == seen[radical(m)]
                same_radical += 1
            seen[radical(m)] = actual
            if radical(m) <= H:
                assert actual == defect(H)
                small_radical += 1
            arithmetic += 1
    for N in [6, 12, 18, 24]:
        for H in [1, N // 3, N // 2, N - 1]:
            for h in [[F(0)] * (N + 1), [F((k % 3) - 1, k + 1) for k in range(N + 1)]]:
                delta = flat_defect(N, H, h)
                for m in range(2, 2 * N + 1):
                    actual = scaled_residual(N, H, h, m) - scaled_residual(N, H, h, m - 1)
                    expected = delta + jump(H, radical(m)) - jump(N, radical(m))
                    expected += correction_jump(N, h, m)
                    assert actual == expected
                    if m <= N and all(h[k] == 0 for k in range(2, m + 1)):
                        assert actual == delta + jump(H, radical(m))
                    complete_flat += 1

    # The m=1 exclusion and both restoration terms are necessary.
    assert arithmetic_residual(2, 1) - arithmetic_residual(2, 0) != defect(2)
    h = [F(0)] * 13
    h[7] = F(1)
    actual = scaled_residual(12, 2, h, 7) - scaled_residual(12, 2, h, 6)
    no_correction = flat_defect(12, 2, h) + jump(2, 7)
    assert actual - no_correction == 1
    h[7] = F(0)
    actual = scaled_residual(12, 2, h, 13) - scaled_residual(12, 2, h, 12)
    no_outer_tail = flat_defect(12, 2, h) + jump(2, 13)
    assert actual != no_outer_tail
    assert actual - no_outer_tail == log(13) - log(12)
    print(f"PASS: {arithmetic} source increments, {same_radical} repeated radicals, "
          f"{small_radical} small-radical cells, {complete_flat} complete flat returns")
    print("PASS: m=1, correction-admission, and after-N negative controls")
    print("Exact finite prime-log algebra only; no local Lean or endpoint estimate")


if __name__ == '__main__':
    main()
