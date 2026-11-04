"""Exact finite regressions for the C29 Nyman arithmetic statements.

Linear forms in formal prime logarithms are compared coefficient by coefficient.
These tests neither execute Lean nor certify an infinite theorem.
"""

from fractions import Fraction as Q
from collections import Counter
import json


def factors(n):
    out = Counter()
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] += 1
            n //= p
        p += 1
    if n > 1:
        out[n] += 1
    return out


def mu(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def clean(a):
    return {p: Q(v) for p, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for p, v in b.items():
        out[p] = out.get(p, Q(0)) + v
    return clean(out)


def scale(c, a):
    return clean({p: Q(c) * v for p, v in a.items()})


def minus(a, b):
    return add(a, scale(-1, b))


def logform(n):
    assert n >= 1
    return clean(factors(n))


def psi(m):
    out = {}
    for n in range(2, m + 1):
        f = factors(n)
        if len(f) == 1:
            out = add(out, {next(iter(f)): Q(1)})
    return out


def scaled_residual(n, delta, m):
    length = logform(n)
    out = dict(length)
    for k in range(2, n + 1):
        lc = add(scale(-mu(k), minus(length, logform(k))),
                 scale(delta.get(k, 0), length))
        out = minus(out, scale(Q(m % k, k), lc))
    return out


def kernel_floor(n, m):
    out = {}
    for k in range(1, n + 1):
        out = add(out, scale(mu(k) * (m // k),
                             minus(logform(n), logform(k))))
    return out


def weight(m):
    assert m >= 1
    return Q(1, m * (m + 1))


def run():
    # Frozen before execution: odd/even, non-sixfold, and smallest cutoffs.
    cutoffs = (2, 3, 4, 6, 7, 10, 11, 17)
    floor_checks = 0
    invariant_checks = 0
    for n in cutoffs:
        for m in range(1, n + 1):
            assert kernel_floor(n, m) == add(logform(n), psi(m))
            floor_checks += 1
        for h in sorted({n // 2, n - 1, n}):
            delta = {k: Q((-1) ** k * (k + 1), k + 2)
                     for k in range(h + 1, n + 1) if k >= 2}
            for m in range(1, h // 2 + 1):
                left = minus(scaled_residual(n, delta, 2 * m),
                             scale(2, scaled_residual(n, delta, m)))
                right = minus(scale(2, psi(m)), psi(2 * m))
                assert left == right
                invariant_checks += 1

    # These are counterexamples to removing stated hypotheses, not to C29.
    n, m = 6, 2
    changed = minus(scaled_residual(n, {4: Q(1)}, 2 * m),
                    scale(2, scaled_residual(n, {4: Q(1)}, m)))
    target = minus(scale(2, psi(m)), psi(2 * m))
    assert minus(changed, target) == logform(6)
    zero = minus(scaled_residual(6, {}, 0),
                 scale(2, scaled_residual(6, {}, 0)))
    assert zero == scale(-1, logform(6))

    carry_checks = 0
    for m in range(0, 18):
        for k in range(1, 2 * m + 4):
            carry = (2 * m) // k - 2 * (m // k)
            assert carry in (0, 1)
            assert Q((2 * m) % k, k) - 2 * Q(m % k, k) == -carry
            if 2 * m < k:
                assert carry == 0
            carry_checks += 1

    # Check the exact sum-of-squares certificate, including overlap of m and 2m.
    energy_checks = 0
    for x in range(0, 13):
        for seed in range(3):
            r = {n: Q(((n * n + 3 * seed * n + seed) % 13) - 6, n + 1)
                 for n in range(1, 2 * x + 1)}
            energy = sum(weight(n) * r[n] ** 2 for n in r)
            dyadic = sum(weight(m) * (r[2 * m] - 2 * r[m]) ** 2
                         for m in range(1, x + 1))
            certificate = sum(weight(m) * (r[2 * m] + 2 * r[m]) ** 2
                              for m in range(1, x + 1))
            for n in r:
                coefficient = 16 * weight(n)
                if n <= x:
                    coefficient -= 8 * weight(n)
                if n % 2 == 0:
                    coefficient -= 2 * weight(n // 2)
                assert coefficient > 0
                certificate += coefficient * r[n] ** 2
            assert certificate == 16 * energy - dyadic
            assert dyadic <= 16 * energy
            energy_checks += 1
    print(json.dumps({
        "status": "PASS_EXACT_FINITE_REGRESSIONS_NOT_LEAN",
        "cutoffs": cutoffs,
        "mobius_log_floor_checks": floor_checks,
        "arbitrary_high_coefficient_invariant_checks": invariant_checks,
        "residue_carry_checks": carry_checks,
        "weighted_square_certificate_checks": energy_checks,
        "excluded_endpoint_defect_N6_m2_delta4_1": "log(6)",
        "zero_index_defect_N6": "-log(6)",
    }, indent=2))


if __name__ == "__main__":
    run()
