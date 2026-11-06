#!/usr/bin/env python3
"""Exact original-residue regression; not Lean proof evidence."""

from fractions import Fraction as F


def residual(c, m):
    return 1 - sum((c[k] * F(m % k, k) for k in range(2, 13)), F(0))


def moments(c):
    return (
        sum(c[2:13], F(0)),
        sum((c[k] / k for k in range(2, 13)), F(0)),
        sum((c[k] * F(k - 1, 2 * k) for k in range(2, 13)), F(0)),
    )


def energy(c, T):
    return sum((residual(c, m) ** 2 / (m * (m + 1))
                for m in range(1, T + 1)), F(0))


def perturb(c, t):
    return [x + t * v for x, v in zip(c, direction)]


direction = [F(0)] * 16
direction[7:10] = [F(7), F(-16), F(9)]
assert moments(direction) == (0, 0, 0)
centered = [F(0)] * 16
centered[2] = F(4)
bases = [centered, [F((k % 5) - 2, k + 1) for k in range(16)]]
checks = 0
for base in bases:
    for t in map(F, [-9, -1, 0, 1, 17]):
        changed = perturb(base, t)
        assert moments(changed) == moments(base)
        assert changed[:7] == base[:7] and changed[13:] == base[13:]
        assert all(residual(changed, m) == residual(base, m) for m in range(7))
        assert residual(changed, 7) == residual(base, 7) + 7 * t
        checks += 1
    for B in map(F, [-100, -1, 0, 1, 100]):
        t = (56 * (abs(B) + 1) - residual(base, 7)) / 7
        changed = perturb(base, t)
        assert residual(changed, 7) == 56 * (abs(B) + 1)
        assert all(B < energy(changed, T) for T in [7, 12, 25])
        checks += 1
assert moments(centered)[2] == 1
assert energy(perturb(centered, F(1)), 7) > energy(centered, 7)
bad = direction.copy()
bad[8] += 1
assert moments(bad) != (0, 0, 0)
assert residual(bad, 1) != 1
print(f"PASS: {checks} exact original-residue moment/energy cases")
print("PASS: mean-centered fixture, unchanged early cells, and broken-direction control")
print("Finite regression only; no infinite estimate or local Lean execution")
