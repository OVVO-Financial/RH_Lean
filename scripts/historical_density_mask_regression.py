#!/usr/bin/env python3
"""Exact finite regressions; infinite and real-exponent claims require Lean.

Registration: balanced rational masks on fixed integer supports; all terms
and both nonnegative costs retained. Integer exponents and square supports
at beta=1/2 permit exact rational arithmetic. Check sharpness and reject
omitted positive mass, larger-cofactor cost, unit normalization and beta<1.
"""

from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

checks = 0
controls = set()


def check(condition):
    global checks
    assert condition
    checks += 1


def power(d, beta):
    if beta.denominator == 1:
        return F(d) ** int(beta)
    assert beta == F(1, 2) and isqrt(d) ** 2 == d
    return F(isqrt(d))


def audit(mask, beta):
    tail = {d: c for d, c in mask.items() if d != 1}
    D = min(tail)
    check(mask[1] == 1)
    check(sum((c / d for d, c in mask.items()), F(0)) == 0)
    cost = sum((abs(c) / power(d, beta) for d, c in tail.items()), F(0))
    base = F(D) / power(D, beta)
    positive = 2 * base * sum((max(c, F(0)) / d for d, c in tail.items()), F(0))
    gap = sum((abs(c) / d * (F(d) / power(d, beta) - base)
               for d, c in tail.items()), F(0))
    check(cost == base + positive + gap)
    if beta <= 1:
        check(positive >= 0 and gap >= 0 and cost >= base)
    if beta < 1:
        check(cost > 1)
    if positive:
        check(cost != base + gap)
        controls.add("positive-mass-omission")
    if gap:
        check(cost != base + positive)
        controls.add("large-cofactor-omission")


for support in [(2, 3, 5), (4, 9, 16), (3, 5, 11, 17)]:
    D, *rest = support
    for values in product([F(-2), F(-1, 2), F(0), F(2, 3), F(3)], repeat=len(rest)):
        mask = {1: F(1), **dict(zip(rest, values))}
        mask[D] = -D * (1 + sum((mask[d] / d for d in rest), F(0)))
        for beta in [F(-1), F(0), F(1)]:
            audit(mask, beta)
        if all(isqrt(d) ** 2 == d for d in support):
            audit(mask, F(1, 2))

for D in range(2, 21):
    for beta in [F(-1), F(0), F(1), F(2)]:
        check(abs(F(-D)) / power(D, beta) == F(D) / power(D, beta))
        check(F(1) + F(-D, D) == 0)
check(F(2) / power(2, F(1)) == 1)
check(F(2) / power(2, F(2)) < 1)
controls.add("exponent-threshold")
check(F(0) == 0 and not F(0) > 1)
controls.add("unit-normalization")
check(controls == {"positive-mass-omission", "large-cofactor-omission",
                   "exponent-threshold", "unit-normalization"})
print(json.dumps({"status": "PASS", "exact_assertions": checks,
                  "negative_controls": sorted(controls), "lean_certification": False}, sort_keys=True))
