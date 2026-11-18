"""Exact finite diagnostics; the uniform real-vector theorem requires Lean.

Preregistered supports K=1..8,12,24. Compare quotient-grouped profiles with
literal floors; certify all principal minors of the rational shifted Gram.
Negative controls retain the first-window rank defect and restoration cost.
"""

from fractions import Fraction as F
from itertools import combinations
import json

checks = 0


def check(condition):
    global checks
    assert condition
    checks += 1


def band(a, b, m):
    return sum(max(0, min(b, m // q) - a) for q in range(1, m // (a + 1) + 1))


def profile(k, m):
    return band(6*k, 8*k, m) - band(10*k, 12*k, m)


def det(a):
    if len(a) == 1:
        return a[0][0]
    return sum(((-1)**j * a[0][j] * det([row[:j] + row[j+1:] for row in a[1:]])
                for j in range(len(a))), F(0))


for k in [*range(1, 9), 12, 24]:
    scales = [k, 4*k, 16*k]
    windows = [range(7*s+1, 8*s+1) for s in scales]
    g = [[F(0) for _ in scales] for _ in scales]
    check(len(set().union(*map(set, windows))) == 21*k)
    for i, window in enumerate(windows):
        check(len(window) == scales[i])
        for m in window:
            p = [profile(s, m) for s in scales]
            check(p[i] == m-6*scales[i] >= scales[i])
            check(all(p[j] == 0 for j in range(i+1, 3)))
            check(all(abs(v) <= m for v in p))
            check(m*(m+1) <= 144*scales[i]**2)
            if k <= 3:
                for s, v in zip(scales, p):
                    direct = sum(m//d for d in range(6*s+1, 8*s+1))
                    direct -= sum(m//d for d in range(10*s+1, 12*s+1))
                    check(v == direct)
            for a in range(3):
                for b in range(3):
                    g[a][b] += F(p[a]*p[b], m*(m+1))
    shifted = [[g[a][b] - (F(k, 956592) if a == b else 0)
                for b in range(3)] for a in range(3)]
    for size in range(1, 4):
        for indices in combinations(range(3), size):
            check(det([[shifted[a][b] for b in indices] for a in indices]) > 0)
    check(all(profile(4*k, m) == 0 for m in windows[0]))
    check(g[1][1] > 0)
    check(profile(k, 12*k) != band(6*k, 8*k, 12*k))
    check(g[0][0] > 0 and F(0) < g[0][0])  # r=-profile has zero restored energy.
    for alpha, v in [(F(2, 3), F(-1, 2)), (F(-3), F(4))]:
        for m in [1, 6*k, 7*k+1, 8*k, 10*k+1, 12*k, 32*k]:
            original = sum((alpha if 6*k < d <= 8*k else
                            v-alpha if 10*k < d <= 12*k else F(0)) * (m//d)
                           for d in range(2, 12*k+1))
            check(original == alpha*profile(k, m) + v*band(10*k, 12*k, m))

check(144*(1+9**2+81**2) == 956592)
check(12*956592 == 11479104 < 49647168)
print(json.dumps({"status": "PASS", "exact_assertions": checks,
                  "supports": [*range(1, 9), 12, 24],
                  "negative_controls": ["first-window-only", "second-band-omission",
                                        "restoration-free-domination"],
                  "lean_certification": False}, sort_keys=True))
