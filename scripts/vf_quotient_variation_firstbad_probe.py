#!/usr/bin/env python3
"""#919 sibling: exact square-hyperbola cutoff decomposition and variation census.

At X=R^2-1, m<R iff floor(X/m)>=R. Thus the high-quotient signed
contribution is a short genuine norm sum, while the low-quotient sector
contains all m>=R. This test uses #919's independently checked Euler
coefficient constructor. It does not extrapolate finite evidence to all R.

The numerical equality V_high=2*sum_{m<R}|a6(m)| is tested for hundreds
of roots; it is NOT assumed by the Lean module.
"""
from array import array
from math import log
import sys

from vf919_principal_coefficient_check import coefficients, quotient_kernel

EXPECTED = {
    # R: (M, long_norm_low_quotient, short_norm_high_quotient,
    #     low_quotient_variation, high_quotient_variation, short_norm_abs_mass)
    317: (-28, -31, 3, 1323, 184, 92),
    548: (234, 214, 20, 2988, 308, 154),
    1027: (367, 380, -13, 7050, 572, 286),
    3000: (-340, -373, 33, 22975, 1696, 848),
}


def exact_square_split(root: int, grouped: array) -> tuple[int, int, int, int, int]:
    x = root * root - 1
    low = [0] * (root + 1)
    high: dict[int, int] = {}
    short_abs = 0

    for m in range(1, root):
        a = grouped[m] if m % 2 and m % 3 else 0
        if a:
            t = x // m
            assert t >= root
            high[t] = high.get(t, 0) + a
            short_abs += abs(a)

    for m in range(root, x + 1):
        a = grouped[m] if m % 2 and m % 3 else 0
        if a:
            t = x // m
            assert 1 <= t < root
            low[t] += a

    low_signed = sum(quotient_kernel(t) * low[t] for t in range(1, root))
    high_signed = sum(quotient_kernel(t) * a for t, a in high.items())
    low_var = sum(abs(low[t] - low[t + 1]) for t in range(1, root))
    support = set(high) | {t - 1 for t in high if t > root}
    high_var = sum(abs(high.get(t, 0) - high.get(t + 1, 0))
                   for t in support)
    assert high_var <= 2 * short_abs
    assert abs(high_signed) <= 2 * short_abs
    return low_signed, high_signed, low_var, high_var, short_abs


def run(extended: bool = False) -> None:
    roots = (317, 548, 1027, 3000) if extended else (317, 548, 1027)
    scan = range(4, 251)
    maximum = max(*roots, max(scan))
    mu, grouped = coefficients(maximum * maximum - 1)
    # Pointwise Euler-factor domination by d_chi(n)=(1*chi_-3)(n).
    # The formal Lean proof of this all-n inequality remains an explicit
    # task; the regression verifies it for every n <= the largest root.
    dchi = [0] * (maximum + 1)
    for d in range(1, maximum + 1):
        c = (0, 1, -1)[d % 3]
        if c:
            for n in range(d, maximum + 1, d):
                dchi[n] += c
    assert all(z >= 0 for z in dchi[1:])
    assert all(abs(grouped[n] if n % 2 and n % 3 else 0) <= dchi[n]
               for n in range(1, maximum + 1))
    for n in (4, 31, 317, maximum):
        assert sum(dchi[1:n + 1]) == sum((n // a) % 3 == 1
                                          for a in range(1, n + 1))
        assert sum(dchi[1:n + 1]) <= n

    prefix = array('i', [0]) * len(mu)
    for n in range(1, len(mu)):
        prefix[n] = prefix[n - 1] + mu[n]

    print('R,M,low_signed,high_signed,V_low,V_high,short_abs,'
          'V_low_over_RlogR')
    for r in roots:
        x = r * r - 1
        low, high, vl, vh, mass = exact_square_split(r, grouped)
        got = (prefix[x], low, high, vl, vh, mass)
        assert got == EXPECTED[r], (r, got, EXPECTED[r])
        assert low + high == prefix[x]
        assert vh == 2 * mass
        print(f'{r},{prefix[x]},{low},{high},{vl},{vh},{mass},'
              f'{vl/(r*log(r)):.9f}')

    largest = (-1.0, 0)
    high_signs: set[int] = set()
    for r in scan:
        x = r * r - 1
        low, high, vl, vh, mass = exact_square_split(r, grouped)
        assert low + high == prefix[x]
        assert vh == 2 * mass, (r, vh, mass)
        high_signs.add((high > 0) - (high < 0))
        ratio = vl / (r * log(r))
        if ratio > largest[0]:
            largest = (ratio, r)
    assert high_signs == {-1, 0, 1}, high_signs
    print(f'scanned R=4..250; max observed V_low/(R log R)='
          f'{largest[0]:.9f} at R={largest[1]}')
    print('High signed sector has positive, zero and negative examples.')
    print('Pointwise |a6(n)| <= (1*chi_-3)(n) verified for n <= largest root.')
    print('No all-R variation estimate or first-bad contraction is asserted.')


if __name__ == '__main__':
    run('--extended' in sys.argv)
