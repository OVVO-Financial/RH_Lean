#!/usr/bin/env python3
"""Finite regression for research/VF_MID_919_GENERAL_X_HIGH_QUOTIENT_ISOLATION.lean.

Exact integer checks, for every X <= LIMIT, of scheduled Census claim
20261017-census-2 with r = isqrt(X) and N = X // (r + 1):

    V_high(X) = sum_{r < t <= X} |B_X(t) - B_X(t+1)|
              = 2 * sum_{n <= N} |a6(n)| - |B_X(r+1)|  <=  2N  <=  2 sqrt(X),

where B_X(t) keeps every quotient bucket, including those on which the
period-36 kernel vanishes.  Also checks |a6(n)| <= d_chi(n) and
sum_{n <= N} d_chi(n) <= N for n, N <= LIMIT.

The Lean module carries the proof; this script is a regression only and
does not extrapolate.
"""
from math import isqrt

from vf919_principal_coefficient_check import coefficients

LIMIT = 4000


def main() -> None:
    _, grouped = coefficients(LIMIT)
    a6 = [0] * (LIMIT + 1)
    for n in range(1, LIMIT + 1):
        if n % 2 and n % 3:
            a6[n] = grouped[n]

    dchi = [0] * (LIMIT + 1)
    for d in range(1, LIMIT + 1):
        c = (0, 1, -1)[d % 3]
        if c:
            for n in range(d, LIMIT + 1, d):
                dchi[n] += c
    assert all(abs(a6[n]) <= dchi[n] for n in range(1, LIMIT + 1))
    running = 0
    for n in range(1, LIMIT + 1):
        running += dchi[n]
        assert 0 <= running <= n, (n, running)

    first_boundary = None
    boundary_cases = 0
    worst = (0.0, 0)
    for x in range(1, LIMIT + 1):
        r = isqrt(x)
        big_n = x // (r + 1)
        buckets = [0] * (x + 3)
        for m in range(1, x + 1):
            if a6[m]:
                buckets[x // m] += a6[m]
        v_high = sum(abs(buckets[t] - buckets[t + 1]) for t in range(r + 1, x + 1))
        mass = sum(abs(a6[n]) for n in range(1, big_n + 1))
        boundary = abs(buckets[r + 1])
        assert v_high == 2 * mass - boundary, (x, v_high, mass, boundary)
        assert mass <= big_n and big_n <= r and big_n * big_n <= x
        assert v_high <= 2 * big_n - boundary
        if boundary:
            boundary_cases += 1
            if first_boundary is None and x >= 256:
                first_boundary = (x, v_high, 2 * mass, boundary)
        if x > 1:
            worst = max(worst, (v_high / (x ** 0.5), x))

    assert first_boundary is not None and first_boundary[0] == 380, first_boundary
    print(f'census-2 identity exact for every X <= {LIMIT}; '
          f'nonzero boundary bucket at {boundary_cases} values of X')
    print(f'first nonzero boundary with X >= 256: X={first_boundary[0]} '
          f'V_high={first_boundary[1]} 2*mass={first_boundary[2]} '
          f'|B(r+1)|={first_boundary[3]}')
    print(f'max V_high/sqrt(X) = {worst[0]:.6f} at X={worst[1]} (bound 2)')
    print(f'|a6(n)| <= d_chi(n) and sum_(n<=N) d_chi(n) <= N for all n, N <= {LIMIT}')
    print('Finite regression only; no low-quotient or Mertens estimate is asserted.')


if __name__ == '__main__':
    main()
