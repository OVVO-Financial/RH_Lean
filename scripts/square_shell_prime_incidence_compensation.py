#!/usr/bin/env python3
"""Exact physical square-shell prime incidence and divisor compensation audit.

No assumed RH/OAI zero-free result, fitted probability law, or synthetic Mobius
weights. For each test shell, compare real pair enumeration with (a) the
prime-window/cofactor formula and (b) exact finite divisor-Mobius inversion.
Finite checks do NOT establish the dyadic 5/2 signed second-moment estimate.
"""
import argparse
import math
from functools import lru_cache


def sieve(limit):
    mu = [0] * (limit + 1)
    spf = [0] * (limit + 1)
    greatest = [0] * (limit + 1)
    pi = [0] * (limit + 1)
    primes = []
    mu[1] = 1
    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = greatest[n] = n
            mu[n] = -1
            primes.append(n)
        for p in primes:
            m = n * p
            if m > limit or p > spf[n]:
                break
            spf[m] = p
            greatest[m] = max(greatest[n], p)
            if n % p == 0:
                mu[m] = 0
                break
            mu[m] = -mu[n]
    count = 0
    for n in range(2, limit + 1):
        if spf[n] == n:
            count += 1
        pi[n] = count
    return mu, greatest, pi, primes


def direct_pairs(x, y, mu, is_same, D):
    total = 0
    for i, a in enumerate(x):
        for b in (y[i+1:] if is_same else y):
            if D <= math.gcd(a, b) < 2 * D:
                total += mu[a] * mu[b]
    return total


def run_one(r, D, mu, largest, pi, primes, verbose=False):
    assert r >= 3 and 2 * D < r
    lo, hi = r * r, r * r + 2 * r
    sites = range(lo + 1, hi + 1)
    smooth = [n for n in sites if largest[n] <= r and mu[n] != 0]
    transport = [n for n in sites if largest[n] > r and mu[n] != 0]
    f = lambda g: int(D <= g < 2 * D)

    SS = direct_pairs(smooth, smooth, mu, True, D)
    ST = direct_pairs(smooth, transport, mu, False, D)
    TT = direct_pairs(transport, transport, mu, True, D)
    P = [0] + [pi[hi // c] - pi[lo // c] for c in range(1, r + 1)]
    z = [0] + [mu[c] * P[c] for c in range(1, r + 1)]
    b = [0] + [sum(mu[s] * f(math.gcd(c, s)) for s in smooth)
                 for c in range(1, r + 1)]
    ST_incidence = -sum(z[c] * b[c] for c in range(1, r + 1))
    assert ST == ST_incidence

    @lru_cache(None)
    def J(c, cp):
        upper = hi // max(c, cp)
        lower = max(lo // c, lo // cp)
        if upper <= lower:
            return 0
        return pi[upper] - pi[lower]

    TT_incidence_twice = 0
    owner_collision_signed = 0
    J_all = 0
    for c in range(1, r + 1):
        for cp in range(1, r + 1):
            j = J(c, cp)
            J_all += j
            if j and c != cp:
                assert abs(c - cp) == 1, (r, c, cp, j)
                assert min(c, cp) * 2 > r
                assert math.gcd(c, cp) == 1
            if not f(math.gcd(c, cp)):
                continue
            w = mu[c] * mu[cp]
            TT_incidence_twice += w * (P[c] * P[cp] - j)
            owner_collision_signed += w * j
    assert TT_incidence_twice == 2 * TT, (r, D, TT_incidence_twice, TT)

    kq = [hi // q - lo // q for q in primes if q > r and q <= hi]
    assert all(0 <= k <= 2 for k in kq)
    assert sum(kq) == sum(P)
    assert J_all == sum(k * k for k in kq), (r, J_all)
    assert J_all <= 4 * r
    assert abs(owner_collision_signed) <= 4 * r
    collision = -owner_collision_signed / 2

    B = [0] * (r + 1)
    F = [0] * (r + 1)
    for d in range(1, r + 1):
        B[d] = sum(mu[s] for s in smooth if s % d == 0)
        F[d] = sum(mu[n] for n in range((lo // d + 1) * d, hi + 1, d))
    a = [0] + [sum(mu[k] * B[k * c] for k in range(1, r // c + 1))
               for c in range(1, r + 1)]
    e = [z[c] - a[c] for c in range(r + 1)]
    for d in range(1, r + 1):
        assert sum(a[c] for c in range(d, r + 1, d)) == B[d]
        assert sum(z[c] for c in range(d, r + 1, d)) == B[d] - F[d]
        assert sum(e[c] for c in range(d, r + 1, d)) == -F[d]
    for c in range(1, r + 1):
        assert sum(f(math.gcd(c, cp)) * a[cp]
                   for cp in range(1, r + 1)) == b[c]

    beta = [0] * (r + 1)
    for d in range(1, r + 1):
        beta[d] = sum(mu[d // k] for k in range(1, d + 1)
                      if d % k == 0 and D <= k < 2 * D)
        if mu[d] == 0:
            assert F[d] == 0
    coherent_boundary_twice = 2 * SS - sum(beta[d] * B[d] ** 2 for d in range(1, r + 1))
    centered_twice = sum(beta[d] * F[d] ** 2 for d in range(1, r + 1))
    physical_twice = 2 * (SS + ST + TT)
    assert physical_twice == centered_twice + coherent_boundary_twice - owner_collision_signed

    @lru_cache(None)
    def truncated_beta(g):
        return sum(beta[d] for d in range(1, r + 1) if g % d == 0)

    direct_boundary_twice = -sum(
        mu[s] * mu[t] * truncated_beta(math.gcd(s, t))
        for s in smooth for t in smooth if math.gcd(s, t) >= r
    )
    assert coherent_boundary_twice == direct_boundary_twice

    # Direct all-physical correction, including squareful zeros and diagonals.
    physical_boundary_twice = -sum(
        mu[m] * mu[n] * truncated_beta(math.gcd(m, n))
        for m in sites for n in sites if math.gcd(m, n) >= r
    )
    assert physical_twice == centered_twice + physical_boundary_twice
    assert physical_boundary_twice == coherent_boundary_twice - owner_collision_signed

    large = sum(beta[d] * F[d] ** 2 for d in range(1, r + 1) if d * d >= r)
    large_absolute_budget = sum(
        abs(beta[d]) * (2 * r // d + 1) ** 2
        for d in range(1, r + 1) if d * d >= r
    )
    assert abs(large) <= large_absolute_budget
    # Genuine multiplicative unshared-factor identity (not an assumed random sign).
    for d in (1, 2, 3, 5, 6, 10, 13, min(31, r)):
        if d > r or mu[d] == 0:
            continue
        cofactor_sum = sum(mu[k] for k in range(lo // d + 1, hi // d + 1)
                           if math.gcd(k, d) == 1)
        assert F[d] == mu[d] * cofactor_sum

    if verbose or r == 137 and D == 1:
        print(f'r={r:3d} D={D:2d}: SS={SS:5d} ST={ST:5d} TT={TT:5d} '
              f'C={SS+ST+TT:6d} | centered={centered_twice/2:7.1f} '
              f'SS-boundary={coherent_boundary_twice/2:6.1f} '
              f'owner-collision={collision:6.1f} '
              f'large-divisor-mode={large/2:7.1f}')
    return SS, ST, TT, centered_twice, physical_boundary_twice


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--max-root', type=int, default=317)
    p.add_argument('--verbose', action='store_true')
    p.add_argument('--exhaustive-root', type=int, default=80,
                   help='test every admissible gcd band for each r=3..this cutoff')
    args = p.parse_args()
    roots = sorted(set([r for r in (14, 31, 137, 317) if r <= args.max_root] +
                       list(range(3, min(args.exhaustive_root, args.max_root) + 1))))
    if not roots:
        p.error('--max-root must be >= 3')
    mu, greatest, pi, primes = sieve((max(roots) + 1) ** 2)
    count = 0
    for r in roots:
        bands = range(1, (r - 1) // 2 + 1) if r <= args.exhaustive_root else (1, 2, 4, 8)
        for D in bands:
            if 2 * D >= r:
                continue
            run_one(r, D, mu, greatest, pi, primes, args.verbose)
            count += 1
    print(f'PASS: {count} exact genuine-Mobius shell/gcd windows; '
          'owner geometry, incidence, divisor compensator, boundary and spectral tail')
    print('OPEN: no H^(5/2+eta) arithmetic upper bound for the low-divisor signed moment')


if __name__ == '__main__':
    main()
