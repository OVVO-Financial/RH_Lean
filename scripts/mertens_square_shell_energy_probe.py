#!/usr/bin/env python3
"""Exact-integer census for the independent 7/8 square-shell energy candidate.

No zeta zeros, external 7/8 bounds, Li fits, random models, or precomputed
Mobius data. Usage:
  python3 scripts/mertens_square_shell_energy_probe.py --root 3162
"""
import argparse
import bisect
from array import array


def sieve(limit):
    mu = array('b', [0]) * (limit + 1)
    smallest = array('I', [0]) * (limit + 1)
    greatest = array('I', [0]) * (limit + 1)
    mu[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if not smallest[n]:
            smallest[n] = n
            greatest[n] = n
            mu[n] = -1
            primes.append(n)
        for p in primes:
            m = n * p
            if m > limit or p > smallest[n]:
                break
            smallest[m] = p
            greatest[m] = max(greatest[n], p)
            if n % p == 0:
                mu[m] = 0
                break
            mu[m] = -mu[n]
    return mu, greatest, primes


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=int, default=1000,
                        help='last square endpoint; shells 2 <= r < root')
    args = parser.parse_args()
    if args.root < 4:
        parser.error('--root must be at least 4')
    root = args.root
    limit = root * root
    mu, largest, primes = sieve(limit)
    smooth = [0] * root
    transport = [0] * root
    delta = [0] * root
    diagonal = [0] * root
    mertens = [-1] * (root + 1)
    for r in range(2, root):
        sr = tr = diag = 0
        for n in range(r*r + 1, (r+1)*(r+1)):
            m = mu[n]
            if m == 0:
                continue
            diag += 1
            if largest[n] <= r:
                sr += m
            else:
                tr -= m
        smooth[r], transport[r], diagonal[r] = sr, tr, diag
        delta[r] = sr - tr
        mertens[r+1] = mertens[r] + delta[r]
    assert mertens[root] == sum(mu[1:limit+1])
    print(f'ROOT={root} X={limit} M(X)={mertens[root]}')
    for r in [14, 137, 317, 1000, 1110, 2000, root-1]:
        if not 2 <= r < root:
            continue
        upper = (r+1)*(r+1)-1
        lower = r*r
        prefix = [0]*(r+2)
        for a in range(1, r+2):
            prefix[a] = prefix[a-1] + mu[a]
        hi = bisect.bisect_left(primes, upper+1)
        lo = bisect.bisect_right(primes, r)
        tr_by_cofactors = 0
        for q in primes[lo:hi]:
            a1 = upper // q
            a0 = lower // q
            assert a1 <= r+1
            tr_by_cofactors += prefix[a1]-prefix[a0]
        assert tr_by_cofactors == transport[r], (
            r, tr_by_cofactors, transport[r])
        print(f'SHELL r={r} smooth={smooth[r]} transport={transport[r]} '
              f'delta={delta[r]} squarefree={diagonal[r]} '
              f'abs-delta/r^3/4={abs(delta[r])/r**.75:.6f}')
    print('DYADIC: H 2H E diagonal off-diagonal E/H^2 E/H^2.5 max|delta|')
    for H in [16, 32, 64, 128, 256, 512, 1024, 1530]:
        if 2*H > root:
            continue
        ee = sum(delta[r]**2 for r in range(H, 2*H))
        diag = sum(diagonal[H:2*H])
        off = ee - diag
        maxdelta = max(abs(delta[r]) for r in range(H, 2*H))
        print(f'DYAD {H} {2*H} {ee} {diag} {off} '
              f'{ee/H**2:.6f} {ee/H**2.5:.8f} {maxdelta}')
    best = max(range(2, root), key=lambda r: abs(delta[r])/r**.75)
    print(f'WORST pointwise |delta_r|/r^.75 = '
          f'{abs(delta[best])/best**.75:.8f} at r={best} delta={delta[best]}')
    print('PASS exact shell conservation, greatest-prime transport, and integer energies')


if __name__ == '__main__':
    main()
