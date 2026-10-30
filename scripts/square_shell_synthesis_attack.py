#!/usr/bin/env python3
"""Exact finite source audit, not an asymptotic proof or random-sign model.

Usage: python3 scripts/square_shell_synthesis_attack.py --heights 64 317 1027
The default requires no third-party packages. All reported numbers are integers.
"""
from __future__ import annotations
import argparse
import json
from math import isqrt
from pathlib import Path


def mobius_sieve(n: int) -> list[int]:
    if n < 1:
        raise ValueError('Positive sieve limit required')
    mu = [1] * (n + 1)
    mu[0] = 0
    composite = bytearray(n + 1)
    for p in range(2, n + 1):
        if not composite[p]:
            for k in range(p, n + 1, p):
                composite[k] = 1
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    return mu


def analyze(H: int) -> dict:
    if H < 3:
        raise ValueError('Use H >= 3')
    mu = mobius_sieve(4 * H * H)
    profiles = []
    squareful_checks = 0
    for R in range(H, 2 * H):
        x, y = R * R - 1, (R + 1) * (R + 1) - 1
        F = [0] * (R + 1)
        for h in range(1, R + 1):
            F[h] = sum(mu[h * k] for k in range(x // h + 1, y // h + 1))
            assert abs(F[h]) * h <= 2 * R + 2 * h
            if mu[h] == 0:
                assert F[h] == 0
                corner = (mu[R] ** 2 * (R * R % h == 0)
                          + 2 * mu[R] * mu[R + 1] * (R * (R + 1) % h == 0)
                          + 2 * mu[R] * mu[R + 2] * (R * (R + 2) % h == 0))
                assert corner == mu[R] ** 2 * (R * R % h == 0)
                squareful_checks += 1
        profiles.append(F)
    delta = [F[1] for F in profiles]
    energy = sum(v * v for v in delta)
    bands = []
    total = 0
    for j in range((2 * H - 1).bit_length()):
        D = 1 << j
        beta = [0] * (2 * H)
        for k in range(D, min(2 * D, 2 * H)):
            for t in range(1, (2 * H - 1) // k + 1):
                beta[t * k] += mu[t]
        signed = sum(beta[h] * F[h] ** 2 for F in profiles
                     for h in range(1, len(F)) if beta[h])
        absolute = sum(abs(beta[h]) * F[h] ** 2 for F in profiles
                       for h in range(1, len(F)) if beta[h])
        total += signed
        bands.append({'D': D, 'signed_gcd_energy': signed,
                      'absolute_mask_energy': absolute})
    assert total == energy
    temporal = []
    for j in range(H.bit_length()):
        L = 1 << j
        joint = diag = max_cross = groups = 0
        for start in range(0, H - L + 1, L):
            row = delta[start:start + L]
            s = sum(row)
            e = sum(v * v for v in row)
            joint += s * s
            diag += e
            max_cross = max(max_cross, s * s - e)
            groups += 1
        temporal.append({'block_roots': L, 'groups': groups,
                         'joint_energy': joint, 'diagonal_energy': diag,
                         'signed_offdiagonal': joint - diag,
                         'largest_positive_group_offdiagonal': max_cross})
    lag = [{'lag': l, 'signed_covariance': sum(a * b for a, b in zip(delta[:-l], delta[l:]))}
           for l in range(1, min(H, 17))]
    # Independent literal Euler double sum at selected roots and divisor masks.
    literal_checks = 0
    for R in sorted({H, 2 * H - 1}):
        x, y = R * R - 1, (R + 1) ** 2 - 1
        for h in [1, 4, 6, 9]:
            from math import gcd
            w = 0
            for a in range(1, R):
                if not mu[a]:
                    continue
                for b in range(1, R):
                    if not mu[b]:
                        continue
                    m = a * b
                    lcm = m * h // gcd(m, h)
                    w += mu[a] * mu[b] * (y // lcm - x // lcm)
            f = sum(mu[h * k] for k in range(x // h + 1, y // h + 1))
            corner = (mu[R] ** 2 * (R * R % h == 0)
                      + 2 * mu[R] * mu[R + 1] * (R * (R + 1) % h == 0)
                      + 2 * mu[R] * mu[R + 2] * (R * (R + 2) % h == 0))
            assert w == -f + corner, (R, h, w, f, corner)
            literal_checks += 1
    return {'H': H, 'delta_energy': energy, 'delta_sum': sum(delta),
            'squareful_mask_checks': squareful_checks,
            'literal_Euler_crosswalk_checks': literal_checks,
            'gcd_bands': bands, 'temporal_blocks': temporal,
            'lag_covariances': lag,
            'scope': 'FINITE EXACT DATA ONLY; no global power-saving claim'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--heights', nargs='+', type=int, default=[32, 64, 127])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = [analyze(H) for H in args.heights]
    # These genuine arithmetic examples refute global favorable-sign shortcuts.
    for row in results:
        if row['H'] == 127:
            assert row['gcd_bands'][0]['signed_gcd_energy'] == 4301
            assert row['lag_covariances'][0]['signed_covariance'] == 2154
    text = json.dumps(results, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
