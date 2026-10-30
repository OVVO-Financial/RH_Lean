#!/usr/bin/env python3
"""Exact audit of the original post-root owner return, not an asymptotic proof.

No random coefficients: construct genuine Mobius signs, remove common post-root
prime families, and strip the least separating prime from each remaining pair.
X is the integer endpoint, not the square-root parameter R of other audits.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from math import isqrt
from pathlib import Path


def arithmetic(limit: int):
    if limit < 2:
        raise ValueError('The endpoint must be at least two')
    spf = list(range(limit + 1))
    spf[0], spf[1] = 0, 1
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    primes = [p for p in range(2, limit + 1) if spf[p] == p]
    bits = {p: 1 << j for j, p in enumerate(primes)}
    mu = [0] * (limit + 1)
    masks = [0] * (limit + 1)
    mertens = [0] * (limit + 1)
    squarefree = [0] * (limit + 1)
    mu[1] = 1
    for n in range(1, limit + 1):
        if n > 1:
            p = spf[n]
            a = n // p
            mu[n] = 0 if a % p == 0 else -mu[a]
            masks[n] = masks[a] | bits[p]
        mertens[n] = mertens[n - 1] + mu[n]
        squarefree[n] = squarefree[n - 1] + mu[n] ** 2
    return primes, bits, mu, masks, mertens, squarefree


def audit(endpoint: int, data) -> dict:
    primes, bits, mu, masks, mertens, squarefree = data
    primes = [p for p in primes if p <= endpoint]
    high = [p for p in primes if p > isqrt(endpoint)]
    high_mask = sum(bits[p] for p in high)
    by_bit = {bits[p]: p for p in primes}
    sites = [n for n in range(1, endpoint + 1) if mu[n]]
    remainder = terminal = recursive = pair_count = 0
    multiplicity = defaultdict(int)
    selected = defaultdict(list)
    for j, n in enumerate(sites):
        for m in sites[:j]:
            if masks[m] & masks[n] & high_mask:
                continue
            weight = mu[m] * mu[n]
            remainder += weight
            pair_count += 1
            different = masks[m] ^ masks[n]
            assert different
            p = by_bit[different & -different]
            a = m // p if m % p == 0 else m
            b = n // p if n % p == 0 else n
            parent = tuple(sorted((a, b)))
            assert weight == -mu[a] * mu[b]
            assert m * n == p * a * b
            if a == b:
                assert weight == -1
                terminal += weight
            else:
                assert parent[0] < parent[1] <= endpoint
                assert not (masks[a] & masks[b] & high_mask)
                recursive += weight
                multiplicity[(parent, p)] += 1
                assert multiplicity[(parent, p)] <= 2
                if parent in {(1, 7), (1, 11), (1, 101)}:
                    selected[parent].append((m, n, p, weight))
    family = sum(mertens[endpoint // p] ** 2 for p in high)
    diagonal = squarefree[endpoint] - sum(squarefree[endpoint // p] for p in high)
    advantage = -sum(k * mu[a] * mu[b]
                     for ((a, b), _p), k in multiplicity.items())
    assert recursive == advantage
    assert remainder == terminal + advantage
    assert 0 <= diagonal <= endpoint
    assert mertens[endpoint] ** 2 == family + diagonal + 2 * remainder
    fibres = []
    for parent, children in sorted(selected.items()):
        amplitude = Fraction(mu[parent[0]] * mu[parent[1]], parent[0] * parent[1])
        values = [Fraction(w, m * n) for m, n, _p, w in children]
        coherent = sum(values, Fraction())
        energy = sum((v * v for v in values), Fraction())
        harmonic = sum((Fraction(1, p) for _m, _n, p, _w in children), Fraction())
        reciprocal = sum((Fraction(1, p * p) for _m, _n, p, _w in children), Fraction())
        assert coherent == -amplitude * harmonic
        assert energy == amplitude ** 2 * reciprocal
        assert reciprocal <= Fraction(79, 81)
        fibres.append({'parent': parent, 'children': children,
                       'parent_amplitude': str(amplitude),
                       'signed_reciprocal_amplitude': str(coherent),
                       'diagonal_energy': str(energy),
                       'diagonal_energy_ratio': str(reciprocal),
                       'coherent_squared_ratio': str(harmonic ** 2),
                       'raw_signed_child_mass': sum(c[3] for c in children)})
    return {'X': endpoint, 'M': mertens[endpoint], 'physical_pairs': pair_count,
            'transported_family_energy': family, 'complement_diagonal': diagonal,
            'terminal_signed_sum': terminal, 'parent_advantage': advantage,
            'complete_signed_remainder': remainder, 'selected_fibres': fibres}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--endpoints', nargs='+', type=int,
                        default=[13, 35, 71, 127, 317, 1027])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not args.endpoints or min(args.endpoints) < 2:
        parser.error('All endpoints must be integers >=2')
    data = arithmetic(max(args.endpoints))
    rows = [audit(x, data) for x in args.endpoints]
    if 35 in args.endpoints:
        row = next(r for r in rows if r['X'] == 35)
        fibre = next(f for f in row['selected_fibres'] if f['parent'] == (1, 7))
        assert fibre['signed_reciprocal_amplitude'] == '31/105'
        assert fibre['diagonal_energy_ratio'] == '361/450'
        assert fibre['coherent_squared_ratio'] == '961/225'
        assert fibre['raw_signed_child_mass'] == 6
    if 13 in args.endpoints:
        assert next(r for r in rows if r['X'] == 13)['complete_signed_remainder'] == 1
    certificates = [Fraction(19, 64), Fraction(7, 48), Fraction(1, 17)]
    for p, lower in zip([2, 3, 5], certificates):
        assert lower ** 4 * p ** 7 < 1
    assert 2 * sum(certificates) == Fraction(1637, 1632) > 1
    result = {'scope': 'EXACT FINITE ARITHMETIC; NOT A GLOBAL POWER-SAVING PROOF',
              'critical_weight_rational_lower_bound': '1637/1632', 'rows': rows}
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(text + '\n', encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
