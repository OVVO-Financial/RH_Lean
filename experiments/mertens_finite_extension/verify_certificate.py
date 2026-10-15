#!/usr/bin/env python3
"""Independently check finite interval certificates with exact integer arithmetic.

Uses a full independent sieve ONLY for validation, not for the prefix predictor.
This script is an executable numerical check, not a Lean kernel certificate.
"""
from array import array
import argparse
import csv
import json
from pathlib import Path


def mobius(limit: int) -> array:
    values = array('b', [1]) * (limit + 1)
    values[0] = 0
    composite = bytearray(limit + 1)
    for p in range(2, limit + 1):
        if composite[p]:
            continue
        for n in range(p, limit + 1, p):
            values[n] = -values[n]
            if n != p:
                composite[n] = 1
        square = p * p
        if square <= limit:
            for n in range(square, limit + 1, square):
                values[n] = 0
    return values


def verify(directory: Path) -> dict:
    summary = json.loads((directory / 'certificates_summary.json').read_text())
    limit = summary['extended_through']
    prefix = summary['prefix']
    if prefix != 1000 or limit != (prefix + 1)**2 - 1:
        raise ValueError('Unexpected certificate scale')
    mu = mobius(limit)
    summatory = array('i', [0]) * (limit + 1)
    for n in range(1, limit + 1):
        summatory[n] = summatory[n-1] + mu[n]
    reports = []
    for cert in summary['certificates']:
        p, q = cert['p'], cert['q']
        for n in range(1, prefix + 1):
            if abs(summatory[n])**q > n**p:
                raise ValueError(f'Failed seed bound: n={n}, exponent={p}/{q}')
        last, count = prefix, 0
        with (directory / f'certificate_{p}_{q}.csv').open(newline='') as stream:
            for row in csv.DictReader(stream):
                left, right, m, b = (int(row[k]) for k in
                    ('left', 'right', 'M_left', 'integer_power_floor'))
                valid = (left == last + 1 and left <= right <= limit
                         and m == summatory[left]
                         and b**q <= left**p < (b+1)**q
                         and abs(m) + right - left <= b)
                if not valid:
                    raise ValueError(f'Invalid interval row: {row}')
                last, count = right, count + 1
        if last != limit or count != cert['anchors']:
            raise ValueError('Incomplete coverage or inconsistent anchor count')
        reports.append(dict(p=p, q=q, anchors=count, last=last, result='PASS'))
    for witness in summary['first_failure_witness']:
        n, m = witness['n'], witness['M_from_prefix']
        if str(abs(m)**20 - n**9) != witness['power_gap']:
            raise ValueError('Incorrect witness integer power gap')
    return {'independent_finite_checks': reports,
            'witness_power_arithmetic': 'PASS',
            'global_envelope_preservation': 'NOT_PROVED'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', nargs='?', type=Path, default=Path('.'))
    args = parser.parse_args()
    print(json.dumps(verify(args.directory), indent=2))
