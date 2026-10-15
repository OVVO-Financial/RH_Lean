"""Independent, standard-library integer checks for the signed-lift diagnostics.

This verifier uses Python's arbitrary-precision integers, not NumPy or numba.
It checks the reported row budgets, smaller higher-order identities, and the
scalar-prefix-only negative control. It is not a Lean numerical certificate.
"""
from itertools import accumulate
from math import comb
from pathlib import Path
import json


def mobius_sieve(limit: int) -> list[int]:
    if limit < 1:
        raise ValueError('limit must be positive')
    primes: list[int] = []
    least = [0] * (limit + 1)
    mu = [0] * (limit + 1)
    mu[1] = 1
    for n in range(2, limit + 1):
        if least[n] == 0:
            least[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p * n > limit:
                break
            least[p * n] = p
            if n % p == 0:
                mu[p * n] = 0
                break
            mu[p * n] = -mu[n]
    return mu


def convolution(f: list[int], g: list[int], cutoff: int) -> list[int]:
    result = [0] * (cutoff + 1)
    for i in range(1, min(cutoff, len(f) - 1) + 1):
        if not f[i]:
            continue
        for j in range(1, min(cutoff // i, len(g) - 1) + 1):
            if g[j]:
                result[i * j] += f[i] * g[j]
    return result


def main() -> None:
    expected = json.loads(Path(__file__).with_name('diagnostics.json').read_text())
    mu = mobius_sieve(1_000_000)
    mertens = list(accumulate(mu))
    for item in expected['floor_kernel']:
        N, x = item['N'], item['x']
        if x > 1_000_000:
            continue
        signed = raw = rows = 0
        for i in range(1, N + 1):
            row = 0
            for j in range(1, N + 1):
                weight = x // (i * j)
                row += mu[j] * weight
                raw += abs(mu[i] * mu[j]) * weight
            signed += mu[i] * row
            rows += abs(mu[i] * row)
        assert (signed, raw, rows) == (item['Q'], item['raw_absolute_budget'],
                                      item['row_signed_then_absolute'])
        assert 2 * mertens[N] - signed == mertens[x] == item['M_x']
    for item in expected['higher_order']:
        N, k, x = item['N'], item['k'], item['x']
        if x > 27_000:
            continue
        a = mu[:N + 1]
        ones = [0] + [1] * x
        f = a[:]
        components = []
        for j in range(1, k + 1):
            components.append((-1) ** (j - 1) * comb(k, j) * sum(f))
            if j < k:
                f = convolution(convolution(a, f, x), ones, x)
        assert components == item['signed_components']
        assert sum(components) == mertens[x]
    # This sparse sequence has bounded prefix sums but is not a genuine long
    # Mobius prefix. It rejects only scalar-prefix-only generalizations.
    a = [0, 1, -1]
    X = 400
    aa1 = convolution(convolution(a, a, X), [0] + [1] * X, X)
    lift = [(2 * a[n] if n < len(a) else 0) - aa1[n] for n in range(X + 1)]
    sums = list(accumulate(lift))
    for t in range(1, 101):
        assert sums[4 * t] == -t
    print('PASS: independent integer budgets through N=1000; higher-order tests')
    print('through X=27000; sparse scalar-prefix negative control at 100 cutoffs.')


if __name__ == '__main__':
    main()
