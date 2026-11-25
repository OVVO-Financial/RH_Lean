#!/usr/bin/env python3
"""Exact prime-exponent decoding on the square prefix and its principal source.

The coordinate checks cover arithmetic site lattices. The signed experiment uses
the actual Λ(n)(N/n−1) prior to Euler centering, retaining every prime power.
Each log(p) has its own rational coefficient. Geometric section Smith factors
require an independently constructed restriction and are outside this experiment.
"""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
from math import comb, isqrt, log, prod


def smallest_factors(n):
    spf = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if spf[p] == p:
            for j in range(p * p, n + 1, p):
                if spf[j] == j:
                    spf[j] = p
    return spf


def factors(n, spf):
    out = {}
    while n > 1:
        p = spf[n]
        exponent = 0
        while n % p == 0:
            exponent += 1
            n //= p
        out[p] = exponent
    return out


def divisors(fac):
    items = tuple(fac.items())
    for exps in product(*(range(a + 1) for _, a in items)):
        yield prod(p ** k for (p, _), k in zip(items, exps))


def coefficient(d, h, spf, signed):
    if h % d:
        return 0
    left, right = factors(d, spf), factors(h, spf)
    weight = prod(comb(a, left.get(p, 0)) for p, a in right.items())
    parity = (sum(right.values()) - sum(left.values())) % 2
    return -weight if signed and parity else weight


def source(n, limit, spf):
    f = factors(n, spf)
    if len(f) == 1 and n != limit:
        return {next(iter(f)): Fraction(limit, n) - 1}
    return {}


def signed_column(low, high, limit, spf):
    ans = {}
    for d in divisors(factors(high, spf)):
        k = coefficient(d, high, spf, True)
        for p, q in source(low * d, limit, spf).items():
            ans[p] = ans.get(p, 0) + k * q
    return {p: q for p, q in ans.items() if q}


def cycle_free_formula(low, high, limit, spf):
    f = factors(high, spf)
    sign = (-1) ** sum(f.values())
    if low > 1:
        return {p: sign * q for p, q in source(low, limit, spf).items()}
    ans = {p: -sign * (limit * (1 - Fraction(p - 1, p) ** a) - 1)
           for p, a in f.items()}
    return {p: q for p, q in ans.items() if q}


def run(r, verify_all):
    limit = r * r - 1
    cutoff = max(2, int(log(limit)))
    spf = smallest_factors(limit)
    low = [1] * (limit + 1)
    maximum = 1
    for n in range(2, limit + 1):
        p = spf[n]
        low[n] = low[n // p] * (p if p <= cutoff else 1)
    rough = [h for h in range(1, limit + 1) if low[h] == 1]
    for h in rough:
        maximum = max(maximum, 2 ** sum(factors(h, spf).values()))
    p0 = next(p for p in range(cutoff + 1, limit + 1) if spf[p] == p)
    power, extremal_mass = 1, 1
    while power * p0 <= limit:
        power *= p0
        extremal_mass *= 2
    assert maximum == extremal_mass

    # Exhaust every interval on smaller prefixes. On large prefixes use a
    # deterministic selection covering the extremal repeated prime power.
    checks = rough if verify_all else sorted(set(rough[::max(1, len(rough) // 250)] + [power]))
    pairs = 0
    for h in checks:
        divs = list(divisors(factors(h, spf)))
        assert sum(abs(coefficient(d, h, spf, True)) for d in divs) == 2 ** sum(factors(h, spf).values())
        for d in divs:
            pairs += 1
            assert d == h or cutoff * d < h
            if d < h:
                assert cutoff * isqrt(d) ** 2 < (isqrt(h) + 1) ** 2
            for sign in [True, False]:
                lhs = sum(coefficient(d, k, spf, sign) * coefficient(k, h, spf, not sign)
                          for k in divs if k % d == 0)
                assert lhs == int(d == h)

    sites = range(1, limit + 1) if verify_all else sorted(
        set(range(1, limit + 1, max(1, limit // 800))) | {2 * p0, 2 * p0 ** 2, power, limit})
    total = 0
    for n in sites:
        if n > limit:
            continue
        ell, h = low[n], n // low[n]
        assert signed_column(ell, h, limit, spf) == cycle_free_formula(ell, h, limit, spf)
        # Reassemble the original value pointwise, including its zero at N.
        decoded = {}
        for d in divisors(factors(h, spf)):
            j = coefficient(d, h, spf, False)
            for p, q in signed_column(ell, d, limit, spf).items():
                decoded[p] = decoded.get(p, 0) + j * q
        assert {p: q for p, q in decoded.items() if q} == source(n, limit, spf)
        total += 1
    print(f"R={r} N={limit} z={cutoff} first_high={p0} max_column_mass={maximum} "
          f"intervals={pairs} exact_principal_sites={total}")
    if 2 * p0 ** 2 <= limit:
        loss = Fraction(limit, 2) - 1
        assert signed_column(2, p0, limit, spf) == {2: -loss}
        assert signed_column(2, p0 ** 2, limit, spf) == {2: loss}
        print(f"  sites {2*p0}, {2*p0**2}: coefficients of log(2) are {-loss}, +{loss}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("r", type=int, nargs="*", default=[16, 32, 64, 317, 1027])
    parser.add_argument("--full", action="store_true", help="verify both inverses and the signed source at every site")
    args = parser.parse_args()
    for anchor in args.r:
        if anchor < 3:
            parser.error("the experiment needs R≥3 so its prime cutoff is a proper prefix")
        run(anchor, args.full or anchor <= 64)
