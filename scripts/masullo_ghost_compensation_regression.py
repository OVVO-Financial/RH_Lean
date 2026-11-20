#!/usr/bin/env python3
"""Source-faithful Masullo/RH_Lean finite Euler ghost regression.

All arithmetic cancellation comparisons below use exact integer vectors of
log-prime coefficients, not floating point. Floating logarithms are used
only to print G_R. This does not verify the manuscript's spectral trace.
"""
from bisect import bisect_left, bisect_right
from collections import Counter
from math import log, sqrt


def primes_through(n):
    flags = bytearray(b"\x01") * (n + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, int(sqrt(n)) + 1):
        if flags[p]:
            flags[p*p:n+1:p] = b"\x00" * ((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def factor(n):
    result = {}
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            result[d] = e
        d += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def lambda_base(n):
    f = factor(n)
    return next(iter(f)) if len(f) == 1 else None


def prime_vector(n):
    return Counter(factor(n))


def squarefree_divisor_terms(m):
    """Only squarefree divisors have nonzero Mobius coefficient."""
    terms = [(1, 1)]
    for q in factor(m):
        terms += [(d*q, -sgn) for d, sgn in list(terms)]
    return terms


def clean(v):
    return {q: k for q, k in v.items() if k}


def check_pointwise(R):
    X = R*R - 1
    ps = primes_through(X)
    cases = 0
    for p in ps:
        if p <= R:
            continue
        for m in range(2, min(R, X//p + 1)):
            retained = Counter()
            omitted = Counter()
            for d, sign in squarefree_divisor_terms(m):
                retained.update({q: sign*e for q, e in factor(p*(m//d)).items()})
                omitted.update({q: -sign*e for q, e in factor(m//d).items()})
            base = lambda_base(m)
            expected = {} if base is None else {base: 1}
            assert clean(retained) == expected, (R, p, m, clean(retained), expected)
            assert clean(omitted) == {q: -e for q, e in expected.items()}
            joint = Counter(retained)
            joint.update(omitted)  # Preserve signed coefficients; Counter + clips negatives.
            assert not clean(joint), (R, p, m)
            cases += 1
    return cases


def check_ghost(R, primes):
    X = R*R - 1
    piR = bisect_right(primes, R)
    # Cofactor-first prime-count form. Each integer coefficient is a log(q) coefficient.
    by_cofactor = Counter()
    for m in range(2, R):
        q = lambda_base(m)
        if q is not None:
            by_cofactor[q] += bisect_right(primes, X//m) - piR

    # Prime-first form, grouped by y=floor(X/p) to avoid O(R*pi(X)) work.
    by_prime = Counter()
    psi_coeff = Counter()
    for y in range(2, R):
        q = lambda_base(y)
        if q is not None:
            psi_coeff[q] += 1
        low = max(R+1, X//(y+1) + 1)
        high = X//y
        frequency = max(0, bisect_right(primes, high) - bisect_left(primes, low))
        for q0, coef in psi_coeff.items():
            by_prime[q0] += frequency * coef
    assert clean(by_cofactor) == clean(by_prime), (R, by_cofactor, by_prime)
    G = sum(n * log(q) for q, n in by_cofactor.items())
    return G, sum(by_cofactor.values()), len(by_cofactor)


def check_strip_pair(alpha, gap):
    """The two-mode Gram calculation, not a global trace-class statement."""
    c = 4*alpha*alpha/(4*alpha*alpha + gap*gap)
    s = gap*sqrt(8*alpha*alpha+gap*gap)/(4*alpha*alpha+gap*gap)
    factor = c*gap/s
    assert abs(factor - 4*alpha*alpha/sqrt(8*alpha*alpha+gap*gap)) < 1e-11
    assert factor <= sqrt(2)*alpha + 1e-12
    return 1/s, factor


def main():
    for R in (7, 13, 31):
        c = check_pointwise(R)
        print(f'R={R}: {c} exact pointwise mu*log high-prime restoration checks')
    assert all(check_strip_pair(0.1, d)[1] <= sqrt(2)*0.1 for d in (1e-3, 1e-5))
    print('Two-mode spacing-independent compensation identity: PASS')

    Rmax = 3000
    primes = primes_through(Rmax*Rmax-1)
    for R in (31, 100, 317, 1027, 3000):
        G, n, bases = check_ghost(R, primes)
        print(f'R={R:4d} G_R={G:.6f} G_R/R^2={G/(R*R):.7f} '
              f'log-prime-coefficient-total={n} distinct-prime-bases={bases}')
    print('Prime-first/Cofactor-first ghost ledger: all exact coefficient checks PASS')
    print('No asymptotic theorem, zero-free region, or RH exponent is certified by finite tests.')


if __name__ == '__main__':
    main()