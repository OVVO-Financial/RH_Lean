"""Independent finite checks. Only integer floors and exact rationals are used."""

from fractions import Fraction as F
from itertools import product
from math import isqrt


def mu(n):
    result = 1
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            n //= d
            if n % d == 0:
                return 0
            result = -result
    return -result if n > 1 else result


def rank(rows):
    pivots = {}
    for row in rows:
        row = list(map(F, row))
        for i in sorted(pivots):
            c = row[i]
            row = [u - c * v for u, v in zip(row, pivots[i])]
        i = next((j for j, v in enumerate(row) if v), None)
        if i is not None:
            pivots[i] = [v / row[i] for v in row]
    return len(pivots)


def forms(r, p, q):
    x, n = r*r - 1, r-1
    rows = ((p, p*mu(p)), (q, -q*mu(q)))
    raw = center = continuous = F(0)
    for (i, u), (j, v) in product(rows, repeat=2):
        f, c = x//(i*j), F(x, i*j)
        raw += u*v*f
        continuous += u*v*c
        if n % i and n % j:
            center += u*v*(F(r+1, n)*F(n % i, i)*F(n % j, j) - (c-f))
    return raw, center, continuous


def main():
    blocks = probes = phases = 0
    for r in range(2, 151):
        x = r*r - 1
        d = [i for i in range(1, r) if r % i == 0]
        w = [[mu(i)*mu(j)*(x//(i*j)) for j in d] for i in d]
        assert rank(w) == (2 if len(d) > 1 else 1)
        for u, i in enumerate(d):
            for v, j in enumerate(d):
                assert w[u][v] == mu(i)*mu(j)*((r//i)*(r//j)-1)
        blocks += 1
    primes = (2, 3, 5, 7, 11, 13, 17, 19)
    for r in range(6, 321):
        for p, q in product(primes, repeat=2):
            if not (p < q < r and (r-1) % p and (r-1) % q):
                continue
            x, n = r*r-1, r-1
            raw, center, continuous = forms(r, p, q)
            assert continuous == 0
            assert raw == 2*(x % (p*q)) - x % (p*p) - x % (q*q)
            assert center == raw + F(r+1, n)*(n % p - n % q)**2
            probes += 1
    for t in (*range(65), 10**30, 10**100):
        for b, value in ((17, -7), (152, 3), (227, 0)):
            r = 225*t + b
            assert all(r % i and (r-1) % i and i < r for i in (3,5))
            assert forms(r, 3, 5) == (value, value, 0)
            phases += 1
    assert forms(8, 3, 5)[0] != forms(8, 3, 5)[1]
    assert forms(17, 3, 5)[0] != 9*32 - 15*19 + 25*11
    assert sum(mu(i)*mu(j)*(15//(i*j)) for i,j in product(range(1,4), repeat=2)) == -1
    print(f'PASS: {blocks} divisor ranks; {probes} complete prime probes; {phases} progression witnesses')


if __name__ == '__main__':
    main()
