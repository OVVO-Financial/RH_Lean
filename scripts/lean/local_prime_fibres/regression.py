"""Exact cyclotomic replay directly from primitive prime-power characters."""

from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, lcm


def prime(p):
    return p >= 2 and all(p % t for t in range(2, isqrt(p) + 1))


def bit(p, x):
    r = pow(x, (p - 1) // 2, p)
    assert r in (1, p - 1)
    return int(r != 1)


def replay(n, q, d):
    assert prime(q) and prime(d) and q % 8 == 3 and d % 16 == 7 and bit(q, -d) == 0
    m, order = 4 * n, lcm(2, n)
    log5 = {r % m: j for j in range(n) for r in (pow(5, j, m), -pow(5, j, m))}
    assert len(log5) == 2 * n
    chars = list(product(range(2), range(2), range(n)))[1:]
    counts = [0, 0]
    for p in (2, q, d, 13, 17):
        # Integer exponents in Q[z]/(z^(order/2)+1). A None value is a genuine ramified zero.
        coeff = {}
        for a, b, j in chars:
            conductor = (d if a else 1) * (q if b else 1) * (m // gcd(n, j) if j else 1)
            if conductor % p == 0:
                continue
            val = ((a * bit(d, p) if a else 0) + (b * bit(q, p) if b else 0)) * (order // 2)
            if j:
                val += j * log5[p % m] * (order // n)
            coeff[a, b, j] = val % order
        if (m * q * d) % p:
            assert len(coeff) == len(chars)
            counts[1] += len(coeff)
            continue
        for i, k, h in product(range(1, 9), range(2), range(n)):
            freq = [0] * (order // 2)
            for (a, b, j), val in coeff.items():
                t = (i * val - (a + b * k) * (order // 2) - j * h * (order // n)) % order
                freq[t % (order // 2)] += 1 if t < order // 2 else -1
            hit = p == d and k == i % 2 and h == i * log5[d % m] % n
            assert freq == [2 * n * int(hit) - 1] + [0] * (order // 2 - 1)
            counts[0] += 1
    for i in range(1, 9):
        z = (i % 2, i * log5[d % m] % n)
        weights = [int((k, h) == z) for k, h in product(range(2), range(n))]
        assert 1 - F(sum(weights), len(weights)) == 1 - F(1, 2 * n)
    return tuple(counts)


if __name__ == '__main__':
    hosts = list(product((1, 2, 4, 8, 32), ((3, 23), (11, 7), (211, 439), (227, 599))))
    runs = [replay(n, q, d) for n, (q, d) in hosts]
    print(f'{len(hosts)} hosts; {sum(c[0] for c in runs)} exact bad-prime coefficients; '
          f'{sum(c[1] for c in runs)} good-prime controls; {8 * len(hosts)} sharp spikes')
