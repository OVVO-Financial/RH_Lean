"""Independent exact finite tests for the original physical-tail phase result."""

from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm
from pathlib import Path
import re


def check(c):
    keys = tuple(c)
    p = lcm(*keys)
    r = [1 - sum(c[k] * Q(m % k, k) for k in keys) for m in range(p)]
    u = [x*x for x in r]
    bias = 1 - sum(c[k]*Q(k-1, 2*k) for k in keys)
    cov = sum(c[k]*c[l]*Q(gcd(k, l)**2-1, 12*k*l) for k in keys for l in keys)
    e = bias*bias + cov
    assert sum(u) == p*e
    f = [Q(0)]
    for x in u:
        f.append(f[-1] + x-e)
    assert f[-1] == 0
    a = min(range(p), key=f.__getitem__)
    b = max(range(p), key=f.__getitem__)
    assert (a == b) == (len(set(u)) == 1)
    for s in range(1, 2*p+2):
        def w(i):
            return Q(1, (s+i)*(s+i+1))
        j = p+2
        z = [f[(s+i) % p]-f[s % p] for i in range(j+1)]
        direct = sum(w(i)*(u[(s+i) % p]-e) for i in range(j))
        transformed = sum((w(i)-w(i+1))*z[i+1] for i in range(j))
        assert direct == transformed + w(j)*z[j]
        if a != b and s % p in (a, b):
            sign = 1 if s % p == a else -1
            assert min(sign*x for x in z) >= 0 and sign*transformed > 0
    return p, a, b, bias, cov


def main():
    assert check({2: 0, 3: 3}) == (6, 2, 1, 0, Q(2, 3))
    assert check({2: 2}) == (2, 0, 1, Q(1, 2), Q(1, 4))
    assert check({2: 0}) == (2, 0, 0, 1, 0)
    for x, y, z in product((-2, 0, 1, 3), repeat=3):
        check({2: x, 3: y, 4: z})
    print('67 exact profiles: full bias/covariance, cyclic extremes, finite Abel boundary')
    if Path('research/NYMAN_TAIL_ABEL.lean').exists():
        paths = [Path('research/NYMAN_TAIL_ABEL.lean'), Path('research/NYMAN_TAIL_PHASES.lean')]
        src = '\n'.join(p.read_text() for p in paths)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', src)
        assert set(re.findall(r'^theorem (\w+)', src, re.M)) == {
            'nyman_cutoff_primitive_periodic', 'nyman_tail_abel',
            'nyman_tail_two_phases', 'nyman_two_moment_tail_phases'}


if __name__ == '__main__':
    main()
