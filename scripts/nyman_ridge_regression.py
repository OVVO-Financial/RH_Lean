"""Independent exact checks in rational prime-log coordinates; no numerical logs."""
from fractions import Fraction as F
from pathlib import Path
import re


def factor(n):
    out = {}
    for p in range(2, n + 1):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        if n == 1:
            break
    return out


def bands(K):
    return range(3*K+1, 4*K+1), range(5*K+1, 6*K+1)


def geometry():
    count = 0
    for K in range(1, 42):
        lo, hi = bands(K)
        s, t = (sum(F(1,k) for k in band) for band in (lo, hi))
        assert s-t >= F(1,12) and ((s-t == F(1,12)) == (K == 1))
        for m in range(6*K+3):
            q, e = (sum(m//k for k in band) for band in (lo,hi))
            assert q == max(0, min(4*K,m)-3*K) + int(m == 6*K+2)
            assert e == max(0, min(6*K,m)-5*K)
            count += 1
    return count


def source(K, H):
    N = 6*K
    lo, hi = bands(K)
    s, t = (sum(F(1,k) for k in band) for band in (lo, hi))
    fac = [None] + [factor(k) for k in range(1, N+1)]
    mu = [0] + [0 if any(e > 1 for e in f.values()) else (-1)**len(f) for f in fac[1:]]
    count = 0
    outputs = sorted({0,1,H,3*K,3*K+1,4*K,4*K+1,5*K,5*K+1,N,N+1,N+2,3*N+7})
    for prime in (p for p in range(2,N+1) if fac[p] == {p:1}):
        def val(k):
            return fac[k].get(prime,0)
        L = val(N)-val(H)
        f = [0] + [mu[k]*(val(N)-val(max(H,k))) for k in range(1,N+1)]
        u, v = sum(F(f[k],k) for k in range(1,N+1)), 2*L+sum(f)
        a, z = (u-t*v/K)/(s-t), (s*v/K-u)/(s-t)
        c = {k:a*int(k in lo)+z*int(k in hi)-f[k] for k in range(2,N+1)}
        assert sum(w/k for k,w in c.items()) == L and sum(c.values()) == 3*L
        for m in outputs:
            g, j = (sum(F(m%k,k) for k in band) for band in (lo,hi))
            D, P = (g-j)/(s-t), (s*j-t*g)/(s-t)
            q, e = (sum(m//k for k in band) for band in (lo,hi))
            assert (D,P) == (m-(q-e)/(s-t), (t*q-s*e)/(s-t))
            literal = L-sum(w*F(m%k,k) for k,w in c.items())
            bare = L+sum(f[k]*F(m%k,k) for k in range(1,N+1))
            assert literal == bare-u*D-F(v,K)*P
            count += 1
    return count


def inventory():
    expected = {'gap', 'residue_floor', 'first_layer', 'first_double', 'moments',
                'residual_profiles', 'floor_profiles'}
    files = [Path(f'research/NYMAN_RIDGE_{s}.lean') for s in ('GEOMETRY', 'PROFILES')]
    body = '\n'.join(p.read_text() for p in files)
    assert set(re.findall(r'^theorem nyman_ridge_(\w+)', body, re.M)) == expected
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', body)
    for path in ('ExactTypes', 'Audit'):
        text = Path(f'scripts/lean/nyman_ridge/{path}.lean').read_text()
        assert all('nyman_ridge_'+name in text for name in expected)


if __name__ == '__main__':
    inventory()
    rows = sum(source(K,H) for K,H in [(1,2),(2,3),(3,5),(6,6),(10,7),(24,12)])
    print(f'RIDGE: {geometry()} floor-pair rows; {rows} exact prime-log/output rows; 7 public interfaces')
