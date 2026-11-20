"""Reconstruct prime rows of L*(physical minus clipped) without real logs."""
from fractions import Fraction as F
from math import isqrt, lcm


def factor(n):
    factors = {}
    for d in range(2, isqrt(n) + 1):
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
    if n > 1:
        factors[n] = 1
    return factors


def check():
    nheads = noutputs = nplateaux = 0
    for K in range(1, 19):
        N = 6*K
        fac = {k: factor(k) for k in range(1, N + 1)}
        mu = {k: 0 if any(e > 1 for e in f.values()) else (-1)**len(f) for k, f in fac.items()}
        primes = [p for p in range(3*K+1, N) if fac[p] == {p: 1}]
        lo, hi = range(3*K+1, 4*K+1), range(5*K+1, N+1)
        s, t = (sum(F(1, k) for k in band) for band in (lo, hi))
        period = lcm(*range(2, N+1))
        for H in sorted({1, 2, 3, 3*K, primes[-2]-1 if len(primes) >= 2 else 1}):
            eligible = [p for p in primes if p > H]
            if len(eligible) < 2:
                if K != 1 or H > 3:
                    continue
                p, q = 5, 2  # independent small-head control; not the two-interior-prime hypothesis
            else:
                p, q = eligible[0], eligible[-1]
            rows = []
            for r in (p, q):
                L = fac[N].get(r, 0) - fac[H].get(r, 0)
                kernel = {k: mu[k]*(fac[N].get(r, 0)-fac[max(H,k)].get(r, 0)) for k in fac}
                u = sum(F(w, k) for k, w in kernel.items())
                v = 2*L + sum(kernel.values())
                if r in eligible:
                    assert (u, v) == (F(1, r), 1)
                a, z = (u-t*v/K)/(s-t), (s*v/K-u)/(s-t)
                rows.append((L, kernel, u, v, a, z))
            a0, z0 = rows[0][-2:]
            a1, z1 = rows[1][-2:]
            determinant = a0*z1-a1*z0
            assert determinant != 0
            if len(eligible) >= 2:
                assert determinant == (F(1, p)-F(1, q))/(K*(s-t))
            seen_values, seen_counts = {}, {}
            for m in [*range(0, 15*K+4), period, period+N, 2*period+N]:
                counts = (sum(m//k for k in lo), sum(m//k for k in hi))
                residues = {k: F(m % k, k) for k in range(2, N+1)}
                error = []
                for L, kernel, u, v, a, z in rows:
                    physical = L - sum((a*(k in lo) + z*(k in hi) - kernel[k])*f for k, f in residues.items())
                    flat = L + sum(kernel[k]*f for k, f in residues.items())
                    clipped = flat - u*m - F(v, K)*(t*K-s*K)/(s-t)
                    err = physical-clipped
                    assert err == a*(counts[0]-K) + z*(counts[1]-K)
                    if m == period+N or m == 2*period+N:
                        assert err == (m-N)*u
                    error.append(err)
                value = tuple(error)
                assert (value == (0, 0)) == (m in (N, N+1))
                assert seen_values.setdefault(value, counts) == counts
                assert seen_counts.setdefault(counts, value) == value
                noutputs += 1
            nplateaux += len(seen_counts)
            nheads += 1
    print(f'{nheads} heads; {noutputs} tested outputs; {nplateaux} distinct joint counts across heads')


if __name__ == '__main__':
    check()
