"""Exact prime coordinates of the original Mobius taper; no numerical logarithms."""
from fractions import Fraction as F
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def valuation(n, p):
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def mobius(n):
    sign, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            sign = -sign
            if n % d == 0:
                return 0
        d += 1
    return -sign if n > 1 else sign


def check():
    bands_checked = heads = cells = 0
    for K in range(1, 41):
        N = 6 * K
        lo, hi = range(3*K+1, 4*K+1), range(5*K+1, N+1)
        s, t = (sum(F(1, k) for k in I) for I in (lo, hi))
        primes = [p for p in range(3*K+1, N) if prime(p)]
        assert primes
        for p in primes:
            for I, mass in ((lo, s), (hi, t)):
                scaled = p * mass
                assert scaled.denominator % p and (scaled.numerator * pow(scaled.denominator, -1, p)) % p == int(p in I)
                assert mass != F(K, p)
                bands_checked += 1
        p = primes[-1]
        for H in sorted({1, 3*K, p-1}):
            # Do not put in the desired (1/p,1) coordinates by hand.
            Lp = valuation(N, p) - valuation(H, p)
            kernel = {k: mobius(k)*(valuation(N, p)-valuation(max(H, k), p)) for k in range(1, N+1)}
            U = sum(F(w, k) for k, w in kernel.items())
            V = 2*Lp + sum(kernel.values())
            assert (Lp, U, V) == (0, F(1, p), 1)
            a, z = (U-t*V/K)/(s-t), (s*V/K-U)/(s-t)
            assert a and z
            weighted = 0
            for m in range(6*K+1, 10*K+3):
                raw = Lp - sum((a*int(k in lo)+z*int(k in hi)-kernel[k])*F(m % k, k) for k in range(2, N+1))
                no_repair = Lp + sum(w*F(m % k, k) for k, w in kernel.items())
                clipped = no_repair-a*(m*s-K)-z*(m*t-K)
                err = raw - clipped
                if m == N+1:
                    assert err == 0
                if m == N+2:
                    assert err == a
                if 8*K <= m <= 9*K+2:
                    assert err == K*a
                    weighted += err**2 / (m*(m+1))
                cells += 1
            assert weighted == (K*a)**2 * (F(1, 8*K)-F(1, 9*K+3))
            assert weighted > F(K, 72)*a**2
            heads += 1
    print(f'WITNESS: {bands_checked} prime/band rows, {heads} original head/prime fixtures, {cells} weighted-output comparisons')


if __name__ == '__main__':
    check()
