"""Exact finite algebra regressions, not an infinite Nyman norm estimate.

Registered domain: Jordan 1..256; N=0..24, four rational signed vectors;
K=1..8, three repairs on the exact final-support gap. No numerical logs.
"""

from fractions import Fraction as F
from math import gcd, prod

checks = 0


def check(ok):
    global checks
    assert ok
    checks += 1


def jordan(n):
    return sum(gcd(gcd(n, a), b) == 1 for a in range(n) for b in range(n))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, n))


J = {0: 0}
for n in range(1, 257):
    J[n] = jordan(n)
    check(sum(J[d] for d in range(1, n+1) if n % d == 0) == n*n)
    check(J[n] == n*n*prod(F(p*p-1, p*p) for p in range(2, n+1)
                         if prime(p) and n % p == 0))
    check(2*J[n] >= n*n)
    check(prod((1-F(1, k*k) for k in range(2, n+1)), start=F(1)) == F(n+1, 2*n))


def covariance(a):
    return sum((a[k]*a[l]*F(gcd(k, l)**2-1, 12*k*l)
                for k in a for l in a), F(0))


for n in range(25):
    for seed in range(4):
        a = {k: F(((k+1)*(seed+3)) % 13-6, seed+1) for k in range(2, n+1)}
        V = covariance(a)
        D = sum((J[d]*sum((a[k]/k for k in a if k % d == 0), F(0))**2
                 for d in range(2, n+1)), F(0))
        check(12*V == D)
        check(sum(a[q]**2 for q in a if 2*q > n) <= 24*V)
        for q in a:
            if 2*q > n:
                check(sum((a[k]/k for k in a if k % q == 0), F(0)) == a[q]/q)

for K in range(1, 9):
    n = 6*K
    gap = list(range(4*K+1, 5*K+1))
    b = {q: F((-1)**q, q+1) for q in gap}
    for mode in range(3):
        e = {k: F((mode*k) % 7-3, k+1) for k in range(2, n+1)}
        c = {k: -b[k] if k in b else F(k % 5-2, 3) for k in e}
        a = {k: c[k]+e[k] for k in c}
        check(sum((e[q]-b[q])**2 for q in gap) <= 24*covariance(a))
        check(all(not (3*K < q <= 4*K or 5*K < q <= 6*K) for q in gap))

# Omission controls: a final-support extension destroys singleton recovery;
# deleting signed cross terms changes the original complete kernel.
a = {2: F(2), 4: F(-4)}
check(sum((a[k]/k for k in a if k % 2 == 0), F(0)) != a[2]/2)
diagonal = sum(a[k]**2*F(k*k-1, 12*k*k) for k in a)
check(covariance(a) != diagonal)
check(F(gcd(2, 3)**2-1, 12*2*3) == 0)
check(F(gcd(2, 3)**2, 12*2*3) != 0)
print(f"PASS {checks} exact assertions; finite covariance only; three omission controls")
