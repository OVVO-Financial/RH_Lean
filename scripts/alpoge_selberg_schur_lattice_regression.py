#!/usr/bin/env python3
"""Deterministic physical-prime signed Selberg band and Schur lattice regression.

No random prime assumptions. K2(p^2)=-log(p)^2 and
K2(pq)=2*log(p)*log(q) (p!=q), E(floor(X/n))=E(1)=-1
for the FULL band p,q in [3R/4,R). This test is NOT an RH bound.
"""
import math

def primes_up_to(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = b'\x00' * ((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]

def det3(a):
    (a0,b,c),(d,e,f),(g,h,i) = a
    return a0*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

tri = [[1 if i == j else -1 for j in range(3)] for i in range(3)]
assert det3(tri) == -4
# S=2I-J, S_3^2=4I-J and S_3*(I-J)=2I
assert [[sum(tri[i][k]*tri[k][j] for k in range(3))
         for j in range(3)] for i in range(3)] == [
         [3 if i==j else -1 for j in range(3)] for i in range(3)]
assert [[sum(tri[i][k]*(0 if k==j else -1) for k in range(3))
         for j in range(3)] for i in range(3)] == [
         [2 if i==j else 0 for j in range(3)] for i in range(3)]

for m in (3, 6, 9, 30, 300):
    for seed in range(1,6):
        v = [((i*19+seed*7)%21)-10 for i in range(m)]
        S = sum(v)
        y = [2*v[i]-S for i in range(m)]
        assert y == [sum((1 if i==j else -1)*v[j]
                          for j in range(m)) for i in range(m)]
        assert all((y[i]-y[j])%2 == 0 for i in range(m)
                   for j in (0,m-1))
        assert sum(y) == (2-m)*S
        vc = [m*v[i]-S for i in range(m)]  # integral centered direction
        assert sum(vc) == 0
        assert [sum((1 if i==j else -1)*vc[j] for j in range(m))
                for i in range(m)] == [2*z for z in vc]
        assert sum((2*z)**2 for z in vc)==4*sum(z*z for z in vc)

for R, expected in [(100,4),(317,14),(549,21),(1027,36),(3000,96)]:
    X = R*R-1
    primes = primes_up_to(R-1)
    P = [p for p in primes if 4*p >= 3*R]
    n = len(P)
    assert n == expected and n>=3
    for p in P:
        for q in P:
            assert p*q <= X < 2*p*q
            assert X//(p*q)==1
    w = [math.log(p) for p in P]
    # Independently count the true signed K2 source faces at E(1)=-1.
    diag = sum(math.log(p)**2 for p in P)   # K2(p²)*E(1)
    mixed = -2*sum(math.log(P[i])*math.log(P[j])
                   for i in range(n) for j in range(i+1,n))  # K2(pq)*E(1)
    face = diag+mixed
    schur = 2*sum(t*t for t in w)-sum(w)**2
    mean = sum(w)/n
    centered = 2*sum((t-mean)**2 for t in w)
    principal = -(n-2)*n*mean*mean
    assert abs(face-schur) <= 1e-9*max(1,abs(face))
    assert abs(face-centered-principal) <= 1e-9*max(1,abs(face))
    assert face<0
    # All logarithm weights are in [3/4 log R,log R] for R>=4.
    assert all(0.75*math.log(R) <= t <= math.log(R) for t in w)
    # Every disjoint triple has intrinsic integer determinant -4 and
    # 1<= singular values <=2 in normalized coefficient coordinates.
    blocks=n//3
    print(f'R={R} primes={n} index=v2({2*blocks}) on {blocks} disjoint '
          f'triples, F/R^2={face/R**2:+.8f}, '
          f'centered/R^2={centered/R**2:.9f}, '
          f'principal/R^2={principal/R**2:+.8f}')
print('PASS: authentic K2 diagonal+offdiagonal, square quotient one,')
print('      normalized 2I-J, nonunit lattice determinant and centered norm 2')
