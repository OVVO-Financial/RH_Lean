#!/usr/bin/env python3
"""Exact actual owner-two AMP clipped/returned signed boundary census.

Source definitions: GLOBAL_RETURNED_CORE_WEIGHTED_GRAM,
GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE,
GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.
No fantasy sequences or independent-owner normalization.
"""
from array import array
from math import isqrt
import sys

RMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1600
assert RMAX >= 8
N = RMAX * RMAX - 1
isprime = bytearray(b'\x01') * (N + 1)
isprime[0:2] = b'\x00\x00'
for p in range(2, isqrt(N) + 1):
    if isprime[p]:
        isprime[p*p:N+1:p] = b'\x00' * (((N - p*p)//p)+1)
primes = [p for p in range(2, N+1) if isprime[p]]
mu = array('b',[1]) * (N+1)
mu[0] = 0
for p in primes:
    for n in range(p, N+1, p):
        mu[n] = -mu[n]
    if p*p <= N:
        for n in range(p*p, N+1, p*p):
            mu[n] = 0
M = array('i',[0])*(N+1)
Odd = array('i',[0])*(N+1)
total, oddtotal = 0, 0
for n in range(1, N+1):
    total += mu[n]
    if n & 1: oddtotal += mu[n]
    M[n] = total
    Odd[n] = oddtotal

oddprimes = [p for p in primes if p > 2 and p*p < RMAX]

def dyadic_odd(y):
    s = 0
    while y:
        s += M[y]
        y //= 2
    return s

for y in [1, 2, 6, 17, 100, 317, 1027, 10000, N]:
    if y <= N:
        assert Odd[y] == dyadic_odd(y), ('dyadic failure', y)

# At p=2 the genuine returned-parent site weight is:
# 1_{R <= 2a} + sum_{q odd prime, q^2 < R} (1/q)1_{2a <= X/q^2}.
def closed_boundary(R):
    X = R*R - 1
    qset = [q for q in oddprimes if q*q < R]
    C = M[X]
    J = Odd[X//2] - Odd[(R-1)//2] + sum(Odd[X//(2*q*q)]/q for q in qset)
    return C, J, -2*C*J

def direct_boundary(R):
    X = R*R - 1
    qset = [q for q in oddprimes if q*q < R]
    C = sum(mu[a] for a in range(1, X+1, 2) if X < 2*a)
    J = 0.0
    for a in range(1, X//2+1, 2):
        weight = float(R <= 2*a)
        for q in qset:
            weight += float(2*a <= X//(q*q)) / q
        J += mu[a]*weight
    return C, J, -2*C*J

for R in (8,17,56,119,317,1027):
    if R <= RMAX:
        a=closed_boundary(R)
        b=direct_boundary(R)
        assert a[0] == b[0] and abs(a[1]-b[1]) < 1e-8 and abs(a[2]-b[2]) < 1e-7, (R,a,b)
        print('verified-direct', R, 'C=M(X)',a[0], 'J',round(a[1],7), 'signed -2CJ',round(a[2],7))

pos=neg=zero=0
sumB=0.0
for R in range(8,RMAX+1):
    C,J,B=closed_boundary(R)
    pos += B>0
    neg += B<0
    zero += B==0
    sumB += B
print('all-root census',8,RMAX,'positive',pos,'negative',neg,'zero',zero,'signed-total',round(sumB,4))
for R in (8,17,56,119,317,1027,1600,2500):
    if R<=RMAX:
        C,J,B=closed_boundary(R)
        print('root',R,'M',C,'returned',f'{J:+.6f}','B',f'{B:+.6f}','B/R^2',f'{B/(R*R):+.8f}')
