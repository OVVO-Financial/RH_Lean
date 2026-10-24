#!/usr/bin/env python3
"""One-sided integrated Li fan, TRUE prime/composite weighted-owner arithmetic.

Finite independent census only, NOT an RH proof.
Requires mpmath for high-precision floor Li_2 and classic li evaluation.
"""
from __future__ import annotations

import math
from mpmath import mp

mp.dps = 44
MAX = 3500
spf = list(range(MAX + 1))
for p in range(2, math.isqrt(MAX) + 1):
    if spf[p] == p:
        for k in range(p*p, MAX + 1, p):
            if spf[k] == k:
                spf[k] = p

is_prime = [False, False] + [spf[k] == k for k in range(2,MAX+1)]
pi = [0] * (MAX + 1)
q = [0] * (MAX + 1)
li2 = mp.li(2)

for n in range(2, MAX + 1):
    pi[n] = pi[n-1] + int(is_prime[n])
    q[n] = int(mp.floor(mp.li(n) - li2))
    if n >= 3:
        assert q[n] - q[n-1] in (0, 1), (n, q[n]-q[n-1])

assert q[2] == 0 and pi[2] == 1

samples = [5,9,16,25,100,400,1000,2500,3481]
for N in samples:
    G = sum(pi[n] - q[n] - 1 for n in range(2,N))
    mismatch = sum(
        (N-k) * (int(is_prime[k]) - (q[k] - q[k-1]))
        for k in range(3,N)
    )
    m = (N-2)//2
    A = m*(N-m-2)
    T = sum(N-k for k in range(3,N,2) if not is_prime[k])
    L = sum(q[n] for n in range(2,N))
    assert G == mismatch == A-T-L, (N,G,mismatch,A-T-L)

    # Exact integral of classical li, not repository Li_2.
    # Integral_2^N li(t) dt =
    # N*li(N)-li(N^2)-2*li(2)+li(4).
    weighted_prime_supply = sum(N-k for k in range(2,N) if is_prime[k])
    H = (mp.mpf(weighted_prime_supply) -
         (N*mp.li(N) - mp.li(N*N) - 2*li2 + mp.li(4)))
    assert H <= G, (N,H,G)
    assert 0 <= G-H < (li2+1/mp.log(2))*(N-2), (N,H,G)

    owner = None
    if math.isqrt(N)**2 == N:
        R = math.isqrt(N)
        # Actual interior blocks have all composites owned by p<=r.
        # Odd square endpoints require SEPARATE billing.
        interior = 0
        for r in range(2,R):
            for k in range(r*r+1,(r+1)*(r+1)):
                if k%2 and not is_prime[k]:
                    assert 3 <= spf[k] <= r, (R,r,k,spf[k])
                    interior += N-k
        boundary = sum(N-s*s for s in range(3,R,2))
        owner = interior + boundary
        assert owner == T, (N, owner, T)

    print('N=%d G=%d H=%s G-H=%s A=%d T=%d L=%d owner=%s' %
          (N,G,mp.nstr(H,11),mp.nstr(G-H,8),A,T,L,owner))

print('PASS: true primes, floor Li_2, ternary mismatch,')
print('      exact weighted S=A-T, odd-square owner boundary,')
print('      classic-li integrated area, and O(N) normalization.')
print('OPEN: universal eventual ONE-SIDED weighted removal inequality.')
