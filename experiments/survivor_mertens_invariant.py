#!/usr/bin/env python3
"""Fibrewise invariant behind the x=210 survivor ledger.

For arbitrary x >= 2, let R=floor(sqrt(x)). Every squarefree outer state has a
unique prime factor p>R and may be written n=c*p with c<p. Pair odd c*p with
2*c*p whenever the child remains <=x. The unpaired p-fibre has signed amplitude

    -M(floor(x/p)).

This script verifies that identity prime-by-prime for every 2 <= x <= 10000.
"""

from __future__ import annotations
import math
from collections import defaultdict

NMAX = 10_000

def sieve(n: int):
    is_comp = [False]*(n+1)
    primes=[]
    mu=[0]*(n+1)
    mu[1]=1
    lpf=[1]*(n+1)
    for i in range(2,n+1):
        if not is_comp[i]:
            primes.append(i)
            mu[i]=-1
        for p in primes:
            if i*p>n:
                break
            is_comp[i*p]=True
            if i%p==0:
                mu[i*p]=0
                break
            mu[i*p]=-mu[i]
    for p in primes:
        for m in range(p,n+1,p):
            lpf[m]=p
    M=[0]*(n+1)
    s=0
    for i in range(1,n+1):
        s+=mu[i]
        M[i]=s
    return primes,mu,lpf,M

PRIMES,MU,LPF,MERTENS=sieve(NMAX)

def check_x(x: int):
    root=math.isqrt(x)
    outer=[n for n in range(1,x+1) if MU[n]!=0 and LPF[n]>root]
    outer_set=set(outer)
    paired=set()
    for n in outer:
        if n%2==1 and 2*n in outer_set:
            paired.add(n); paired.add(2*n)
    survivors=[n for n in outer if n not in paired]

    by_prime=defaultdict(int)
    for n in survivors:
        by_prime[LPF[n]] += MU[n]

    transform=0
    for p in PRIMES:
        if p<=root:
            continue
        if p>x:
            break
        y=x//p
        lhs=by_prime.get(p,0)
        rhs=-MERTENS[y]
        assert lhs==rhs, (x,p,y,lhs,rhs)
        transform += MERTENS[y]

    total=sum(MU[n] for n in survivors)
    assert total == -transform, (x,total,-transform)

    # Once sqrt(x) >= 2, every post-root prime is odd and the survivors are
    # exactly the odd top-half outer states.  For x=2,3 the exceptional
    # post-root prime p=2 still satisfies the fibrewise Mertens identity, but
    # the odd-state description is not applicable.
    if root >= 2:
        assert survivors == [
            n for n in outer if n%2==1 and x//2 < n <= x
        ], x

    return len(survivors), total

def main():
    samples={}
    for x in range(2,NMAX+1):
        count,total=check_x(x)
        if x in (210,224,317,3135,10000):
            samples[x]=(count,total)

    assert samples[210] == (38,0)
    assert samples[224] == (42,4)
    assert samples[317] == (59,-1)
    assert samples[3135] == (557,47)

    print(f"survivor Mertens invariant: PASS for every 2 <= x <= {NMAX}")
    for x,(count,total) in samples.items():
        print(f"x={x}: survivors={count}, amplitude={total}")

if __name__ == "__main__":
    main()
