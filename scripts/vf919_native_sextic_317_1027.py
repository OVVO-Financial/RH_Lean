#!/usr/bin/env python3
"""Exact Eisenstein sextic ideal-row census for BOTH x and R = 317/1027.

Independent stdlib-only calculation. In O=Z[omega], omega^2+omega+1=0,
zeta6=1+omega. A split p=1(mod3) has two prime ideals indexed by distinct
roots t of t^2+t+1=0 in F_p. For primary alpha=a+b*omega (a=1,b=0 mod3),
the genuine canonical sextic value chi_{p,t}(alpha)=zeta6^e is characterized
by (1+t)^e=(a+b*t)^((p-1)/6) mod p. This is precisely the finite residue
rule of OAI GaussSum/FiniteFourier.lean sexticChar_reduce_unit, implemented
here WITHOUT importing the analytic proof.

For the four cutoffs, enumerate true integer mu(n), unique high split prime
p>sqrt(x) or p>R, squarefree representable ideal-norm cofactor k=n/p,
all distinct primary cofactor generators and BOTH prime ideals over p.
No norm-only flattening, no numeric approximation and no analytic 7/8 claim.
"""
from collections import Counter
from functools import lru_cache
from math import gcd, isqrt

CASES = {
    ("x", 317): (19, 7, (7, 11), ((-2,-3,(5,5)), (1,3,(1,1))), 2),
    ("x", 1027): (37, 7, (10, 26), ((-2,-3,(1,3)), (1,3,(3,5))), -1),
    ("R", 317): (439, 229, (171, 267), ((-17,-12,(0,4)), (-5,12,(2,0))), 1),
    ("R", 1027): (3727, 283, (1188, 2538), ((13,-6,(3,1)), (19,6,(5,3))), -1),
}
EXPECTED = {
    ("x", 317): (33, 76, -4, (58,4,3,4,3,4), (-57,0)),
    ("x", 1027): (97, 232, -3, (168,13,14,10,14,13), (-155,0)),
    ("R", 317): (49, 160, 11, (70,15,20,20,20,15), (-47,0)),
    ("R", 1027): (140, 452, -20, (196,55,51,44,51,55), (-124,0)),
}
# Exactly zeta6^e in the 1,zeta6 basis, no floating point.
ZETA = ((1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1))


def sieve(n):
    lp,mu,ps=[0]*(n+1),[0]*(n+1),[]
    mu[1]=1
    for i in range(2,n+1):
        if not lp[i]:lp[i]=i;mu[i]=-1;ps.append(i)
        for p in ps:
            if p>lp[i] or i*p>n:break
            lp[i*p]=p
            if p==lp[i]:mu[i*p]=0;break
            mu[i*p]=-mu[i]
    greatest=[0]*(n+1)
    for p in ps:
        for i in range(p,n+1,p):greatest[i]=p
    return mu,greatest,set(ps)


@lru_cache(None)
def roots(p):
    assert p>3 and p%6==1
    g=2
    while pow(g,(p-1)//3,p)==1:g+=1
    t=pow(g,(p-1)//3,p)
    pair=tuple(sorted((t,(-1-t)%p)))
    assert pair[0]!=pair[1]
    assert all((r*r+r+1)%p==0 for r in pair)
    assert all(len({pow((1+r)%p,e,p) for e in range(6)})==6 for r in pair)
    return pair


@lru_cache(None)
def primary(k):
    bnd=isqrt(4*k//3)+5
    pairs=tuple((a,b) for a in range(-bnd,bnd+1) if a%3==1
        for b in range(-bnd,bnd+1) if b%3==0 and a*a-a*b+b*b==k)
    assert all((a-b,-b) in pairs for a,b in pairs)
    return tuple(sorted(pairs))


def exponent(p,r,a,b):
    v=(a+b*r)%p
    if not v:return None
    target=pow(v,(p-1)//6,p)
    es=[e for e in range(6) if pow((1+r)%p,e,p)==target]
    assert len(es)==1
    return es[0]


def phases(p,a,b):
    return tuple(exponent(p,r,a,b) for r in roots(p))


def exact_sum(hist):
    return tuple(sum(hist[e]*ZETA[e][j] for e in range(6)) for j in (0,1))


def interval(mode,v):
    return (0,v,isqrt(v)) if mode=="x" else (v*v,(v+1)**2-1,v)


def main():
    mu,lp,primes=sieve(1028**2-1)
    for (mode,v),(p0,k0,expected_roots,expected_gens,expected_twist) in CASES.items():
        left,right,cut=interval(mode,v)
        assert (roots(p0)==expected_roots and p0 in primes and
                k0 in primes and p0>cut>=k0 and left<p0*k0<=right and
                mu[p0*k0]==1)
        gens=primary(k0)
        witness=tuple((a,b,phases(p0,a,b)) for a,b in gens)
        assert witness==expected_gens,(mode,v,witness,expected_gens)
        wh=Counter(e for a,b,ee in witness for e in ee)
        assert exact_sum(wh)==(expected_twist,0)
        # Four distinct ideal pairs over split rational p0*k0: coefficient
        # a_F(p0*k0)=+4; true integer Mobius mu(p0*k0)=+1.
        assert len(witness)*2==4
        assert len({ee for _,_,ee in witness})>1
        for a,b in gens:
            ea,eb=phases(p0,a,b)
            ca,cb=phases(p0,a-b,-b)
            assert ca==(-eb)%6 and cb==(-ea)%6

        count,rows=0,0
        hist,signed=Counter(),Counter()
        for n in range(left+1,right+1):
            p=lp[n]
            if p<=cut or p%3!=1 or mu[n]==0:continue
            k=n//p
            if k<=0 or k>cut or gcd(k,6)!=1:continue
            gs=primary(k)
            if not gs:continue
            count+=1
            for a,b in gs:
                for e in phases(p,a,b):
                    assert e is not None
                    hist[e]+=1
                    signed[e]+=mu[n]
                    rows+=1
        h=tuple(hist[e] for e in range(6))
        result=(count,rows,sum(mu[left+1:right+1]),h,exact_sum(signed))
        assert result==EXPECTED[(mode,v)],(mode,v,result,EXPECTED[(mode,v)])
        assert all(h) # Every sixth-root phase appears in all four datasets.
        print(f"{mode}={v} interval=({left},{right}] high_p>{cut} "
              f"M_increment={result[2]} split_norm_seats={count} "
              f"ideal_rows={rows} phases={h} signed_Z[zeta6]={result[4]}")
        print(f"  p={p0} k={k0} n={p0*k0} roots={expected_roots} "
              f"primary_phase_rows={witness} sum={expected_twist} "
              f"a_F(n)=4 mu_Z(n)=1")

if __name__=="__main__":
    main()
