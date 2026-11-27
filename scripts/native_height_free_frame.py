#!/usr/bin/env python3
"""Native squarefree high-prime decoder: exact Gram identities and slope-tail audit.
The maps are actual divisor incidences, NOT the original period pairing or Ga.
"""
from fractions import Fraction as F
from math import gcd, isqrt, fsum, log, sqrt, asinh, exp
from bisect import bisect_right
from array import array
import csv
from pathlib import Path


def sieve(N):
    prime=bytearray(b'\x01')*(N+1)
    prime[:2]=b'\x00\x00'
    for p in range(2,isqrt(N)+1):
        if prime[p]:
            prime[p*p::p]=b'\x00'*((N-p*p)//p+1)
    sf=bytearray(b'\x01')*(N+1);sf[0]=0
    for p in range(2,isqrt(N)+1):
        if prime[p]:
            pp=p*p;sf[pp::pp]=b'\x00'*(N//pp)
    return array('I',(i for i in range(2,N+1) if prime[i])),sf


def exact_gram(R,z):
    N=R*R-1;ps,sf=sieve(N);S=[n for n in range(1,N+1) if sf[n]]
    rough=[True]*(N+1)
    for p in ps:
        if p>z:break
        for k in range(p,N+1,p):rough[k]=False
    cols={b:{a for a in S if a<=b and b%a==0 and rough[b//a]} for b in S}
    A={b:F(sum(cols[b]),b) for b in S}
    defect=F(0);tr=F(0);tr2=F(0);checks=0
    for i,b in enumerate(S):
        tr+=A[b];tr2+=A[b]**2;defect+=(A[b]-1)**2
        for c in S[:i]:
            g=gcd(b,c);u=b//g;v=c//g
            actual=sum(cols[b]&cols[c]);pred=g*A[g] if rough[u] and rough[v] else F(0)
            assert actual==pred
            q=F(actual*actual,b*c)
            defect+=2*q;tr2+=2*q;checks+=1
    D=len(S);assert defect==tr2-2*tr+D
    eta=D*tr2/tr**2-1
    assert 0<=eta<=defect/D
    # Coarse proved upper bound: e^1.5<5, (exp(3/z)-1)<15/z for z>=2.
    assert defect<=F(35*N,z)
    if z>=R:
        t=[sum((F(1,p) for p in ps if p>z and a*p<=N),F(0)) for a in S if a<R]
        assert defect==2*sum(t)+sum(x*x for x in t)
    return D,defect,eta,checks


def layer_cake(xs,ys):
    # Pure finite-array diagnostic of the distributional step, not lattice witnesses.
    s=sum(xs,F(0))/len(xs);u=max(xs)-s;H=max(F(0),s-min(ys))
    breaks=sorted({F(0),H}|{min(H,max(F(0),s-x)) for x in xs+ys})
    A=F(0);B=F(0)
    for l,r in zip(breaks,breaks[1:]):
        t=(l+r)/2
        alpha=F(sum(x<s-t for x in xs),len(xs))
        beta=F(sum(y<s-t for y in ys),len(ys))
        A+=(r-l)*alpha;B+=(r-l)*beta
    assert A==sum((min(H,max(F(0),s-x)) for x in xs),F(0))/len(xs)
    assert B==sum((max(F(0),s-y) for y in ys),F(0))/len(ys)
    assert A<=u and s-sum(ys,F(0))/len(ys)<=B
    return A,B


def main():
    checks=0
    for R in (4,8,12,16):
        for z in sorted({2,3,5,R}):
            D,e,eta,n=exact_gram(R,z);checks+=n
            print('exact',R,z,D,float(e),float(eta))
    # Deterministic exhaustive small arrays check the finite layer-cake identity.
    from itertools import product
    layers=0
    for xs in product(range(-2,3),repeat=3):
        for ys in product(range(-3,4),repeat=2):
            layer_cake(list(map(F,xs)),list(map(F,ys)));layers+=1
    print('exact off-diagonal Gram checks',checks,'finite-layer-cake checks',layers)
    roots=(64,317,1027,2048,4096,8192)
    ps,sf=sieve(roots[-1]**2-1)
    pref=array('d',[0.0]);s=0.0
    for p in ps:
        s+=1.0/p;pref.append(s)
    out=[]
    for R in roots:
        N=R*R-1;D=sum(sf[:N+1]);i=bisect_right(ps,R)
        t=[];edges=0
        for a in range(1,R):
            if not sf[a]:continue
            j=bisect_right(ps,N//a)
            if j>i:
                t.append(pref[j]-pref[i]);edges+=j-i
        L1=fsum(t);L2=fsum(x*x for x in t);defect=2*L1+L2
        eta=(D*defect-L1*L1)/(D+L1)**2
        lognormsq=2*asinh(sqrt(max(t,default=0))/2)
        out.append((R,N,D,len(t),edges,defect,defect/R,defect*log(R)/R,defect/D,eta,lognormsq))
        print('root',out[-1])
    path=Path(__file__).with_name('native_height_free_frame_results.csv')
    with path.open('w',newline='') as f:
        w=csv.writer(f);w.writerow(('R','N','squarefree_dimension','rank_S','high_prime_edges','gram_HS2','HS2_over_R','HS2_logR_over_R','e','eta','log_operator_norm_sq'));w.writerows(out)

if __name__=='__main__':main()
