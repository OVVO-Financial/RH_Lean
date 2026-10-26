#!/usr/bin/env python3
"""Reproducible independent finite audit of #919 a6/K / CORR4 quotient and hyperbola.
Uses integer-only SPF/euler-polynomial sieve; no RH hypotheses or stochastic fits.
"""
import argparse
from math import isqrt
import numpy as np


def data_sieves(n):
    spf = np.arange(n + 1, dtype=np.int32)
    for p in range(2, isqrt(n) + 1):
        if spf[p] == p:
            spf[p*p:n+1:p] = np.where(spf[p*p:n+1:p] == np.arange(p*p,n+1,p), p, spf[p*p:n+1:p])
    mu = np.zeros(n + 1, dtype=np.int8)
    mu[1] = 1
    a6 = np.zeros(n + 1, dtype=np.int16)
    a6[1] = 1
    high_p = np.zeros(n + 1, dtype=np.int32)
    for k in range(2,n+1):
        p = int(spf[k]); j = k // p
        high_p[k] = max(p,int(high_p[j]))
        if j % p == 0:
            mu[k] = 0
            if p >= 5 and (j//p) % p:
                a6[k] = a6[j//p]*(1 if p % 3 == 1 else -1)
        else:
            mu[k] = -mu[j]
            if p >= 5:
                a6[k] = a6[j]*(-2 if p%3 == 1 else 0)
    z = np.arange(n+1)
    s6 = np.where((z%6==1)|(z%6==5),mu,0).astype(np.int8)
    b6 = np.where(z%3==1,s6,np.where(z%3==2,-s6,0)).astype(np.int8)
    return spf,mu,a6,high_p,s6,b6


def q36(t):
    t = np.asarray(t, dtype=np.int64)
    c = lambda k: (k % 3 == 1).astype(np.int64)
    return c(t) - c(t//3) - c(t//4) + c(t//12)


def get_ramps(H):
    """Integer numerator R(d)*H^2: tent weight for h>=d."""
    weights = np.array([H-abs(h) for h in range(-H+1,H)],dtype=np.int64)
    tail = np.r_[np.cumsum(weights[::-1],dtype=np.int64)[::-1],0]
    def ramp(d):
        ar=np.asarray(d, dtype=np.int64)
        idx=np.clip(ar+H-1,0,len(tail)-1)
        return np.where(ar <= -H+1, H*H, np.where(ar>=H, 0, tail[idx]))
    return ramp


def buckets(pfx, a6, X,H,T, number_detail=16):
    maxu=(X+H-1)//(T+1)  # nonempty for m>T; larger u only contribute 0
    maxu_proposed=(X+H)//T
    ramp=get_ramps(H)
    small = np.zeros(maxu+1,dtype=np.int64)
    incr=np.zeros(maxu+1,dtype=np.int64)
    kprev=0
    for u in range(1,maxu+1):
        val=int(q36([u])[0]); incr[u]=val-kprev; kprev=val
        lo=T+1
        # whole-weight site m iff um <= X-H+1
        full=min((X-H+1)//u,(X+H-1)//u)
        total=0
        if full>=lo:
            total=int(pfx[full]-pfx[T])*H*H
        coll_start=max(lo,full+1)
        coll_end=(X+H-1)//u
        if coll_end>=coll_start:
            ms=np.arange(coll_start,coll_end+1,dtype=np.int64)
            total+=int(np.dot(a6[ms].astype(np.int64),ramp(u*ms-X)))
        small[u]=total
    contributions=small*incr
    btest={int(u):[int(incr[u]),float(small[u])/(H*H),float(contributions[u])/(H*H)] for u in range(1,min(number_detail,maxu)+1)}
    val=int(contributions.sum())
    print('Abel signed total, absolute-bucket total, #nonzero buckets:', val/(H*H), float(np.abs(contributions).sum())/(H*H), int(np.count_nonzero(contributions)))
    return val,maxu,maxu_proposed,btest,[(int(u),float(contributions[u])/(H*H)) for u in np.argsort(-np.abs(contributions))[0:12] if u>0]


def main(R,H,T):
    X=R*R-1
    if not (R>=4 and H>0 and 0<T<X-H):
        raise ValueError("require R>=4, H>0, and 0<T<R^2-1-H")
    n=X+H
    spf,mu,a6,hp,mu6,b6=data_sieves(n)
    pfx=np.r_[0, np.cumsum(a6[1:].astype(np.int64))]
    mertens=np.r_[0, np.cumsum(mu[1:].astype(np.int64))]
    hs=np.arange(-H+1,H,dtype=np.int64)
    w=H-np.abs(hs)
    xhs=X+hs
    total_num=int(np.dot(w,mertens[xhs])); total=total_num/H**2
    mv=int(mertens[X]);
    Q=q36(xhs[:,None]//np.arange(1,T+1)[None,:])
    low_per_h=(Q*a6[1:T+1]).sum(axis=1)
    low_num=int(np.dot(w,low_per_h)); low=low_num/H**2
    high=total-low
    A6=int(pfx[X]);pA6=int(pfx[X//2]);b1=A6-pA6
    begin=X//2+1
    ms=np.arange(begin,X+1,dtype=np.int32)
    ishigh=hp[ms]>R
    issplit=(spf[ms]==ms)&(ms%3==1)&(ms>R)
    highcomposite=ishigh&(~issplit)
    smooth=~ishigh
    e1=int(a6[ms[issplit]].sum())
    e2=int(a6[ms[highcomposite]].sum())
    e3=int(a6[ms[smooth]].sum())
    num_primes=int(issplit.sum())
    recovered_num,actualumax,proposedumax,details,largest=buckets(pfx,a6,X,H,T)
    # Cross-check at a few h the exact restored Mertens identity using bucket weights
    source=[]
    for y in [X-H+1,X,X+H-1]:
        m=np.arange(1,y+1,dtype=np.int64)
        source.append((y,int(np.dot(a6[1:y+1].astype(np.int64),q36(y//m))),int(mertens[y])))
    # Independent Dirichlet hyperbola check using moving vs frozen cutoffs.
    hy=[]
    for y in [X-H+1, X, X+H-1]:
        z=isqrt(y)
        aa=np.arange(1,z+1,dtype=np.int64)
        Fmu=np.cumsum(mu6.astype(np.int64)); Fb=np.cumsum(b6.astype(np.int64))
        term1=int(np.dot(mu6[aa].astype(np.int64),Fb[y//aa]))
        term2=int(np.dot(b6[aa].astype(np.int64),Fmu[y//aa]))
        overlap=int(Fmu[z]*Fb[z])
        v=term1+term2-overlap
        zfix=isqrt(X)
        af=np.arange(1,zfix+1,dtype=np.int64)
        naive=int(np.dot(mu6[af].astype(np.int64),Fb[y//af])+np.dot(b6[af].astype(np.int64),Fmu[y//af])-Fmu[zfix]*Fb[zfix])
        hy.append((y,z,v,int(pfx[y]),zfix,naive,naive-int(pfx[y])))
    assert recovered_num == total_num-low_num, 'Abel numerator identity failed'
    assert e1+e2+e3 == b1, 'bucket-1 partition failed'
    assert all(value==truth for _,value,truth in source), 'sharp restored Mobius formula failed'
    assert all(value==truth for _,_,value,truth,*_ in hy), 'moving hyperbola identity failed'
    print('R H T X=',R,H,T,X)
    print('M(X), A_H M, Low, High, high-share:',mv,total,low,high,high/total)
    print('A6(X), A6(X/2), u=1 sharp bucket:', A6,pA6,b1)
    print('u=1 dissection: split primes count, split a6, high split composites, R smooth, composite sum, net')
    print(num_primes,e1,e2,e3,e2+e3,e1+e2+e3)
    print('Q36 values 0..36:',list(map(int,q36(np.arange(37)))))
    print('Exact M=source checks:',source)
    print('quotient Abel high:',recovered_num/H**2,'integer numerator error:',recovered_num-(total_num-low_num),'Umax_actual',actualumax,'Umax_formula',proposedumax)
    print('first quotient contributions [u, dK, smoothed (A6-A6T), weighted]:',details)
    print('largest |signed| quotient contributions:',largest)
    print('hyperbola (Y, sqrtY, exact, A6, fixed_cutoff, naive, error):',hy)
    print('Coefficient abs mass T:',np.sum(np.abs(a6[1:T+1])), 'T:',T)
    # Frozen cutoff loses the moving diagonal whenever floor(sqrt(Y)) changes.
    zfix=isqrt(X)
    Fmu=np.cumsum(mu6.astype(np.int64)); Fb=np.cumsum(b6.astype(np.int64))
    t1=np.zeros(len(xhs),dtype=np.int64)
    t2=np.zeros(len(xhs),dtype=np.int64)
    for a in range(1,zfix+1):
        if mu6[a]: t1 += int(mu6[a])*Fb[xhs//a]
        if b6[a]: t2 += int(b6[a])*Fmu[xhs//a]
    overlap=int(Fmu[zfix]*Fb[zfix]); frozen=t1+t2-overlap
    mismatch=frozen-pfx[xhs]
    def avg(v): return float(np.dot(w.astype(np.float64),v))/H**2
    print('frozen-hyperbola averages term1, term2, overlap, naive, exact, defect:',
          avg(t1),avg(t2),overlap,avg(frozen),avg(pfx[xhs]),avg(mismatch))
    print('frozen-hyperbola mismatch sites, min, max:',
          int(np.count_nonzero(mismatch)),int(np.min(mismatch)),int(np.max(mismatch)))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--R',type=int,default=1027);parser.add_argument('--H',type=int,default=5000);parser.add_argument('--T',type=int,default=150); ns=parser.parse_args();main(ns.R,ns.H,ns.T)
