#!/usr/bin/env python3
"""Actual prime q -> odd composite c*q owner-matched diagnostic for #918.

Every selected historical prime is an ACTUAL pi event and every target
odd composite is a physical original +w_R VF seat. A selected pair
is divergent by sign; these are NOT additional cancellation budgets.
"""
import math
import numpy as np


def audit(roots=(119, 317, 1027, 1760, 5267, 6000)):
    hi=max(roots)
    maxq=((hi+1)**2-1)//3
    sieve=bytearray(b'\x01')*(maxq+1)
    sieve[:2]=b'\x00\x00'
    for p in range(2,math.isqrt(maxq)+1):
        if sieve[p]:
            sieve[p*p::p]=b'\x00'*((maxq-p*p)//p+1)
    primes=np.flatnonzero(np.frombuffer(sieve,dtype=np.uint8))

    for R in roots:
        A=R//2+1
        w=(2*R+1)/(R*math.log(R*R+R+0.5))
        count=0
        recent=0
        total_div=0.0
        recent_div=0.0
        c3=0
        seen_high_parents=set()
        for c in range(3,R+1,2):
            lo=max(R,R*R//c)
            upper=((R+1)**2-1)//c
            if upper<=lo:
                continue
            q=primes[np.searchsorted(primes,lo,side='right'):
                     np.searchsorted(primes,upper,side='right')]
            if len(q)==0:
                continue
            assert np.all(c*q>R*R) and np.all(c*q<(R+1)**2)
            for ancestor in q:
                ancestor=int(ancestor)
                assert ancestor not in seen_high_parents, (R,ancestor,c)
                seen_high_parents.add(ancestor)
            s=np.floor(np.sqrt(q)).astype(np.int64)
            assert np.all(s>=2) and np.all(s<R)
            old_w=(2*s+1)/(s*np.log(s*s+s+0.5))
            charges=w*(1-old_w)
            count+=len(q)
            total_div+=float(np.sum(charges))
            present=s>=A
            recent+=int(np.sum(present))
            recent_div+=float(np.sum(charges[present]))
            if c==3:
                c3=len(q)
            if np.any(present):
                assert c==3, ("half-run high-q parent cofactor must be 3",R,c)
        assert recent==c3
        print("OWNER_MATCH R=%d A=%d high_q_odd_composites=%d "
              "half_run_actual_parents=%d earlier_parents=%d "
              "all_selected_divergent=%.6f half_run_divergent=%.6f PASS" %
              (R,A,count,recent,count-recent,total_div,recent_div))



def sparse_full(maxroot=6000):
    """Whole-panel actual semiprime/triple and calibrated floor-Li census."""
    from scipy.special import expi
    assert 8<=maxroot<=6000
    top=(maxroot+1)**2
    rootflag=bytearray([1])*(maxroot+2)
    rootflag[:2]=bytearray([0,0])
    for p in range(2,math.isqrt(maxroot+1)+1):
        if rootflag[p]:
            rootflag[p*p::p]=bytearray([0])*((maxroot+1-p*p)//p+1)
    primes=np.array([p for p in range(3,maxroot+2,2) if rootflag[p]],
                    dtype=np.int64)
    least=np.zeros((top+1)//2,dtype=np.uint16)
    for p in primes:
        j=(int(p*p)-1)//2
        block=least[j::int(p)]
        block[block==0]=p
    bound=max(((r+1)**2-1)//(math.isqrt(r)+1)
              for r in range(8,maxroot+1))
    flag=bytearray([1])*(bound+1)
    flag[:2]=bytearray([0,0])
    for p in range(2,math.isqrt(bound)+1):
        if flag[p]:flag[p*p::p]=bytearray([0])*((bound-p*p)//p+1)
    pi=np.cumsum(np.frombuffer(flag,dtype=np.uint8),dtype=np.int64)
    R=np.arange(8,maxroot+1,dtype=np.int64)
    P=np.zeros(len(R),dtype=np.int64)
    G=P.copy()
    S=P.copy()
    sem=P.copy()
    for j,n in enumerate(R):
        r=int(n)
        first=r*r+1+(r%2)
        owner=least[(first-1)//2:(first-1)//2+r]
        P[j]=np.count_nonzero(owner==0)
        G[j]=np.count_nonzero((owner>0)&(owner.astype(np.int64)**2<=r))
        S[j]=r-P[j]-G[j]
        ps=primes[(primes>math.isqrt(r))&(primes<=r)]
        if len(ps):
            high=((r+1)**2-1)//ps
            low=r*r//ps
            assert high.max()<len(pi)
            sem[j]=np.sum(pi[high]-pi[low])
        assert 0<=sem[j]<=S[j]
    Q=expi(np.log(np.arange(8,maxroot+2,dtype=float)**2))-expi(math.log(2))
    assert np.min(abs(Q-np.rint(Q)))>2e-8
    F=np.diff(np.floor(Q)).astype(np.int64)
    sigma=S-(P+S-F)
    assert np.array_equal(sigma,F-P)
    print("SPARSE_FULL R=8..%d blocks=%d semiprimes=%d triples=%d "
          "semiprime_share=%.9f raw_sparse_lag1=%.9f "
          "sparse_floorLi_residual_lag1=%.9f PASS" %
          (maxroot,len(R),sum(sem),sum(S-sem),sum(sem)/sum(S),
           np.corrcoef(S[:-1],S[1:])[0,1],
           np.corrcoef(sigma[:-1],sigma[1:])[0,1]))


if __name__=="__main__":
    import sys
    audit()
    if "--sparse-full" in sys.argv:
        sparse_full()
