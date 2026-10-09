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


if __name__=="__main__":
    audit()
