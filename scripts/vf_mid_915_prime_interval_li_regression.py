#!/usr/bin/env python3
"""#915 actual prime cofactor intervals q>sqrt(X) and exact floor-Li matching.

For the open current square block R^2<n<(R+1)^2, set X=(R+1)^2-1.
If n=c*q, q>R prime and odd c>=1, then

 max(R,R^2//c) < q <= X//c, with c<=R.

These ACTUAL prime intervals partition the large-prime-factor sites
without duplication. Every composite (c>=3 odd) retains its original VF
site charge +w_R, including squareful c; c=1 is a TRUE prime site
charged w_R-1. Per band actual count = floor-Li events + signed
integer prime/floor-Li mismatch boundary, not an approximation.

This checks cofactor-specific gaps, their SIGNED cancellation in aggregate,
and compatibility with actual physical sites. No short-interval RH theorem
is claimed and no parent is duplicated in the original NNS norm.
"""
import argparse
import math
from bisect import bisect_right

from vf_mid_915_floor_li_transport_regression import (
    li_floor, prime_sieve, block_weight
)


def run(R, prime, primes):
    X=(R+1)**2-1
    lower_sq=R*R
    assert X<=len(prime)-1
    def pi(n):
        return bisect_right(primes,n)
    w=block_weight(R)
    all_sites=set()
    li_total=actual_total=mismatch_total=0
    li_charge=actual_charge=0.
    hist_above=hist_below=0
    sample=[]
    values={}
    a=R//2+1
    for c in range(1,R+1,2):
        lower=max(R,lower_sq//c)
        upper=X//c
        if lower>=upper:
            continue
        actual=pi(upper)-pi(lower)
        ref=li_floor(upper)-li_floor(lower)
        err=actual-ref
        actual_total+=actual
        li_total+=ref
        mismatch_total+=err
        wt=(w-1) if c==1 else w
        actual_charge+=wt*actual
        li_charge+=wt*ref
        values[c]=(actual,ref,err,lower,upper)
        for q in primes[pi(lower):pi(upper)]:
            n=c*q
            assert q>R and (lower_sq<n<=X), (R,c,q,n)
            assert n%2==1
            assert n not in all_sites, (R,n,c,q)
            all_sites.add(n)
            if c==1:
                assert prime[n],(R,n)
            else:
                assert not prime[n],(R,n)
                if q>=a*a:
                    assert c==3,(R,n,c,q,a)
                    hist_above+=1
                else:
                    hist_below+=1
    physical_direct=0.
    for n in range(lower_sq+1,X+1):
        if not (n&1): continue
        found=False
        for c in range(1,R+1,2):
            if n%c:continue
            q=n//c
            if q>R and prime[q]:
                assert not found,(R,n,c,q)
                found=True
        if found:
            assert n in all_sites
            physical_direct+= w-int(bool(prime[n]))
    assert abs(physical_direct-actual_charge)<1e-8
    assert abs((actual_charge-li_charge)-w*(
        mismatch_total-(values[1][2] if 1 in values else 0)
    )+(values[1][2] if 1 in values else 0))<1e-7
    assert sum(int(not prime[n]) for n in all_sites)==hist_above+hist_below
    actual_prime=pi(X)-pi(lower_sq)
    assert values[1][0]==actual_prime
    print("STRATIFY R=%d X=%d sqrtBandStart=%d highprimePhysicalSites=%d "
          "oddHighComposites=%d c3AncestorRecent=%d cge5AncestorOlder=%d "
          "liBandEventMass=%d actualBandEventMass=%d signedLiMismatch=%+d "
          "physicalCharge=%.6f LIReferenceCharge=%.6f signedVFDelta=%+.6f PASS"
          %(R,X,a*a,len(all_sites),hist_above+hist_below,hist_above,
            hist_below,li_total,actual_total,mismatch_total,
            physical_direct,li_charge,physical_direct-li_charge))
    for c in (1,3,5,7,9,11,13,17,101):
        if c in values and (c<=17 or c==101):
            av,lv,err,lo,hi=values[c]
            print("COFACTOR R=%d c=%d primeInterval=(%d,%d] actual=%d "
                  "floorLi=%d Ehi-Elo=%+d "
                  "%s"%
                  (R,c,lo,hi,av,lv,err,
                   "PRIME_SITE" if c==1 else "COMPOSITE_DESCENDANT"))
    return mismatch_total


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--extended",action="store_true")
    args=parser.parse_args()
    roots=[317,1027]
    if args.extended:
        roots=[18,56,317,1027,2000]
    prime,primes=prime_sieve((max(roots)+1)**2)
    for R in roots:
        run(R,prime,primes)
    print("PASS exact cofactor-dependent sqrt(X) prime intervals and signed floor-Li masses")
    print("OPEN: all-scale SIGNED control of correlated E(X/c) - E(R^2/c) errors")


if __name__=="__main__":
    main()
