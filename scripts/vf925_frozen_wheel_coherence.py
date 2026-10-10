#!/usr/bin/env python3
"""#925 genuine A-wheel / rank-two semiprime transport stress test.

All P, pi and semiprime incidences are exact integer counts from a prime sieve.
VF, primorial density and phases are numerical float evaluations. The signed
wheel-phase / prime-pair cancellation is an exact FINITE identity, not RH.
"""
import argparse
import bisect
import json
import math


def sieve_flags(upper):
    flags=bytearray(b'\x01')*(upper+1)
    flags[:2]=b'\x00\x00'
    for p in range(2,math.isqrt(upper)+1):
        if flags[p]:flags[p*p::p]=b'\x00'*((upper-p*p)//p+1)
    return flags


def run(max_anchor):
    max_root=2*max_anchor
    flags=sieve_flags(max_root*max_root)
    low_primes=[n for n in range(2,4*max_anchor+1) if flags[n]]
    pi_sq=[0]*(max_root+1)
    count=0
    prev=1
    for root in range(2,max_root+1):
        square=root*root
        count+=flags[prev+1:square+1].count(1)
        pi_sq[root]=count
        prev=square
    VF=[0.]*(max_root+1)
    for r in range(2,max_root):
        VF[r]=VF[r-1]+(2*r+1)/math.log(r*r+r+.5)
    # VF[R-1] is sum_{2 <= r < R} V_r.
    def reference(A,B):return VF[B-1]-VF[A-1]
    density=[1.0]*(max_anchor+1)
    prod=1.0
    pos=0
    for r in range(max_anchor+1):
        while pos<len(low_primes) and low_primes[pos]<=r:
            p=low_primes[pos]
            prod*=1-1/p
            pos+=1
        density[r]=prod
    def case(A,B):
        assert 20<=A<=max_anchor and A<B<=2*A
        lower=A*A;upper=B*B-1
        P=pi_sq[B]-pi_sq[A]
        start=bisect.bisect_right(low_primes,A)
        stop=bisect.bisect_left(low_primes,B)
        late=0
        for p in low_primes[start:stop]:
            U=upper//p
            late+=bisect.bisect_right(low_primes,U)-bisect.bisect_right(low_primes,p)
        open_span=B*B-A*A-(B-A)
        bulk=density[A]*open_span
        wheel=P+late-bulk
        V=reference(A,B)
        deterministic=bulk-V
        arithmetic=late-wheel
        residual=P-V
        assert abs((deterministic-arithmetic)-residual)<1e-6
        return dict(A=A,B=B,prime_supply=P,rank_two_semiprimes=late,
            frozen_wheel_survivors=P+late,bulk_density=bulk,
            signed_wheel_boundary=wheel,VF_reference=V,
            deterministic_offset=deterministic,
            arithmetic_restoration=arithmetic,remaining_signed_residual=residual,
            restoration_ratio=arithmetic/deterministic if deterministic else None)
    values=[case(A,2*A) for A in range(20,max_anchor+1)]
    ratios=sorted(z['restoration_ratio'] for z in values)
    N=len(values)
    checks=[case(317,395)]
    if max_anchor>=1000:
        checks.append(case(1000,1102))
    if max_anchor>=2000:
        checks.append(case(2000,2120))
    if max_anchor>=2634:
        checks.append(case(2634,5267))
    if max_anchor>=2709:
        checks.append(case(2709,5417))
    if max_anchor==3000:
        assert all(z['signed_wheel_boundary']<0 for z in values)
        assert all(z['deterministic_offset']>0 for z in values)
    if max_anchor>=2634:
        target=next(z for z in checks if z['A']==2634)
        assert target['rank_two_semiprimes']==125272
        assert target['prime_supply']==1253703
        assert abs(target['remaining_signed_residual']-(-132.642152))<1e-4
    return dict(max_anchor=max_anchor,dyadic_cases=N,
        wheel_phase_negative_cases=sum(z['signed_wheel_boundary']<0 for z in values),
        deterministic_offset_positive_cases=sum(z['deterministic_offset']>0 for z in values),
        restoration_ratio_min=ratios[0],
        restoration_ratio_median=ratios[N//2],
        restoration_ratio_max=ratios[-1],
        within_two_percent_of_deterministic_offset=sum(abs(z['remaining_signed_residual'])<=0.02*abs(z['deterministic_offset']) for z in values),
        exact_sample_runs=checks)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--max-anchor',type=int,default=1000)
    args=p.parse_args()
    assert args.max_anchor>=317
    print(json.dumps(run(args.max_anchor),indent=2))
