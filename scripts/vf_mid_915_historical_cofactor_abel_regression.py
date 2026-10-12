#!/usr/bin/env python3
"""#915 complete historical cofactor-first sqrt(x) prime-fiber Abel regression.

Every actual historical composite site n=c*q with q>floor(sqrt n)
PRIME, odd c>=3, and block a<=r<=R is counted ONCE. Fixed c now spans
one BROAD interval (r0(c)^2/c, (R+1)^2/c] for r0(c)=max(a,c).
A prime cannot sit exactly on the square quotient face, so there are no
missing ACTUAL prime atoms when blocks are telescoped.

Discrete Li DOES sometimes jump at such square-quotient faces. Use the
CLOSED-quotient cofactor Li reference, which telescopes exactly; its
nonphysical endpoint events remain in the true signed mismatch stream,
not in invented actual prime seats.

The historical site has its own original VF weight w_r. Exact weighted
Abel moves all PRIME-minus-Li history into endpoint backlogs plus smooth
native w_r-w_(r+1) differences. No previous historical NNS abs capacity
is introduced or available as independent spending.
"""
import argparse
import math
from bisect import bisect_right
from vf_mid_915_floor_li_transport_regression import (
    li_floor, prime_sieve, block_weight
)


def run(R,prime,primes):
    a=R//2+1
    B=R+1
    X=B*B-1
    seen=set()
    total_actual=0
    weight_original=0.0
    samples=(3,5,7,9,11,13,17,101,317)
    for c in range(3,R+1,2):
        r0=max(a,c)
        if r0>=B: continue
        low=r0*r0//c
        hi=B*B//c
        actual=bisect_right(primes,hi)-bisect_right(primes,low)
        blockTotal=0
        weight_c=0.0
        for r in range(r0,B):
            lo_r=r*r//c
            hi_r=(r+1)*(r+1)//c
            t=bisect_right(primes,hi_r)-bisect_right(primes,lo_r)
            blockTotal+=t
            weight_c+=block_weight(r)*t
            # Actual prime atoms never fall on the quotient-square face;
            # Li jump atoms MAY, and remain in the deterministic reference.
            nUpper=((r+1)*(r+1)-1)//c
            if nUpper<hi_r:
                assert not (primes[bisect_right(primes,nUpper):bisect_right(primes,hi_r)]), (R,c,r,hi_r)
        assert blockTotal==actual,(R,c,blockTotal,actual)
        total_actual+=actual
        weight_original+=weight_c
        # Independent occurrence reassembly through genuine q primes
        # and actual physical n=cq, verifying unique super-root prime owner.
        for q in primes[bisect_right(primes,low):bisect_right(primes,hi)]:
            n=c*q
            r=math.isqrt(n)
            assert r0<=r<B and r*r<n<(r+1)*(r+1),(R,c,q,n,r)
            assert q>r and c<=r
            assert n not in seen,(R,n,c,q)
            seen.add(n)
            assert not prime[n],(R,n)
        if c in samples:
            floor_total=li_floor(hi)-li_floor(low)
            # Exact in signed mismatch currency, WITH literal native VF
            # scalar retained through every historical square block.
            weighted_li=weighted_err=variation=0.0
            for r in range(r0,B):
                lo_r=r*r//c;hi_r=(r+1)*(r+1)//c
                E0=bisect_right(primes,lo_r)-li_floor(lo_r)
                E1=bisect_right(primes,hi_r)-li_floor(hi_r)
                w0=block_weight(r)
                weighted_err+=w0*(E1-E0)
                weighted_li+=w0*(li_floor(hi_r)-li_floor(lo_r))
                variation+=(w0-block_weight(r+1))*E1
            EB=bisect_right(primes,hi)-li_floor(hi)
            EA=bisect_right(primes,low)-li_floor(low)
            rhs=block_weight(B)*EB-block_weight(r0)*EA+variation
            assert abs(weighted_err-rhs)<4e-7,(R,c,weighted_err,rhs)
            assert abs(weight_c-(weighted_li+weighted_err))<4e-7,(R,c)
            print("HISTORY_FIBER R=%d c=%d r0=%d qWindow=(%d,%d] "
                  "actual=%d floorLi=%d Ehi-Elo=%+d "
                  "nativeVF=%.6f signedWeightedError=%+.6f "
                  "AbelBoundary=%.6f AbelVariation=%.6f PASS"
                  %(R,c,r0,low,hi,actual,floor_total,actual-floor_total,
                    weight_c,weighted_err,
                    block_weight(B)*EB-block_weight(r0)*EA,variation))
    assert len(seen)==total_actual
    print("HISTORY_FIBER_SUM R=%d a=%d qgtNativeRootComposites=%d "
          "literalVFWeightedCharge=%.9f allPhysicalSitesDistinct=YES PASS"
          %(R,a,total_actual,weight_original))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--extended",action="store_true")
    args=parser.parse_args()
    roots=[317,1027]
    if args.extended:
        roots=[56,317,1027]
    prime,primes=prime_sieve((max(roots)+1)**2)
    for R in roots:
        run(R,prime,primes)
    print("PASS cofactor-first history Fubini, absent prime square faces, and exact native-weight Abel transport")
    print("OPEN quantitative signed historical cofactor-boundary restriction for production #915")


if __name__=="__main__":
    main()
