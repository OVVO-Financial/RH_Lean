#!/usr/bin/env python3
"""#915 ACTUAL-prime middle 2q versus original odd-composite donor capacity.

For every current square band (r^2,(r+1)^2), q prime and
r^2 < 2q < (r+1)^2 iff floor(r^2/2) < q <= floor(r^2/2)+r.

This independently tests that the entire REAL middle parent population
fits inside the ORIGINAL positive odd-composite seat population, without
adding any even 2q VF/NNS capacity. The R>=62 proof uses ONLY independent
fixed 30-wheel and 6-wheel bounds. The finite 4..61 cases are audited
explicitly; no RH-scale estimate is being tested/proved here.
"""
import argparse
import bisect
import math
from vf_mid_915_floor_li_transport_regression import prime_sieve

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--extended',action='store_true')
    args=ap.parse_args()
    limit=6000 if args.extended else 1027
    flag,primes=prime_sieve((limit+1)**2)
    pi=lambda n:bisect.bisect_right(primes,n)
    tight=[]
    max_share=(-1,None)
    signed_min=(float('inf'),None)
    near=[]
    def w(r):
        return (2*r+1)/(r*math.log(r*r+r+0.5))
    all_weight={r:w(r) for r in range(2,limit+1)}
    for r in range(4,limit+1):
        curr=pi((r+1)**2)-pi(r*r)
        low=r*r//2
        mid=pi(low+r)-pi(low)
        assert low+r == ((r+1)**2-1)//2
        assert curr + mid <= r, (r,curr,mid)
        assert low+1 > r
        composite_donors=r-curr
        assert mid<=composite_donors
        historical_q=primes[bisect.bisect_right(primes,low):bisect.bisect_right(primes,low+r)]
        # Real signed NEGATIVE historical parent charge, evaluated at
        # the actual native sqrt(q) square band, not its later even child.
        historical_negative=sum(1-all_weight[math.isqrt(q)] for q in historical_q)
        current_positive=w(r)*composite_donors
        signed_margin=current_positive-historical_negative
        if r>=8:
            assert signed_margin > 0, (r, signed_margin)
        if r>=8 and signed_margin < signed_min[0]:
            signed_min=(signed_margin,r)
        if r>=62:
            Ucurr=8*((2*r)//30+1)
            Umid=2*(r//6+1)
            assert curr<=Ucurr and mid<=Umid
            assert Ucurr+Umid<=r
        if mid==composite_donors:
            tight.append(r)
        if r in (4,6,8,18,56,119,317,1027,5266,6000):
            # Independent ORIGINAL physical test, not just R-P by definition.
            count_odd_composite=sum(not flag[n] for n in range(r*r+1,(r+1)**2) if n%2==1)
            assert count_odd_composite==composite_donors
            a=r//2+1
            mids=[q for q in primes[bisect.bisect_right(primes,low):bisect.bisect_right(primes,low+r)]]
            assert all(r*r<2*q<(r+1)**2 and a*a<=q<r*r for q in mids)
            assert len(mids)==mid
            assert mids==historical_q
            print('REAL_OWNER R=%d currentPrimes=%d even2qPrimeParents=%d '
                  'trueOddCompositeDonors=%d surplus=%d halfRunAnchor=%d '
                  'nativePositiveVF=%.9f genuineHistoricalNegativeVF=%.9f '
                  'signedHistoricalCurrentMargin=%.9f '
                  'kernelEnvelope30=%d kernelEnvelope6=%d PASS' %
                  (r,curr,mid,composite_donors,composite_donors-mid,a,
                   current_positive,historical_negative,signed_margin,
                   8*((2*r)//30+1),2*(r//6+1)))
        share=mid / max(1,composite_donors)
        if share>max_share[0]:
            max_share=(share,r)
        if 4<=r<62 and composite_donors-mid<2:
            near.append((r,curr,mid,composite_donors))
    print('PASS actual prime 2q parent count <= original positive odd composite '
          'seat count ALL 4<=R<=%d; 30/6 wheel bound all R>=62.'%limit)
    print('finite exceptions not covered by coarse wheels 4..61: VERIFIED')
    print('NUMERICAL ONLY signed physical charge margin positive at every '
          '8<=R<=%d; minimum (signed margin,R)=%s. '
          'This is NOT the missing all-R arithmetic theorem or hbalance.'
          %(limit,signed_min))
    print('tight R:',tight[:25],'; max occupied donor fraction:',max_share,
          '; near finite:',near[:25])

if __name__=='__main__':
    main()
