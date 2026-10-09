#!/usr/bin/env python3
"""#915: terminal top-third Li mismatch and native cofactor/smooth restoration.

Independent primality sieve and largest-prime-factor physical-site census.
The floor-Li smooth reference is a FORMAL complement, not a new sieve set.
No asymptotic or unconditional first-bad estimate is claimed.
"""
import math
from vf_mid_915_floor_li_transport_regression import prime_sieve, li_floor, midpoint_vf

EXPECTED = {
    317: (-26, -24, -41, 6897, 6912, 23240, 23680),
    1027: (-64, -50, -122, 59438, 59496, 250542, 252429),
}

def check(R):
    A, B = R // 2 + 1, R + 1
    X, T = B * B, B * B // 3
    H = X // 2
    pflag, primes = prime_sieve(X)
    count = [0] * (X + 1)
    for n in range(1, X + 1):
        count[n] = count[n - 1] + int(bool(pflag[n]))
    lpf = [0] * (X + 1)
    for q in primes:
        for n in range(q, X + 1, q):
            lpf[n] = q
    E = lambda n: count[n] - li_floor(n)
    EA, ET, EH, EB = E(A*A), E(T), E(H), E(X)
    assert A*A <= T < H and (EA, ET, EB) == EXPECTED[R][:3]
    assert (ET-EA) + (EH-ET) + (EB-EH) == EB-EA
    # Bucket 2b: post-root primes in (X/3,X/2] have exactly
    # one proper full-integer multiple, 2q, which is even.
    # Bucket 3: primes q>X/2 have NO proper integer multiple.
    owner2_only_primes = [q for q in primes if T < q <= H]
    terminal_primes = [q for q in primes if H < q <= X]
    assert all(2*q<=X and 3*q>X for q in owner2_only_primes)
    assert all(2*q>X for q in terminal_primes)
    assert len(owner2_only_primes)==count[H]-count[T]
    assert len(terminal_primes)==count[X]-count[H]
    totals = dict(P=0,F=0,G=0,FL=0,S=0,SL=0,
                  cp=0.0,cg=0.0,cs=0.0,abs_local_g=0.0)
    by_cofactor = {}
    for r in range(A, B):
        w = (2*r+1)/(r*math.log(r*r+r+0.5))
        P = count[(r+1)**2] - count[r*r]
        F = li_floor((r+1)**2) - li_floor(r*r)
        G = FL = 0
        for c in range(3, r+1, 2):
            lo, hi = r*r//c, (r+1)**2//c
            actual = count[hi] - count[lo]
            expected = li_floor(hi) - li_floor(lo)
            G += actual
            FL += expected
            charge = w*(actual-expected)
            by_cofactor[c] = by_cofactor.get(c,0.0) + charge
            totals['abs_local_g'] += abs(charge)
        # Count true sites independently, without quotient prime intervals.
        first = r*r+1
        if first%2 == 0:
            first += 1
        physical = [n for n in range(first,(r+1)**2,2)]
        assert len(physical)==r
        actualG = sum(not pflag[n] and lpf[n] > r for n in physical)
        S = sum(not pflag[n] and lpf[n] <= r for n in physical)
        assert G==actualG and S + G + P == r, (R,r,S,G,P)
        SL = r-F-FL
        deltaP, deltaG, deltaS = P-F,G-FL,S-SL
        assert deltaP+deltaG+deltaS==0
        cp,cg,cs=(w-1)*deltaP,w*deltaG,w*deltaS
        assert abs(cp+cg+cs - (F-P)) < 1e-9
        for k,v in (('P',P),('F',F),('G',G),('FL',FL),('S',S),('SL',SL),
                    ('cp',cp),('cg',cg),('cs',cs)):
            totals[k]+=v

    assert tuple(totals[k] for k in ('P','F','G','FL'))==EXPECTED[R][3:]
    assert totals['P']-totals['F']==EB-EA
    assert abs(totals['cp']+totals['cg']+totals['cs']-(EA-EB)) < 1e-8
    assert abs(totals['cg']-sum(by_cofactor.values())) < 1e-8
    abel_end=abel_variation=0.0
    for c,weighted_error in by_cofactor.items():
        r0=max(A,c)
        def weight(r):
            return (2*r+1)/(r*math.log(r*r+r+0.5))
        end=weight(B)*E(B*B//c)-weight(r0)*E(r0*r0//c)
        variation=sum((weight(r)-weight(r+1))*E((r+1)**2//c)
                      for r in range(r0,B))
        assert abs(end+variation-weighted_error)<1e-8,(R,c)
        abel_end+=end
        abel_variation+=variation
    assert abs(abel_end+abel_variation-totals['cg'])<1e-8
    Ptop=count[X]-count[T]
    Ftop=li_floor(X)-li_floor(T)
    assert Ptop-Ftop==EB-ET
    # Every integer q > floor(X/3) has no odd cofactor c >= 3 in n <= X.
    assert 3*(T+1)>X
    # FULL parity-refined CURRENT clock: split each genuine odd physical
    # w-prime charge into (w/2-prime) and (w/2 at its even mate).
    # The L1 premium must be charged before using ANY even mate as heat.
    w = (2*R+1)/(R*math.log(R*R+R+0.5))
    first = R*R+1
    if first % 2 == 0:
        first += 1
    odds = range(first,(R+1)**2,2)
    P_R = count[(R+1)**2]-count[R*R]
    original_signed = sum(w-int(bool(pflag[n])) for n in odds)
    refined_signed = sum(w/2-int(bool(pflag[n]))+w/2 for n in odds)
    original_abs = sum(abs(w-int(bool(pflag[n]))) for n in odds)
    refined_abs = sum(abs(w/2-int(bool(pflag[n])))+abs(w/2) for n in odds)
    assert abs(original_signed-refined_signed)<1e-9
    assert abs(original_signed-(R*w-P_R))<1e-9
    premium=w*P_R
    assert abs(refined_abs-original_abs-premium)<1e-9
    D_R=count[R*R]-midpoint_vf(R)
    M_original=abs(D_R)+original_abs
    M_refined=abs(D_R)+refined_abs
    price=2*M_original*premium+premium*premium
    assert abs((M_refined*M_refined-M_original*M_original)-price)<1e-7
    assert all(2*q<=X and 2*q%2==0 for q in owner2_only_primes)
    print('PARITY_PRICE R=%d P_R=%d w=%.9f '
          'originalAbs=%.9f refinedAbs=%.9f L1Premium=%.9f '
          'originalM=%.9f squaredCost=%.9f '
          'even2qOriginalVFPayment=0.000000 PASS' %
          (R,P_R,w,original_abs,refined_abs,premium,
           M_original,price))
    print('R=%d A=%d B=%d E(A^2)=%d E(X/3)=%d E(X/2)=%d E(X)=%d '
          'lowerCompositeEligibleMismatch=%+d owner2OnlyMismatch=%+d '
          'noDescendantMismatch=%+d '
          'fullMiddleActualPrimes=%d terminalActualPrimes=%d '
          'topActual=%d topLi=%d '
          'actualP=%d liP=%d actualHighC=%d liHighC=%d '
          'actualSmooth=%d liSmooth=%d '
          'chargePrime=%+.9f chargeHighC=%+.9f chargeSmooth=%+.9f '
          'restored=%+.9f '
          'abelEndpoints=%+.9f abelVariation=%+.9f '
          'cofactorInterCohortRatio=%.6f '
          'absLocalCofactorCharge=%.6f PASS' %
          (R,A,B,EA,ET,EH,EB,ET-EA,EH-ET,EB-EH,
           len(owner2_only_primes),len(terminal_primes),
           Ptop,Ftop,totals['P'],totals['F'],
           totals['G'],totals['FL'],totals['S'],totals['SL'],
           totals['cp'],totals['cg'],totals['cs'],
           totals['cp']+totals['cg']+totals['cs'],
           abel_end,abel_variation,
           abs(totals['cg'])/sum(abs(v) for v in by_cofactor.values()),
           totals['abs_local_g']))

if __name__ == '__main__':
    for R in (317,1027):
        check(R)
