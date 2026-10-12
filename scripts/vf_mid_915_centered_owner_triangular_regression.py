#!/usr/bin/env python3
"""#915: exact original-seat centered first-owner triangular Fubini.

Arithmetic is ACTUAL integer divisibility/prime membership; no heuristic PNT.
The entire current odd VF signed field is reconstructed SITE BY SITE by
reference product + predictable centered owner's survivor deviations.
The full off-diagonal owner Gram reduces to linear later-owner discrepancies.

CRITICAL: original D_R anchored history remains one compressed scalar.
This test does NOT establish hbalance; cross-owner contributions can have
BOTH signs on ordinary square blocks.
"""
from __future__ import annotations

import math
from bisect import bisect_right


def sieve(N):
    prime=bytearray(b"\x01")*(N+1)
    prime[:2]=b"\x00\x00"
    for q in range(2,math.isqrt(N)+1):
        if prime[q]:
            prime[q*q:N+1:q]=b"\x00"*((N-q*q)//q+1)
    return prime,[n for n in range(2,N+1) if prime[n]]


def scan(R, prime, primes, *, verbose=True):
    owners=[p for p in primes if 2<p<=R]
    m=len(owners)
    alpha=1.
    for p in owners:
        alpha*=1-1/p
    beta=[0.]*m
    suffix=1.
    for i in range(m-1,-1,-1):
        beta[i]=suffix
        suffix*=1-1/owners[i]
    w=(2*R+1)/(R*math.log(R*R+R+.5))
    center=w-alpha
    xi=[0.]*m
    survivors=[0]*m
    diag_actual=0.
    cross_actual=0.
    center_mixed=0.
    source_actual=0.
    signed_total=0.
    count_primes=0
    maxerr=0.

    for n in range(R*R+1,(R+1)**2):
        if n%2==0:
            continue
        s=1
        g=[]
        for i,p in enumerate(owners):
            deviation=s*(int(n%p==0)-1/p)
            survivors[i]+=s
            xi[i]+=deviation
            g.append(deviation)
            s*=int(n%p!=0)
        pn=int(bool(prime[n]))
        count_primes+=pn
        # All current prime seats survive the full low-prime wheel;
        # all composites in the open square block are removed.
        assert s==pn,(R,n,s,pn)
        z=center+sum(beta[i]*g[i] for i in range(m))
        physical=w-pn
        maxerr=max(maxerr,abs(z-physical))
        assert abs(z-physical)<4e-12,(R,n,z,physical)
        source_actual+=physical
        signed_total+=z
        center_mixed+=center**2+2*center*sum(beta[i]*g[i] for i in range(m))
        pref=0.
        for j in range(m):
            term=beta[j]*g[j]
            diag_actual+=term*term
            cross_actual+=2*term*pref
            pref+=term

    expected_diag=sum(
        beta[i]**2*((1-2/p)*xi[i]+(p-1)/p**2*survivors[i])
        for i,p in enumerate(owners))
    prefix=0.
    expected_cross=0.
    for i,p in enumerate(owners):
        expected_cross+=-2*beta[i]*xi[i]*prefix
        prefix+=beta[i]/p
    tolerance=lambda x:max(1e-7,abs(x)*1e-8)
    assert abs(diag_actual-expected_diag)<tolerance(expected_diag)
    assert abs(cross_actual-expected_cross)<tolerance(expected_cross)
    assert abs(source_actual-signed_total)<tolerance(source_actual)
    assert abs(source_actual-(R*w-count_primes))<tolerance(source_actual)

    exact_diag=sum((w-int(bool(prime[n])))**2 for n in
        range(R*R+1,(R+1)**2) if n%2)
    assert abs(exact_diag-(center_mixed+expected_diag+expected_cross))<tolerance(exact_diag)

    VF=sum((2*r+1)/math.log(r*r+r+.5) for r in range(2,R))
    D=bisect_right(primes,R*R)-VF
    U=max(-D,0)+w*(R-count_primes)
    L=max(D,0)+(1-w)*count_primes
    slack=6*U*L-U*U-L*L
    if verbose:
        print("CENTERED_OWNER R=%d owners=%d primeSupply=%d alpha=%.9f "
              "correction=%+.6f diagonal=%+.6f cross=%+.6f "
              "actualSumSquares=%.6f originalD=%.6f originalSlack=%.6f "
              "maxSeatError=%.2g PASS"%
              (R,m,count_primes,alpha,sum(beta[i]*xi[i] for i in range(m)),
               expected_diag,expected_cross,exact_diag,D,slack,maxerr))
    return expected_cross,slack


def main():
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("--extended",action="store_true")
    args=p.parse_args()
    endpoints=[8,18,56,79,119,317,1027,2000]
    if args.extended:
        endpoints+=[6000]
    M=max(endpoints)
    prime,primes=sieve((M+1)**2)
    pos=neg=0
    extrema=[(0,0.),(0,0.)]
    # Consecutive scan explicitly tests whether the triangular offdiagonal
    # is SIGN-DEFINITE: it is not, and no new sign claim may be inferred.
    for R in range(8,301):
        x,_=scan(R,prime,primes,verbose=False)
        if x>1e-7:
            pos+=1
            if x>extrema[0][1]:extrema[0]=(R,x)
        elif x< -1e-7:
            neg+=1
            if x<extrema[1][1]:extrema[1]=(R,x)
    assert pos>0 and neg>0
    print("SIGN_AUDIT R=8..300 positive=%d negative=%d "
          "maxPositive=(%d,%.6f) maxNegative=(%d,%.6f) PASS"%
          (pos,neg,*extrema[0],*extrema[1]))
    for R in endpoints:scan(R,prime,primes)
    print("PASS original VF seat+Gram centered-owner identities")
    print("OPEN first-bad signed control of accumulated owner deviations")


if __name__=="__main__":
    main()
