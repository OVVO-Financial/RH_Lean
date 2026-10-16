#!/usr/bin/env python3
"""Integer-only upper certificate for a centered Nyman–Beurling approximation.

For each integer k>=2 let a_k(m)=(m%k)/k. On the step interval
1/(m+1)<x<=1/m the actual function {1/(kx)}-{1/x}/k equals a_k(m).
For coefficients c_k=p_k/Q the exact squared L2(0,1) error is
    sum_(m>=1) [1-sum_k c_k*a_k(m)]**2/(m*(m+1)).
All finite and tail contributions are rounded UP in units 2**-64.
This certifies a finite upper bound, NOT convergence or RH.
"""
from __future__ import annotations
import json
from math import lcm

P = [30381,29554,4202,24930,-17325,20677,-836,3472,
     -13605,14424,-1750,14168,-11155,-8879,8102]
Q = 32768
T = 2_000_000
SCALE = 1 << 64
EXPECTED_PART = 330864155671387940
EXPECTED_TAIL = 479349618301436

def check():
    N=len(P)+1
    L=lcm(*range(2,N+1))
    D=Q*L
    assert N==16 and L==720720
    # D*(1-F(m)) depends only on m modulo L and is an exact integer.
    v=[D]*L
    for k,p in enumerate(P,2):
        t=p*(L//k)
        for r in range(L):
            v[r]-=t*(r%k)
    den2=D*D
    total=0
    for m in range(1,T+1):
        numerator=v[m%L]
        divisor=den2*m*(m+1)
        total+=(SCALE*numerator*numerator+divisor-1)//divisor
    assert total==EXPECTED_PART,(total,EXPECTED_PART)
    # Each atom lies in [0,1), hence |1-F(m)|<=1+sum|c_k|.
    # sum_(m>T) 1/(m(m+1))=1/(T+1), with upward rounding.
    tail_num=(Q+sum(abs(p) for p in P))**2
    tail_den=Q*Q*(T+1)
    tail=(SCALE*tail_num+tail_den-1)//tail_den
    assert tail==EXPECTED_TAIL,(tail,EXPECTED_TAIL)
    upper=total+tail
    assert 500*upper<9*SCALE,(upper,SCALE)
    return dict(N=N,T=T,coefficients_numerators=P,coefficients_denominator=Q,
                scaled_partial_upper=total,scaled_tail_upper=tail,
                scaled_total_upper=upper,scale=SCALE,
                exact_conclusion="d_16^2 < 9/500 (finite only)")

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
