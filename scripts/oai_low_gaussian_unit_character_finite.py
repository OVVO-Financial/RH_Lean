#!/usr/bin/env python3
"""Exact CRT and Eisenstein-unit projection on actual OAI completed-row
m-dependent factors. Finite constituent test, not full detector or RH."""
from fractions import Fraction
from math import exp, pi, isqrt
import cmath

P={7:(3,2),13:(2,3),37:(2,10),73:(5,8)}

def sextic(p):
    g,r=P[p]
    logs={pow(g,k,p):k%6 for k in range(p-1)}
    assert len(logs)==p-1
    return [0j]+[cmath.exp(1j*pi*logs[n]/3) for n in range(1,p)]

def gate():
    j=Fraction(21,64)
    eps=Fraction(1,384)
    x=Fraction(17,48)
    y=Fraction(23,48)
    assert 1+eps-x-2*j == -Fraction(1,128)
    assert 1+eps-3*j == Fraction(7,384) < y
    assert j < Fraction(1,3)
    print('PASS exact cubic range J>=Z^(21/64): F/Q<=Z^(-1/128)')

def cases():
    for s,I,J,principal_expected in [
        (37,{37:1},{73:2},True),
        (37,{37:1},{73:1},False),
        (37,{37:1},{37:1},False),
        (37,{73:1},{},False),
        (13,{}, {7:1},False)
    ]:
        e={p:(I.get(p,0)+3*J.get(p,0)-(p==s))%6
           for p in ({s}|set(I)|set(J))}
        h={p:sextic(p) for p in e}
        central=1+0j
        for p,k in e.items():
            local=sum(h[p][r]**k for r in range(1,p))
            if k==0: assert abs(local-(p-1))<1e-7
            else: assert abs(local)<1e-8
            central*=local
        principal=all(k==0 for k in e.values())
        assert principal == principal_expected
        if not principal: assert abs(central)<1e-6
        um=1+0j
        uw=1+0j
        for p,k in e.items():
            um*=h[p][p-1]**k
            uw*=h[p][P[p][1]]**k
        unit_forces_zero=(abs(um-1)>1e-8 or abs(uw-1)>1e-8)
        Q=4096
        L=isqrt(2*Q)+4
        total=0j;absolute=0.
        for a in range(-L,L+1):
            for b in range(-L,L+1):
                n=a*a-a*b+b*b
                if n<=Q*.2 or n>=Q:continue
                t=n/Q
                w=exp(6.25-1/((t-.2)*(1-t)))
                v=w
                for p,k in e.items():
                    v*=h[p][(a+P[p][1]*b)%p]**k
                total+=v
                absolute+=abs(v)
        ratio=abs(total)/absolute
        if principal: assert abs(ratio-1)<1e-9
        if unit_forces_zero: assert ratio<1e-9
        print('PASS s=%d I=%r J=%r CRT_zero=%s unit_zero=%s ratio=%.8g'%
              (s,I,J,not principal,unit_forces_zero,ratio))
if __name__=='__main__':
    gate()
    cases()
