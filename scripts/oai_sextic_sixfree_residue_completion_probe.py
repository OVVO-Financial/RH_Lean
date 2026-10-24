#!/usr/bin/env python3
"""True Eisenstein primitive sextic row cancellation with sixth-free ideal masks.

This is a FINITE regression for the complete primary/radial character carrier.
It is NOT the full compensated physical OAI source, detector, or a proof.
"""
import cmath
import math
from fractions import Fraction as F

PRIMES = ((7, 3, 4), (13, 2, 9), (19, 2, 7))

def norm(a, b):
    return a*a-a*b+b*b

def mul(z, w):
    a,b=z
    c,d=w
    return (a*c-b*d, a*d+b*c-b*d)

def sixth_power(z):
    value=(1,0)
    for _ in range(6):
        value=mul(value,z)
    return value

def sixth_divisors(U):
    limit=int(round(U**(1/6)))+2
    B=math.isqrt(2*limit)+2
    return tuple({sixth_power((a,b))
        for a in range(-B,B+1)
        for b in range(-B,B+1)
        if norm(a,b)>1 and norm(a,b)**6<=U})

def divides_ideal_generator(d,a,b):
    x,y=d
    N=norm(x,y)
    if N==0:
        return False
    c,e=mul((a,b),(x-y,-y))
    return c%N==0 and e%N==0

def sextic_log_table(p,g,omega):
    assert (omega*omega+omega+1)%p==0
    logs={pow(g,k,p):k%6 for k in range(p-1)}
    assert len(logs)==p-1
    return logs

def verify_complete_primary_residue_tile(p,g,omega):
    logs=sextic_log_table(p,g,omega)
    L=3*p
    bins=[0]*7
    for a in range(1,L,3):
        for b in range(0,L,3):
            val=(a+omega*b)%p
            bins[6 if val==0 else logs[val]]+=1
    assert len(set(bins[:6]))==1
    assert bins[:6]==[(p-1)*p//6]*6, (p,bins)
    assert bins[6]==p
    return bins

def physical_primary_sixthfree_probe(p,g,omega,U):
    logs=sextic_log_table(p,g,omega)
    divisors=sixth_divisors(U)
    root=[cmath.exp(2j*math.pi*k/6) for k in range(6)]
    B=math.isqrt(2*U)+2
    signed=0j
    total=0.
    count=0
    for a in range(-B,B+1):
        if a%3!=1:
            continue
        for b in range(-B,B+1):
            if b%3:
                continue
            N=norm(a,b)
            if not(0<N<=U):
                continue
            t=N/U
            if not(.2<t<1):
                continue
            if any(divides_ideal_generator(d,a,b) for d in divisors):
                continue
            residue=(a+omega*b)%p
            if residue==0:
                continue
            W=(t-.2)**2*(1-t)**2
            signed+=W*root[logs[residue]]
            total+=W
            count+=1
    return count,abs(signed)/total

for p,g,omega in PRIMES:
    bins=verify_complete_primary_residue_tile(p,g,omega)
    print("TRUE sextic complete-period OAI residue:",p,bins)
    for U in (2048,8192,32768,131072):
        count,ratio=physical_primary_sixthfree_probe(p,g,omega,U)
        assert count>0 and ratio<0.01,(p,U,count,ratio)
        print("p=",p,"U=",U,"sixthfree=",count,"signed/absolute=",round(ratio,8))

# Arithmetic savings: U=Z^(13/16), q=Z^(1/6);
# actual complete tile method gives q*sqrt(U)+q^2*U^(1/6).
raw=F(13,16)
tile=F(1,6)+F(13,32)
sixth=F(1,3)+F(13,96)
assert tile==F(55,96) and sixth==F(45,96)
assert raw-tile==F(23,96)>F(1,8)
assert raw-sixth==F(33,96)>F(1,8)
print("PASS signed PRIMARY SIXTH-FREE character completion: saving",raw-tile,
      "versus required 1/8; does not certify full OAI physical source.")
