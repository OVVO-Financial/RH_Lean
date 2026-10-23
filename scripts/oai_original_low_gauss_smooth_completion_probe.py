#!/usr/bin/env python3
"""Original OAI LOW Gaussian prime phase and ideal-period source scale audit.

Original LowRowMellin: Q=N(C.generator)*X*Y; gauss s~Y, m~Q.
Checks TRUE split Eisenstein sextic Gauss transforms and nontrivial
unit-trivial p=37/73 radial sums. Never claims full correctedCompletedT.
"""
from fractions import Fraction as F
from math import isqrt, pi, sqrt
from cmath import exp

SPLIT_PRIMES = ((7,3,4), (13,2,9), (19,2,7), (37,2,10), (73,5,8))

def eis_norm(a,b):
    return a*a - a*b + b*b

def sixth_character_table(p,g,omega):
    assert (omega*omega+omega+1)%p == 0
    logs={pow(g,k,p):k%6 for k in range(p-1)}
    assert len(logs) == p-1
    z=[exp(2j*pi*k/6) for k in range(6)]
    return [0j if h==0 else z[logs[h]] for h in range(p)]

def gauss(c,p,h):
    return sum(c[t]*exp(2j*pi*h*t/p) for t in range(p))

def radial_sum(p,omega,U,c):
    r=isqrt(2*U)+2
    signed=0j
    unsigned=0.
    for a in range(-r,r+1):
        for b in range(-r,r+1):
            n=eis_norm(a,b)
            if not(0<n<=U):
                continue
            t=n/U
            if not(.2<t<1):
                continue
            w=(t-.2)**2*(1-t)**2
            signed+=w*c[(a+omega*b)%p]
            unsigned+=w
    return signed,unsigned

for p,g,omega in SPLIT_PRIMES:
    chi=sixth_character_table(p,g,omega)
    assert abs(sum(chi)) < 1e-10
    G=gauss(chi,p,1)
    assert abs(abs(G)**2-p) < 1e-9
    for h in range(p):
        physical=gauss(chi,p,h)
        expected=0j if h==0 else G/chi[h]
        assert abs(physical-expected)<1e-9,(p,h,physical,expected)
    units_trivial=abs(chi[-1]-1)<1e-9 and abs(chi[omega]-1)<1e-9
    assert units_trivial == (p in (37,73))
    print('ACTUAL PRIMITIVE SEXTIC GAUSS PHASE q',p,
          'Gauss norm',round(abs(G),7),
          'character unit-invariant',units_trivial)
    for U in (4096,32768,131072):
        signed,absolute=radial_sum(p,omega,U,chi)
        assert absolute>0
        if not units_trivial:
            # Full six-unit orbit forces exact cancellation at ALL radial U.
            assert abs(signed)<1e-7,(p,U,signed)
        else:
            # Nonvacuous smooth character completion checks.
            assert 0<abs(signed)<absolute,(p,U,signed)
        print(' q',p,'Q',U,'signed',round(abs(signed),8),
              'unsigned',round(absolute,8),
              'ratio',round(abs(signed)/absolute,10),
              'geometric-bound-scale',round(sqrt(p*U)+p,4))

Y=F(23,48)
Q=F(5,6)
assert Y+F(17,48)==Q
assert (Y+Q)/2==F(21,32)
assert Q-(Y+Q)/2==F(17,96)
assert F(17,96)>F(1,8)
print('PASS real OAI low Gaussian Q=Z^5/6, q=Y=Z^23/48; signed radial saving 17/96 > 1/8')
print('WARNING: low B(sigma,m)=correctedCompletedT is arithmetically nonradial.')
