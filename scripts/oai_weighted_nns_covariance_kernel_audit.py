#!/usr/bin/env python3
"""Exact finite NNS zero-target Gram test on RH_Lean's genuine ideal sextic phases.

Phase lists are the four existing 317/1027 native ideal witnesses.
Derivative-log coefficients and W below are ILLUSTRATIVE: not the full OAI
actual marked F.rows. Tests the source-preserving algebra needed for their
eventual formal substitution, not an asymptotic analytic estimate.
"""
import cmath
import math

SEXTIC=[cmath.exp(2j*math.pi*r/6) for r in range(6)]
PHASES={"x317":(5,5,1,1),"x1027":(1,3,3,5),
        "R317":(0,4,2,0),"R1027":(3,1,5,3)}
LOGS=[math.log(z) for z in (3,5,7,11)]
def p(t): return (abs(t)+t)/2
def n(t): return (abs(t)-t)/2
def co(a,b): return p(a)*p(b)+n(a)*n(b)
def dv(a,b): return p(a)*n(b)+n(a)*p(b)
def phi(z): return z.real-z.imag,z.real+z.imag
def close(a,b):
    assert math.isclose(a,b,rel_tol=1e-9,abs_tol=1e-8), (a,b)

def gram(atoms):
    vs=[phi(z) for z in atoms]
    D=sum((x*x+y*y)/2 for x,y in vs)
    C=sum((co(x,r)+co(y,s))/2 for x,y in vs for r,s in vs)
    V=sum((dv(x,r)+dv(y,s))/2 for x,y in vs for r,s in vs)
    direct=abs(sum(atoms))**2
    close(C-V,direct)
    close(D+(C-D)-V,direct)
    assert C+1e-8>=D and V>=-1e-8
    return direct,D,C-D,V

for j,k in ((0,0),(0,1),(1,0),(1,1),(0,2),(2,0)):
    original=diag=co_off=div=0.
    for h,(name,exps) in enumerate(PHASES.items()):
        z=[SEXTIC[e] for e in exps]
        pj=[a*L**j for a,L in zip(z,LOGS)]
        pk=[a*L**k for a,L in zip(z,LOGS)]
        # Literal convolution-before-norm atom array, with ALL (i,l) labels.
        b=[a*c for a in pj for c in pk]
        assert len(b)==16
        W2=1 if j==k==0 else 1/((h+2)**2)
        E,D,C,V=gram(b)
        close(E,abs(sum(pj)*sum(pk))**2)
        original+=W2*E;diag+=W2*D;co_off+=W2*C;div+=W2*V
    close(original,diag+co_off-div)
    print(f"j={j} k={k}: marked={original:.9f} diagonal={diag:.9f} "
          f"co_off={co_off:.9f} divergent={div:.9f} "
          f"signed_payment={div-co_off:.9f}")
    if j==k==0:
        close(original,19)
        close(diag,64)
        close(div-co_off,45)

# Euler subtraction A-B: NNS favorably oriented pairing appears with MINUS.
for phase in SEXTIC:
    a=2-.3j
    b=(1+.2j)*phase
    ax,ay=phi(a);bx,by=phi(b)
    D=(ax*ax+ay*ay+bx*bx+by*by)/2
    aligned=co(ax,bx)+co(ay,by)-dv(ax,bx)-dv(ay,by)
    close(abs(a-b)**2,D-aligned)

# Complete character phase averaging does not supply new energy saving.
for a,b in ((1+0j,1+0j),(2-3j,.5+1.5j)):
    avg=sum(abs(a-t*b)**2 for t in SEXTIC)/6
    close(avg,abs(a)**2+abs(b)**2)
print("PASS: original-weight NNS Gram=diagonal+co_off-div; "
      "all 6 j/k pairs, genuine 317/1027 sextic labels, Euler subtraction")
