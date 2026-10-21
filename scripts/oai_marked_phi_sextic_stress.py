#!/usr/bin/env python3
"""Finite exact-formula stress for the OAI marked-row real-NNS bridge.

Sixth-root phases below are genuine unit sixth roots, NOT OpenAI's full
Hecke ideal-labelled source. This checks all allowed derivative cases,
realification, quadrants, and an obstruction to phase-only power savings.
"""
import cmath
import math
from fractions import Fraction

zeta = [cmath.exp(2j*math.pi*r/6) for r in range(6)]
def phi(z): return z.real-z.imag, z.real+z.imag
def e(z):
    x,y=phi(z)
    return (x*x+y*y)/2
def pos(t): return max(t,0.)
def neg(t): return max(-t,0.)
def quartic(z):
    x,y=phi(z)
    marginals=pos(x)**4+neg(x)**4+pos(y)**4+neg(y)**4
    mixed=sum(a*a*b*b for a in (pos(x),neg(x))
              for b in (pos(y),neg(y)))
    return (marginals+2*mixed)/4
def near(a,b): return math.isclose(a,b,rel_tol=1e-10,abs_tol=1e-9)

for z in zeta+[2-3j,-.3+4.1j,0j]:
    assert near(e(z),abs(z)**2)
    assert near(quartic(z),abs(z)**4)
for j,k in ((0,0),(0,1),(1,0),(1,1),(2,0),(0,2)):
    original=0.
    nns=0.
    for i in range(1,79):
        v=zeta[(i*i+i)%6]
        base=(1+i/37)*v+(0.2+0.1j)*zeta[(i+1)%6]
        pj=base*complex(math.log1p(i),0.03*i)**j
        pk=base*complex(math.log1p(i),0.03*i)**k
        # Explicit selected-slot test mask; NOT OAI's actual source mask.
        physical=(0 if i%11==0 else zeta[i%6]/(1+i%8))
        original+=abs(pj*pk*physical)**2
        nns+=e(pj)*e(pk)*e(physical)
    assert near(original,nns),(j,k,original,nns)
    print(f'j={j} k={k} selected_weighted_moment={original:.10f} = realNNS')

# Pure sextic phases alone do not force favourable marked/rescaled alignment.
compensated=[abs(1-z)**4 for z in zeta]
A=2
C=[2*z.real for z in zeta]
baseline=[A*A+c*c for c in C]
good=sum(A*pos(c) for c in C)
bad=sum(A*neg(c) for c in C)
assert near(sum(compensated),36.)
assert near(sum(baseline),36.)
assert near(good,bad)
print('sixth_roots |1-zeta|^4:', ','.join(str(round(v)) for v in compensated))
print(f'baseline_sum={sum(baseline):.0f}; actual_sum={sum(compensated):.0f};'
      f' positive_alignment={good:.2f}; negative_alignment={bad:.2f}')

# Four genuine Eisenstein ideal-labelled finite phase families ALREADY proved
# in RHLean's VF_919_NATIVE_SEXTIC_OWNER_PROJECTION_20261019.lean.
# This is finite tagged ideal arithmetic, not an OAI global row family.
native_witnesses=(
    ('x317', (5,5,1,1), 2, -2),
    ('x1027', (1,3,3,5), -1, 1),
    ('R317', (0,4,2,0), 1, -1),
    ('R1027',(3,1,5,3), -1, 1),
)
total_actual_quartic=0.
total_norm_first_quartic=0.
for name,exps,expected,expected_selected in native_witnesses:
    actual=sum(zeta[e] for e in exps)
    selected=sum(-zeta[(-e)%6] for e in exps)
    assert near(actual.real,expected) and near(actual.imag,0)
    assert near(selected.real,expected_selected) and near(selected.imag,0)
    assert near(quartic(actual),abs(actual)**4)
    assert near(quartic(selected),abs(selected)**4)
    total_actual_quartic+=quartic(actual)
    total_norm_first_quartic+=len(exps)**4
    print(f'native_ideal_phase_{name}: labels={exps}, signed={expected}, '
          f'selected={expected_selected}, fourth={quartic(actual):.0f}, '
          f'positive_before_phase={len(exps)**4}')
assert near(total_actual_quartic,19.)
assert near(total_norm_first_quartic,1024.)
print(f'FOUR native phase witnesses: signed fourth sum={total_actual_quartic:.0f}, '
      f'norm-first quartic sum={total_norm_first_quartic:.0f}, '
      f'finite ratio={total_norm_first_quartic/total_actual_quartic:.4f}')

# PRE-NORM negative directional mixed-quadrant ledger for the four TRUE
# native Eisenstein ideal-labelled phases (not a population estimate).
total_K2=total_KP=total_KN=total_Q=0.
for name,exps,expected,expected_selected in native_witnesses:
    atoms=[zeta[q] for q in exps]
    K=sum(abs(a)**2 for a in atoms)
    grams=[(atoms[i]*atoms[j].conjugate()).real
           for i in range(len(atoms)) for j in range(i+1,len(atoms))]
    P=sum(pos(g) for g in grams)
    N=sum(neg(g) for g in grams)
    E=abs(sum(atoms))**2
    assert near(E,K+2*(P-N))
    assert near(E*E,K*K+4*K*P-4*K*N+4*(P-N)**2)
    total_K2+=K*K; total_KP+=4*K*P
    total_KN+=4*K*N;total_Q+=4*(P-N)**2
    print(f'signed_NNS_{name}: K={K:.5g} P={P:.5g} N={N:.5g} fourth={E*E:.5g}')
assert near(total_K2,64.) and near(total_KP,80.)
assert near(total_KN,152.) and near(total_Q,27.)
assert near(total_K2+total_KP-total_KN+total_Q,19.)
print('signed NNS 317/1027 ledger: 19 = 64 + 80 - 152 + 27')

# The actual mixed derivative M4 must polarize P_j and P_k separately,
# not take a fourth power of the entire product.
for j,k in ((0,0),(0,1),(1,0),(0,2),(2,0),(1,1)):
    for _,exps,_,_ in native_witnesses:
        lognorm=[math.log(13+i*7) for i in range(4)]
        per=[]
        for degree in (j,k):
            atoms=[zeta[q]*lognorm[i]**degree for i,q in enumerate(exps)]
            g=[(atoms[i]*atoms[h].conjugate()).real
               for i in range(4) for h in range(i+1,4)]
            per.append((sum(abs(z)**2 for z in atoms),
                        sum(pos(v) for v in g),sum(neg(v) for v in g),
                        abs(sum(atoms))**2))
        Kj,Pj,Nj,Ej=per[0]
        Kk,Pk,Nk,Ek=per[1]
        pol=Kj*Kk+2*(Kj*Pk+Kk*Pj)-2*(Kj*Nk+Kk*Nj)+4*(Pj-Nj)*(Pk-Nk)
        assert near(pol,Ej*Ek),(j,k,pol,Ej*Ek)
print('PASS: six j+k<=2 mixed fourth degree polarized NNS identities')

# Equal physical weights paired at a prime do NOT cancel if the character
# phase at that prime is -1. Preserve phase before the character transform.
for phase in (-1,1,cmath.exp(2j*math.pi/3)):
    a0=a1=1+0j
    assert near(abs(a0-phase*a1),
                abs((a0-a1)+(1-phase)*a1))
assert near(abs(1-(-1)*1),2)

# Exact logarithmic discrete Leibniz remainders at degrees 0,1,2.
for j in range(3):
    a0,a1,phase=1.2-0.3j,0.7+0.6j,zeta[1]
    x,l=4.2,1.3
    direct=a0*x**j-phase*a1*(x+l)**j
    leak=sum(math.comb(j,r)*x**r*l**(j-r) for r in range(j))
    paired=(a0-phase*a1)*x**j-phase*a1*leak
    assert near(abs(direct-paired),0.)
print('PASS: phase-correct Euler toggling and j=0,1,2 log leakage')

# A positive *resonant term* need not lower bound fourth moment over
# restricted character rows. Trivial character, source +1 at 1, -1 at p.
trivial_amplitude=1-1
resonant_convolution_energy=1**2+(-2)**2+1**2
assert trivial_amplitude**4==0 and resonant_convolution_energy==6
print('restricted trivial-row fourth=0; equal-ideal resonant energy=6; nonres=-6')

for t in (Fraction(1,100000),Fraction(1,10000),Fraction(1,4)):
    assert 1+t/4+t/4==1+t/2
    assert 1+t/2<1+t
    print('width',str(t),'retained_exponent',str(1+t/2),
          'published_exponent',str(1+t),'slack',str(t/2))
print('PASS: exact real NNS row, fourth-order quadrants, sixth-phase obstruction, OAI width slack')
