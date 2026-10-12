#!/usr/bin/env python3
"""Independent exact-rational reproduction of native RH_Lean sector six at R=18.

This is *not* a proof of a first-bad RH bound. It computes the literal
lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber carrier and
lowOwnerFirstOwnerDirichletPolarizationAtom at physical clock 18^2-1=323.
The U/L partial masses are defined as positive/negative parts of those *pair
polarization atoms* (not the anchored VF first-bad U/L variables).
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
import math, json

R=18
W=R*R-1

def factor_sqfree(n):
    factors=set(); v=n
    for p in range(2, math.isqrt(v)+2):
        if p*p>v:break
        if v%p==0:
            v//=p; factors.add(p)
            if v%p==0:return None
            while v%p==0:
                v//=p
    if v>1:factors.add(v)
    return frozenset(factors)

facts=[None]*(W+1)
for n in range(1,W+1): facts[n]=factor_sqfree(n)
primes=[n for n in range(2,W+1) if facts[n]==frozenset([n])]
def pop(n):return 1 if len(facts[n])%2==0 else -1

def postroot_common(x,y,w):
    return any(q>math.isqrt(w) for q in facts[x]&facts[y])

def least_parent_equal(x,y):
    f=facts[x]^facts[y]
    if not f:return False
    q=min(f)
    px=x//q if q in facts[x] else x
    py=y//q if q in facts[y] else y
    return px==py

def pol_weight(n):
    # lowOwnerFarTailWeight 18 n + lowOwnerReciprocalDaughterWeight 18 n
    # sole low q^2 daughter q=3, raw cutoff floor(323/9)=35.
    return F(int(n>=R))+ F(int(n<=W//9),3)

def atom(p,x,y):
    # Dirichlet polarization for admitted x,y: mu(x)*mu(y) times
    # negative base-returned products, with full endpoint coefficient.
    return -pop(x)*pop(y)*(pol_weight(x)*pol_weight(p*y)+pol_weight(p*x)*pol_weight(y))

by_sector=defaultdict(lambda:dict(U=F(0),L=F(0),n=0))
fine=defaultdict(lambda:dict(U=F(0),L=F(0),n=0))
ex=[]
for p in primes:
    if p>math.isqrt(W):break
    sigmap=defaultdict(list)
    for n in range(1,W//p+1):
        f=facts[n]
        if f is None or p in f:continue
        sig=tuple(sorted(q for q in f if q<p))
        sigmap[sig].append(n)
    for sig, xs in sigmap.items():
        for i,x in enumerate(xs):
            for y in xs[i+1:]:
                d=facts[x]^facts[y]
                r=max(d)
                assert r>p
                if postroot_common(x,y,W):label=1
                else:
                    a=x//r if r in facts[x] else x
                    b=y//r if r in facts[y] else y
                    low,high=sorted((a,b))
                    if a==b:label=2
                    elif r*high>W:label=3
                    elif postroot_common(low,high,W//r):label=4
                    elif least_parent_equal(low,high):label=5
                    else:label=6
                z=atom(p,x,y)
                leg=by_sector[label]
                leg['U']+=max(z,0)
                leg['L']+=max(-z,0)
                leg['n']+=1
                if label==6:
                    sub=fine[p,sig,r]
                    sub['U']+=max(z,0);sub['L']+=max(-z,0);sub['n']+=1
                    if len(ex)<12:ex.append({'p':p,'sig':sig,'r':r,'x':x,'y':y,'atom':str(z)})

def formatted(d):
    u,l=d['U'],d['L']; den=u+l
    slack=6*u*l-u*u-l*l
    return {'count':d['n'],'U_fraction':str(u),'L_fraction':str(l),
            'U':float(u),'L':float(l),'B_fraction':str(slack),
            'B':float(slack),'ratio_fraction':str((u-l)**2/den**2) if den else '0',
            'ratio':float((u-l)**2/den**2) if den else 0.0,
            'inside_cone':slack>=0}
result={'production_R':R,'clock_W':W,
        'owner_fibers':{str(k):formatted(d) for k,d in sorted(by_sector.items())},
        'total_sector_six':formatted(by_sector[6]),
        'fine_cells':len(fine),
        'unbalanced_fine_cells':sum(not formatted(x)['inside_cone'] for x in fine.values()),
        'example_recursive_pairs':ex}
path='/tmp/vf_mid_sector_six_exact_r18_result.json'
with open(path,'w') as f:json.dump(result,f,indent=2)
print('R=',R,'W=',W)
for k,val in result['owner_fibers'].items():print('sector',k,val)
print('Unbalanced fine child-run cells',result['unbalanced_fine_cells'],'/',result['fine_cells'])
print('Saved',path)
# Regression: native Sector Six cone failure on the exact physical clock.
assert by_sector[6]['n'] == 106
assert by_sector[6]['U'] == F(320, 3)
assert by_sector[6]['L'] == F(46, 3)
assert 6 * by_sector[6]['U'] * by_sector[6]['L'] - by_sector[6]['U'] ** 2 - by_sector[6]['L'] ** 2 == -F(16196,9)
