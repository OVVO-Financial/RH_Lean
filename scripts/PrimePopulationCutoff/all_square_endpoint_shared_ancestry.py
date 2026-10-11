#!/usr/bin/env python3
"""All-square-endpoint exact signed gcd ancestry census, R=2..1000.

The shared/coprime quadratic Gram entries are restricted to genuine post-root
prime extensions. All integer summands and identities are exact.
"""
import csv
import numpy as np
from math import gcd,sqrt
from pathlib import Path
from prime_cutoff_audit import mobius_sieve

NROOT=1000
DIR=Path('/mnt/data/prime_cutoff_experiment')
ps,spf,mu,om,gr,M,Q=mobius_sieve(NROOT*NROOT-1)
P=np.asarray(ps,dtype=np.int64)
a=np.zeros(NROOT,dtype=np.int64)
b=np.zeros(NROOT,dtype=np.int64)
d=np.zeros(NROOT,dtype=np.int64)
for j in range(2,NROOT):
    if not mu[j]: continue
    d[j]=1
    for i in range(2,j):
        if not mu[i]: continue
        z=mu[i]*mu[j]
        if gcd(i,j)>1: a[j]+=z
        else: b[j]+=z
A=np.cumsum(a);B=np.cumsum(b);D=np.cumsum(d)
for k in range(2,NROOT):
    assert D[k]+2*(A[k]+B[k])==(M[k]-1)**2
records=[]
for R in range(2,NROOT+1):
    X=R*R-1
    alive=P[(P>=R)&(P<=X//2)]
    k=X//alive
    sa=int(A[k].sum());sb=int(B[k].sum());dd=int(D[k].sum())
    diag_expected=int(np.sum([(M[int(u)]-1)**2 for u in k],dtype=np.int64))
    assert dd+2*(sa+sb)==diag_expected
    delta=int(np.sum(2*(1-np.array([M[int(u)] for u in k],dtype=np.int64)),dtype=np.int64))
    nneg=sum(M[int(u)]>1 for u in k)
    K=max((M[y]-1)**2/(y+1) for y in range(R))
    QR=2*M[R-1]-M[X]
    records.append(dict(R=R,X=X,n_active=int(len(alive)),shared=sa,coprime=sb,diagonal=dd,
             total_prime_update_energy=diag_expected,total_postroot_update=delta,
             postroot_negative_steps=nneg,M=M[X],Q=QR,K=K,C=abs(QR)/(R*sqrt(K)),Aend=(M[X]-1)**2/(R*R*K)))
with open(DIR/'all_square_roots_2_1000.csv','w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=records[0].keys());w.writeheader();w.writerows(records)
pos=[r for r in records if r['shared']>0]
neg=[r for r in records if r['shared']<0]
zero=[r for r in records if r['shared']==0]
flips=[r for r in records if r['postroot_negative_steps']>0]
print('all roots',len(records),'shared negative',len(neg),'positive',len(pos),'zero',len(zero))
print('positive shared roots',[(r['R'],r['shared']) for r in pos[:65]])
print('last positive shared root',pos[-1]['R'] if pos else None)
print('first negative postroot square R',flips[0]['R'] if flips else None,'details',flips[0]['postroot_negative_steps'] if flips else None)
print('negative update cases',len(flips))
print('min/max shared',min(records,key=lambda z:z['shared'])['shared'], max(records,key=lambda z:z['shared'])['shared'])
print('max C after root20',max((r for r in records if r['R']>=20),key=lambda z:z['C']))
for R in [17,18,32,33,56,95,96,97,100,317,500,1000]:
    r=records[R-2]
    print('R',R,'X',r['X'],'shared',r['shared'],'coprime',r['coprime'],'neg_update',r['postroot_negative_steps'],'C',r['C'])
