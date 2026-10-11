#!/usr/bin/env python3
"""Critical shared-ancestry overlap sign cutoffs over square roots 2..1000."""
import csv
from math import gcd
import numpy as np
from prime_cutoff_audit import mobius_sieve
from pathlib import Path
D=Path('/mnt/data/prime_cutoff_experiment')
maxR=1000
primes,spf,mu,om,gr,M,Q=mobius_sieve(maxR*maxR-1)
P=np.asarray(primes,dtype=np.int64)
S=np.zeros(maxR,dtype=np.int64)
for d in range(2,maxR):
 if mu[d]==0:continue
 for c in range(2,d):
  if mu[c]!=0 and gcd(c,d)>1:
   S[d]+=mu[c]*mu[d]
S=np.cumsum(S)
res=[]
for R in range(2,maxR+1):
 X=R*R-1
 Psel=P[(P>=R)&(P<=X//2)]
 if not len(Psel):
  res.append(dict(R=R,x=X,ever_positive=False,first_shared_negative=None,last_shared_positive=None,
                  stable_negative_start=None,max_positive_overlap=0,full_overlap=0))
  continue
 kk=X//Psel
 path=np.cumsum(S[kk]);full=int(path[-1])
 pos=(path>0)
 neg=(path<0)
 everpos=bool(np.any(pos))
 firstneg=int(Psel[np.argmax(neg)]) if np.any(neg) else None
 lastpos=int(Psel[len(Psel)-1-np.argmax(pos[::-1])]) if everpos else None
 i_last=np.flatnonzero(pos)[-1] if everpos else -1
 stable_start=int(Psel[i_last+1]) if i_last+1<len(Psel) else None
 res.append(dict(R=R,x=X,ever_positive=everpos,first_shared_negative=firstneg,last_shared_positive=lastpos,
          stable_negative_start=stable_start,max_positive_overlap=int(path.max()),full_overlap=full))
with open(D/'all_square_shared_overlap_cutoffs_2_1000.csv','w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=res[0]);w.writeheader();w.writerows(res)
pos=[r for r in res if r['ever_positive']]
print('square roots with intermediate positive shared overlap',len(pos),'out of',len(res))
print('first ten',pos[:10])
print('last ten',pos[-10:])
print('largest absolute positive intermediate',max(res,key=lambda r:r['max_positive_overlap']))
print('largest ratio stable-start/sqrt(x)',max((r for r in pos if r['stable_negative_start']),key=lambda r:r['stable_negative_start']/r['R']))
