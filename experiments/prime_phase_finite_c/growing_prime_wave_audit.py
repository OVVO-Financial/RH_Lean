#!/usr/bin/env python3
"""Additional test: let prime frequencies grow with square-root R (p<=R)."""
import numpy as np, json,os
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.stats import pearsonr,spearmanr
O=os.path.dirname(__file__)
data=np.genfromtxt(O+'/actual_root_scan.csv',delimiter=',',names=True)
R=data['R'].astype(np.int64)
Rmax=int(R.max())
isprime=np.ones(Rmax+1,dtype=bool);isprime[:2]=False
for p in range(2,int(Rmax**.5)+1):
 if isprime[p]:isprime[p*p::p]=False
primes=np.flatnonzero(isprime)
Y=np.zeros(len(R),dtype=float);Yw=np.zeros(len(R),dtype=float);m=np.zeros(len(R),dtype=int)
for p in primes:
 ids=R>=p
 rs=R[ids]
 local=np.sin(2*np.pi*((rs*rs-1)%p)/p)
 Y[ids]+=local
 Yw[ids]+=local/p
 m[ids]+=1
idx=R>=31
C=data['C_R'];Q=data['Q_R'];A=data['A_R']
def corr(x,y):return {'pearson':float(pearsonr(x,y).statistic),'spearman':float(spearmanr(x,y).statistic)}
Ynorm=Y/np.sqrt(np.maximum(1,m))
res={'prime_count_at_max':int(m[-1]),'waves_amplitude_corr_C':corr(abs(Y[idx]),C[idx]),
     'waves_normalized_corr_C':corr(abs(Ynorm[idx]),C[idx]),
     'waves_weighted_corr_C':corr(abs(Yw[idx]),C[idx]),
     'waves_signed_corr_Q':corr(Y[idx],Q[idx]),
     'waves_norm_signed_corr_Q':corr(Ynorm[idx],Q[idx]),
     'normwave_mean':float(Ynorm[idx].mean()),'normwave_std':float(Ynorm[idx].std()),
     'normwave_abs_ge_2':float(np.mean(abs(Ynorm[idx])>=2)),
     'selected_roots':[]}
for r in [56,317,1000,5561,6000]:
 if r > Rmax: continue
 id=np.where(R==r)[0][0]
 res['selected_roots'].append({'R':r,'primes_active':int(m[id]),'Y_grow':float(Y[id]),'Y_grow_norm':float(Ynorm[id]),'C_R':float(C[id])})
np.savetxt(O+'/growing_prime_wave_scan.csv',np.stack([R,m,Y,Ynorm,Yw,C,A],axis=1),delimiter=',',header='R,num_primes,Y_growing,Y_over_sqrt_m,Y_weighted,C_R,A_R',comments='')
with open(O+'/growing_prime_wave_results.json','w') as f:json.dump(res,f,indent=2)
plt.figure(figsize=(9.6,5.4))
plt.scatter(abs(Ynorm[idx]),C[idx],s=6,alpha=.25)
plt.xlabel(r'Normalized growing prime-wave amplitude $|Y_{p\leq R}(R^2-1)|/\sqrt{\pi(R)}$')
plt.ylabel('Actual finite-C ratio $C_R$')
plt.title('All available prime periods up to R, entering sequentially\nTested against genuine Mobius roots 31 through '+str(Rmax))
plt.grid(alpha=.2);plt.tight_layout();plt.savefig(O+'/growing_sine_vs_finite_C.png',dpi=175);plt.close()
print(json.dumps(res,indent=2))
