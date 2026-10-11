#!/usr/bin/env python3
"""Reproduce data-derived charts from exact C++ arithmetic census."""
from pathlib import Path
import pandas as pd
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

D=Path(__file__).resolve().parent
roots=pd.read_csv(D/'root_features.csv')
gcd=pd.read_csv(D/'selected_gcd_overlap.csv')
shg=pd.read_csv(D/'selected_smooth_high_gcd.csv')
owner=pd.read_csv(D/'selected_owner_groups.csv')
q=roots[roots.R>=31].copy()

fig,ax=plt.subplots(figsize=(11,5.5))
R=q.R.to_numpy()
shared=q.same_prime_cross_shared/(q.R*q.R*q.K_R)
coprime=q.same_prime_cross_gcd1/(q.R*q.R*q.K_R)
energy=q.centered_owner_prime_diagonal/(q.R*q.R*q.K_R)
ax.plot(R, shared, label='Shared gcd: signed cross-interaction',lw=1.4)
ax.plot(R, coprime, label='Coprime: signed cross-interaction',lw=1.4)
ax.plot(R, energy, label='Same-prime total Gram (nonnegative)',lw=1.4)
ax.axhline(0,color='gray',lw=.6)
ax.set(xlabel='Root R',ylabel=r'Coefficient divided by $R^2K_R$',title='Exact conditional prime-cofactor overlap, all roots 31–6000')
ax.legend(loc='center right');ax.grid(alpha=.2)
fig.tight_layout();fig.savefig(D/'conditional_gcd_overlap.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(11,5.5))
ax.plot(shg.R,shg.coprime_ancestry_cross/shg.full_smooth_high_cross.abs(),label='Coprime smooth/high interaction',marker='o')
ax.plot(shg.R,shg.shared_ancestry_cross/shg.full_smooth_high_cross.abs(),label='Shared-gcd smooth/high interaction',marker='s')
ax.axhline(-1,label='Full smooth/high interaction',ls='--',lw=1)
ax.axhline(0,color='gray',lw=.6)
ax.set(xlabel='Root R (six exact censuses)',ylabel=r'Signed interaction / $|S_R H_R|$',title='Scale-dependent reversal: which ancestry sector supplies the negative cross-energy?')
ax.grid(alpha=.2);ax.legend()
fig.tight_layout();fig.savefig(D/'smooth_high_conditional_reversal.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(11,5.5))
ax.plot(q.R,q.weighted_parity_mean,label='Prime-extension weighted Möbius parity',lw=1)
ax.plot(q.R,q.unweighted_parity_mean,label='Unweighted squarefree-cofactor parity',lw=1,alpha=.9)
ax.axhline(0,color='gray',lw=.7)
ax.set(xlabel='Root R',ylabel='Signed parity mean',title='Prime-extension availability changes the apparent sign balance')
ax.grid(alpha=.2);ax.legend()
fig.tight_layout();fig.savefig(D/'weighted_unweighted_parity.png',dpi=160);plt.close(fig)

# Exact historical Möbius parity CDF difference at the fixed root R=317.
R=317
mu=[1]*(R+1)
mu[0]=0
is_p=[True]*(R+1)
for p in range(2,R+1):
    if is_p[p]:
        for n in range(p,R+1,p):mu[n]=-mu[n]
        for n in range(p*p,R+1,p*p):mu[n]=0
        for n in range(p*p,R+1,p):is_p[n]=False
Nplus=mu[1:R].count(1);Nminus=mu[1:R].count(-1)
cumpos=cumneg=0
cdf=[]
for c in range(1,R):
    if mu[c]==1:cumpos+=1
    if mu[c]==-1:cumneg+=1
    cdf.append(cumpos/Nplus-cumneg/Nminus)
fig,ax=plt.subplots(figsize=(11,5.5))
ax.plot(range(1,R),cdf,label=r'$P(c\leq t\mid\mu(c)=+1)-P(c\leq t\mid\mu(c)=-1)$')
ax.axhline(0,color='black',lw=.7)
ax.set(xlabel='Cofactor cutoff t (corresponds to decreasing prime availability)',ylabel='Conditional CDF difference',title='No first-order stochastic dominance of prime availability (R = 317)')
ax.grid(alpha=.2);ax.legend()
fig.tight_layout();fig.savefig(D/'parity_conditional_cdf_crossing.png',dpi=160);plt.close(fig)
print('Charts generated:',*[p.name for p in D.glob('*.png')])
