#!/usr/bin/env python3
"""Generate fixed-x prime insertion figures from the exact stage CSVs."""
from pathlib import Path
import pandas as pd
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
D=Path(__file__).resolve().parent

def chart_stage(x):
    d=pd.read_csv(D/f'prime_steps_x{x}.csv')
    mx=int(d.true_M.iloc[0]); root=int(x**.5)
    fig, ax=plt.subplots(figsize=(12,5.8))
    ax.plot(d.prime,d.candidate_sum,linewidth=2.25,label='Prime-candidate signed field')
    ax.plot(d.prime,d.smooth_sum,linewidth=1.6,label='Smooth-only Euler population',alpha=.75)
    ax.axhline(mx,linestyle='--',color='black',linewidth=1.2,label=f'Actual M({x})={mx}')
    for cut,txt in [(root,'sqrt(x): square-zero support complete'),(x/3,'x/3: last two-fold layer begins'),(x/2,'x/2: candidate reconstruction complete')]:
        ax.axvline(cut,alpha=.35,color='grey',linewidth=1.5)
        ax.annotate(txt,xy=(cut,.03),xycoords=('data','axes fraction'),rotation=90,fontsize=9,ha='left',va='bottom')
    ax.set(xlabel='Last prime admitted',ylabel='Signed arithmetic population',title=f'Fixed endpoint x={x}: sequential insertion of actual primes')
    ax.set_xlim(0,x)
    ax.legend(loc='lower right')
    ax.grid(alpha=.25)
    fig.tight_layout()
    fig.savefig(D/f'sequential_prime_population_x{x}.png',dpi=165)
    plt.close(fig)

for x in (317,1027,100488): chart_stage(x)

fig,ax=plt.subplots(figsize=(10.5,6))
for x in (317,1027,100488,999999):
    d=pd.read_csv(D/f'prime_steps_x{x}.csv')
    # stage correctness is a pointwise statistic; cannot substitute for signed cancellation
    ax.plot(d.prime/x,d.fraction_correct,label=f'x={x:,}',linewidth=1.8)
ax.axvline(1/3,color='grey',alpha=.45,linestyle=':',label='x/3')
ax.axvline(1/2,color='grey',alpha=.45,linestyle='--',label='x/2')
ax.axhline(.99,color='black',linestyle=':',alpha=.7)
ax.set(xlabel='Prime cutoff / fixed endpoint x',ylabel='Fraction of site values agreeing with actual Mobius',
       title='When does the prime-comb field become pointwise correct?')
ax.set_xlim(0,.55);ax.set_ylim(.55,1.005);ax.grid(alpha=.2);ax.legend()
fig.tight_layout();fig.savefig(D/'site_agreement_by_prime_cutoff.png',dpi=165);plt.close(fig)

for x in (317,1027,100488,999999):
    d=pd.read_csv(D/f'ancestry_prefix_x{x}.csv')
    fig,ax=plt.subplots(figsize=(11.5,6.3))
    ax.plot(d.prime,d.shared_gcd_signed_overlap,label='Shared gcd>1: signed overlap',linewidth=2)
    ax.plot(d.prime,d.coprime_signed_overlap,label='Coprime gcd=1: signed overlap',linewidth=1.8)
    ax.axhline(0,color='black',linewidth=1)
    if x in (317,1027):
        ax.set_xlim(d.prime.min(),d.prime.max())
    else:
        ax.set_xscale('log')
    ax.set(xlabel='Highest prime inserted after sqrt(x)',ylabel='Unordered signed pair-overlap count',
           title=f'x={x:,}: exact ancestry-conditioned overlap as primes enter')
    ax.legend();ax.grid(alpha=.2)
    fig.tight_layout();fig.savefig(D/f'ancestry_overlap_prime_cutoff_x{x}.png',dpi=165);plt.close(fig)

for x in (100488,999999):
    d=pd.read_csv(D/f'prime_steps_x{x}.csv')
    if 'stage_C_proxy' not in d:continue
    fig,ax=plt.subplots(figsize=(11.5,5.8))
    ax.plot(d.prime/x,d.stage_C_proxy,label='Truncated field proxy |2M(R-1)-J_y|/(R sqrt K)',linewidth=2)
    ax.axhline(float(d.stage_C_proxy.iloc[-1]),label='Actual finite-C ratio at full prime cutoff',linestyle='--',color='black')
    ax.axhline(1.5,label='Example fixed budget 1.5 (not a theorem)',linestyle=':',color='grey')
    ax.axvline(1/3,color='black',alpha=.4);ax.axvline(1/2,color='black',alpha=.4)
    ax.set(yscale='log',xlabel='Highest processed prime / x',ylabel='Truncated C proxy (NOT actual finite C until completion)',
           title=f'x={x:,}: large apparent amplification persists until final 2p corrections')
    ax.set_xlim(.0,.52);ax.grid(alpha=.2);ax.legend()
    fig.tight_layout();fig.savefig(D/f'finite_C_proxy_prime_cutoff_x{x}.png',dpi=165);plt.close(fig)

print('Created',len(list(D.glob('*.png'))),'figures')
