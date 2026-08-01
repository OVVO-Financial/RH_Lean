#!/usr/bin/env python3
from __future__ import annotations
import math, json
from pathlib import Path
import numpy as np
import pandas as pd
from scipy.special import expi
from numba import njit

BASE=Path(__file__).resolve().parent
OUT=BASE/'results'; OUT.mkdir(parents=True, exist_ok=True)

@njit(cache=True)
def mobius_linear(n:int)->np.ndarray:
    mu=np.zeros(n+1,np.int8); mu[1]=1
    comp=np.zeros(n+1,np.uint8)
    primes=np.empty(n+1,np.int32); pc=0
    for i in range(2,n+1):
        if comp[i]==0:
            primes[pc]=i; pc+=1; mu[i]=-1
        for j in range(pc):
            p=primes[j]; x=i*p
            if x>n: break
            comp[x]=1
            if i%p==0:
                mu[x]=0; break
            mu[x]=-mu[i]
    return mu

def prime_pi_table(n:int)->np.ndarray:
    isp=np.ones(n+1,np.bool_); isp[:2]=False
    for p in range(2,math.isqrt(n)+1):
        if isp[p]: isp[p*p:n+1:p]=False
    return np.cumsum(isp,dtype=np.int32)

def li(x):
    x=np.asarray(x,dtype=np.float64); return expi(np.log(x))

def profiles(start,H,pi,mu_small,M):
    rows=[]; maxerr=0
    for t in range(start,start+H):
        S=(t+1)**2; X=S-1
        c=np.arange(1,t+1,dtype=np.int64)
        Lo=np.maximum(t+2,(S+2*c-1)//(2*c)); U=X//c
        prime=(pi[U]-pi[Lo-1]).astype(float)
        base=li(U)-li(Lo-1)
        muc=mu_small[c].astype(float)
        ps=float(muc@prime); bs=float(muc@base)
        L=float(M[X])+ps
        Main=L-bs
        R=ps-bs
        odd=np.arange(1,t//2+1,2,dtype=np.int64); odd=odd[mu_small[odd]!=0]
        ch=2*odd; w=mu_small[odd].astype(float)
        d1=(pi[U[odd-1]]-pi[Lo[odd-1]-1]).astype(float)-(li(U[odd-1])-li(Lo[odd-1]-1))
        d2=(pi[U[ch-1]]-pi[Lo[ch-1]-1]).astype(float)-(li(U[ch-1])-li(Lo[ch-1]-1))
        P=float(w@(d1-d2))
        tail=np.arange(t//2+1,t+1,dtype=np.int64); tail=tail[(tail&1)==1]; tail=tail[mu_small[tail]!=0]
        dt=(pi[U[tail-1]]-pi[Lo[tail-1]-1]).astype(float)-(li(U[tail-1])-li(Lo[tail-1]-1))
        T=float(mu_small[tail].astype(float)@dt)
        maxerr=max(maxerr,abs(R-(P+T)),abs(float(M[X])-(Main-R)))
        rows.append({'t':t,'Main':Main,'P':P,'T':T,'R':R,'SquareM':float(M[X])})
    return pd.DataFrame(rows),maxerr

def decomp_metrics(df,N,wid):
    # final = Main - P - T
    X=df[['Main','P','T']].to_numpy(float)
    signed=X*np.array([1.,-1.,-1.])
    total=signed.sum(axis=1)
    G=signed.T@signed
    means=signed.mean(axis=0); H=len(df)
    G0=H*np.outer(means,means); Xc=signed-means; Gc=Xc.T@Xc
    comp=np.diag(G); Et=float(total@total)
    corr=np.corrcoef(signed,rowvar=False)
    coherent_total=H*float(total.mean()**2); centered_total=float((total-total.mean())@(total-total.mean()))
    coherent_sep=float(np.trace(G0)); centered_sep=float(np.trace(Gc))
    return {
      'N':N,'window_id':wid,'start':int(df.t.iloc[0]),'H':H,
      'final_energy':Et,'separate_energy':float(comp.sum()),'final_survival':Et/float(comp.sum()),
      'coherent_survival':coherent_total/coherent_sep if coherent_sep else np.nan,
      'centered_survival':centered_total/centered_sep if centered_sep else np.nan,
      'final_coherent_fraction':coherent_total/Et if Et else np.nan,
      'Main_energy':float(G[0,0]),'P_energy':float(G[1,1]),'T_energy':float(G[2,2]),
      'cross_Main_negP':2*float(G[0,1]),'cross_Main_negT':2*float(G[0,2]),'cross_negP_negT':2*float(G[1,2]),
      'corr_Main_negP':float(corr[0,1]),'corr_Main_negT':float(corr[0,2]),'corr_negP_negT':float(corr[1,2]),
      'P_coherent_fraction':H*float(signed[:,1].mean()**2)/float(G[1,1]) if G[1,1] else np.nan,
      'Main_coherent_fraction':H*float(signed[:,0].mean()**2)/float(G[0,0]) if G[0,0] else np.nan,
      'final_over_HN2':Et/(H*N*N),
      'P_over_HN2':float(G[1,1])/(H*N*N),
      'Main_over_HN2':float(G[0,0])/(H*N*N),
      'T_over_HN2':float(G[2,2])/(H*N*N),
    }

def main():
    Ns=[4000,6000,8000,10000]
    H=192; wids=[0,1,2,3]
    tmax=max(N+(max(wids)+1)*H-1 for N in Ns); xmax=(tmax+1)**2-1
    print('precompute',tmax,xmax)
    pi=prime_pi_table(xmax)
    mu_small=mobius_linear(tmax)
    mu_all=mobius_linear(xmax)
    M=np.cumsum(mu_all,dtype=np.int64)
    rows=[]; errs=[]
    for N in Ns:
      for wid in wids:
        start=N+wid*H
        df,e=profiles(start,H,pi,mu_small,M)
        df.to_csv(OUT/f'full_profiles_N{N}_w{wid}.csv',index=False)
        rows.append(decomp_metrics(df,N,wid)); errs.append(e)
        print('done',N,wid,'surv',rows[-1]['final_survival'],'coh',rows[-1]['coherent_survival'],'Pcoh',rows[-1]['P_coherent_fraction'])
    out=pd.DataFrame(rows); out.to_csv(OUT/'full_recombination_grid.csv',index=False)
    print('\nRESULTS\n',out.to_string(index=False))
    print('max exact error',max(errs))
    print('\nSUMMARY\n',out.groupby('N').agg(final_survival_median=('final_survival','median'),coherent_survival_median=('coherent_survival','median'),centered_survival_median=('centered_survival','median'),P_coherent_median=('P_coherent_fraction','median'),final_HN2_max=('final_over_HN2','max')).to_string())
if __name__=='__main__': main()
