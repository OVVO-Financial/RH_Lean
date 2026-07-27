#!/usr/bin/env python3
from __future__ import annotations
import math, json, sys
from pathlib import Path
import numpy as np
import pandas as pd
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE))
from validate_or_kill_kj import prime_pi_table, li_table, mobius_linear, exact_pair_matrix

OUT=BASE/'results'
OUT.mkdir(exist_ok=True)
scales=[32000,64000,128000,200000]
H=256
window_ids=list(range(8))
bands=[('deep_1_8',1/8,1/4),('transition_1_4',1/4,1/2),('aggregate_1_64_to_1_2',1/64,1/2)]
max_u=0
for N in scales:
 for wid in window_ids:
  t=N+(wid+1)*H-1
  cmin=max(1,int(N/64))
  max_u=max(max_u,((t+1)**2-1)//cmin)
print('max_u',max_u)
pi=prime_pi_table(max_u)
li=li_table(max_u)
mu=mobius_linear(max(scales)+10)
rng=np.random.default_rng(20260727)
rows=[]
for N in scales:
 for wid in window_ids:
  start=N+wid*H
  for label,lf,hf in bands:
   clo=max(1,int(math.floor(N*lf))); chi=max(clo+1,int(math.ceil(N*hf)))
   c,A,KJ=exact_pair_matrix(start,H,clo,chi,pi,li,mu)
   signs=mu[c].astype(float)
   y=A@signs
   colmeans=A.mean(axis=0)
   Ac=A-colmeans
   yc=Ac@signs
   mean_actual=H*float(colmeans@signs)**2
   centered_actual=float(yc@yc)
   mean_diag=H*float(colmeans@colmeans)
   centered_diag=float(np.sum(Ac*Ac))
   total_actual=float(y@y); total_diag=float(np.sum(A*A))
   reps=64
   rs=rng.choice(np.array([-1.,1.]),size=(len(c),reps))
   yr=A@rs
   yrc=Ac@rs
   rtot=np.sum(yr*yr,axis=0)/total_diag
   rmean=H*np.mean(yr,axis=0)**2/mean_diag if mean_diag else np.full(reps,np.nan)
   rcent=np.sum(yrc*yrc,axis=0)/centered_diag if centered_diag else np.full(reps,np.nan)
   Kp=KJ[0]@signs; Jp=KJ[1]@signs
   rows.append({
    'N':N,'window_id':wid,'start':start,'H':H,'band':label,'columns':len(c),
    'total_ratio':total_actual/total_diag,
    'coherent_ratio':mean_actual/mean_diag if mean_diag else np.nan,
    'centered_ratio':centered_actual/centered_diag if centered_diag else np.nan,
    'coherent_fraction_actual':mean_actual/total_actual if total_actual else np.nan,
    'coherent_fraction_diagonal':mean_diag/total_diag if total_diag else np.nan,
    'total_random_percentile':(np.sum(rtot<=total_actual/total_diag)+.5)/(reps+1),
    'coherent_random_percentile':(np.sum(rmean<=mean_actual/mean_diag)+.5)/(reps+1) if mean_diag else np.nan,
    'centered_random_percentile':(np.sum(rcent<=centered_actual/centered_diag)+.5)/(reps+1) if centered_diag else np.nan,
    'KJ_survival':float(y@y)/(float(Kp@Kp)+float(Jp@Jp)),
    'KJ_corr':float(np.corrcoef(Kp,Jp)[0,1]),
   })
   print(N,wid,label,'total',rows[-1]['total_ratio'],'mean',rows[-1]['coherent_ratio'],'center',rows[-1]['centered_ratio'])
df=pd.DataFrame(rows)
df.to_csv(OUT/'kj_coherent_centered_grid.csv',index=False)
summary=df.groupby('band').agg(
 total_median=('total_ratio','median'),total_max=('total_ratio','max'),
 coherent_median=('coherent_ratio','median'),coherent_max=('coherent_ratio','max'),
 centered_median=('centered_ratio','median'),centered_max=('centered_ratio','max'),
 coherent_fraction_median=('coherent_fraction_actual','median'),
 centered_below_one=('centered_ratio',lambda x: float(np.mean(x<1))),
 coherent_below_one=('coherent_ratio',lambda x: float(np.mean(x<1))),
 KJ_survival_median=('KJ_survival','median'),KJ_corr_median=('KJ_corr','median'),
).reset_index()
summary.to_csv(OUT/'kj_coherent_centered_summary.csv',index=False)
print('\nSUMMARY\n',summary.to_string(index=False))
