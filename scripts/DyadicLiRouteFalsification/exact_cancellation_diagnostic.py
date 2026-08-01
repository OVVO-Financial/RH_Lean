from pathlib import Path
import numpy as np, pandas as pd, math, sys
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
from validate_or_kill_kj import prime_pi_table, li_table, mobius_linear, exact_pair_matrix

base=BASE/'results'
base.mkdir(parents=True, exist_ok=True)
files=sorted(base.glob('full_profiles_N*_w*.csv'))
rows=[]; all_parts=[]
for f in files:
    df=pd.read_csv(f)
    stem=f.stem
    N=int(stem.split('_N')[1].split('_w')[0]); wid=int(stem.split('_w')[1])
    P=df.P.to_numpy(float); T=df["T"].to_numpy(float); Main=df.Main.to_numpy(float); M=df.SquareM.to_numpy(float)
    H=len(df); one=np.ones(H)
    means={k:float(np.mean(v)) for k,v in [('P',P),('T',T),('Main',Main),('M',M)]}
    identity=Main-P-T-M
    X=np.column_stack([Main,T,one])
    coef, *_=np.linalg.lstsq(X,P,rcond=None)
    resid=P-X@coef
    X2=np.column_stack([Main,T])
    coef2,*_=np.linalg.lstsq(X2,P,rcond=None)
    resid2=P-X2@coef2
    normP=np.linalg.norm(P)
    candidates={
      'P_minus_Main_plus_T':P-(Main-T),
      'P_minus_Main_minus_T':P-(Main+T),
      'P_plus_Main_plus_T':P+(Main+T),
      'P_minus_Main':P-Main,
      'P_plus_T':P+T,
    }
    row={'N':N,'window_id':wid,'H':H,**{f'mean_{k}':v for k,v in means.items()},
         'exact_identity_max':float(np.max(np.abs(identity))),
         'coherent_uncancelled_equals_meanM_error':abs((means['Main']-means['P']-means['T'])-means['M']),
         'meanM_abs':abs(means['M']),
         'meanM_zero':means['M']==0,
         'ls_coef_Main':coef[0],'ls_coef_T':coef[1],'ls_coef_const':coef[2],
         'ls_rel_resid':float(np.linalg.norm(resid)/normP),
         'ls_max_resid':float(np.max(np.abs(resid))),
         'ls2_coef_Main':coef2[0],'ls2_coef_T':coef2[1],
         'ls2_rel_resid':float(np.linalg.norm(resid2)/normP),
    }
    for k,v in candidates.items(): row[k+'_rel']=float(np.linalg.norm(v)/normP)
    rows.append(row)
    all_parts.append(pd.DataFrame({'P':P,'Main':Main,'T':T,'M':M,'one':one,'N':N,'wid':wid}))

out=pd.DataFrame(rows).sort_values(['N','window_id'])
out.to_csv(base/'exact_cancellation_window_tests.csv',index=False)
all_df=pd.concat(all_parts,ignore_index=True)
y=all_df.P.to_numpy(); X=np.column_stack([all_df.Main,all_df["T"],np.ones(len(all_df))])
coef,*_=np.linalg.lstsq(X,y,rcond=None); r=y-X@coef
print('WINDOW TESTS')
print(out[['N','window_id','mean_P','mean_Main','mean_T','mean_M','meanM_abs','ls_rel_resid','ls2_rel_resid']].to_string(index=False))
print('\nGLOBAL FIT P = a Main + b T + c')
print(coef,'rel',np.linalg.norm(r)/np.linalg.norm(y),'max',np.max(np.abs(r)))
print('\nSUMMARY')
print(out[['meanM_abs','ls_rel_resid','ls2_rel_resid','P_minus_Main_plus_T_rel','P_minus_Main_minus_T_rel','P_plus_Main_plus_T_rel']].describe().to_string())

Ns=sorted(out.N.unique()); H=192; wids=sorted(out.window_id.unique())
tmax=max(N+(max(wids)+1)*H-1 for N in Ns)
cmin=min(max(1,int(N/64)) for N in Ns)
max_u=((tmax+1)**2-1)//cmin
print('\nprecompute pair matrix max_u',max_u)
pi=prime_pi_table(max_u); li=li_table(max_u); mu=mobius_linear(tmax+10)
svrows=[]
for N in Ns:
  for wid in wids:
    start=N+wid*H
    c,A,_=exact_pair_matrix(start,H,max(1,int(N/64)),int(math.ceil(N/2)),pi,li,mu)
    U,s,Vh=np.linalg.svd(A,full_matrices=False)
    u=U[:,0]
    if u.mean()<0:u=-u
    df=pd.read_csv(base/f'full_profiles_N{N}_w{wid}.csv')
    Main=df.Main.to_numpy(float); T=df["T"].to_numpy(float); P=df.P.to_numpy(float); one=np.ones(H)
    def proj_rel(cols):
      X=np.column_stack(cols); b,*_=np.linalg.lstsq(X,u,rcond=None); rr=u-X@b
      return float(np.linalg.norm(rr)),b,float(np.max(np.abs(rr)))
    r1,b1,m1=proj_rel([one]); r2,b2,m2=proj_rel([Main,T]); r3,b3,m3=proj_rel([Main,T,one])
    svrows.append({'N':N,'window_id':wid,'top_share':float(s[0]**2/np.sum(s*s)),
                   'u_constant_resid':r1,'u_constant_max':m1,
                   'u_MainT_resid':r2,'u_MainT_max':m2,
                   'u_MainTconst_resid':r3,'u_MainTconst_max':m3,
                   'corr_u_const':float(np.dot(u,one)/(np.linalg.norm(u)*np.linalg.norm(one))),
                   'coef_MainTconst_Main':b3[0],'coef_MainTconst_T':b3[1],'coef_MainTconst_const':b3[2]})
sv=pd.DataFrame(svrows); sv.to_csv(base/'exact_cancellation_svd_tests.csv',index=False)
print('\nSVD SUMMARY')
print(sv.describe().to_string())
