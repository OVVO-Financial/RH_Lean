from __future__ import annotations
import argparse, json, math
from pathlib import Path
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from scipy.special import expi
from scipy.stats import spearmanr
from nns.meboot import nns_meboot

R0_DEFAULT=56
RMAX_DEFAULT=3162
RHO_GRID=np.array([-0.95,-0.75,-0.50,-0.25,0.0,0.25,0.50,0.75,0.95])
PHIS=[-0.90,-0.50,0.0,0.50,0.90,0.97,0.99]
LI2_CONST=float(expi(math.log(2.0)))

def sieve(limit:int)->tuple[np.ndarray,np.ndarray]:
    is_prime=np.ones(limit+1,dtype=bool); is_prime[:2]=False
    for p in range(2,int(math.isqrt(limit))+1):
        if is_prime[p]: is_prime[p*p:limit+1:p]=False
    return is_prime,np.cumsum(is_prime,dtype=np.int64)

def li2(x:np.ndarray|float)->np.ndarray|float:
    return expi(np.log(x))-LI2_CONST

def robust_floor_li2(values:np.ndarray, near_tol:float=2e-7)->tuple[np.ndarray,int,float]:
    vals=np.asarray(li2(values.astype(np.float64)),dtype=np.float64)
    nearest=np.rint(vals); dist=np.abs(vals-nearest)
    floors=np.floor(vals).astype(np.int64)
    idx=np.flatnonzero(dist<near_tol)
    max_correction=0.0
    if idx.size:
        import mpmath as mp
        mp.mp.dps=80; c=mp.ei(mp.log(2))
        for j in idx:
            xx=int(values[j]); hp=mp.ei(mp.log(xx))-c; f=int(mp.floor(hp))
            max_correction=max(max_correction,abs(float(hp)-float(vals[j])))
            floors[j]=f
    return floors,int(idx.size),float(max_correction)

def corr(a,b):
    a=np.asarray(a,dtype=float); b=np.asarray(b,dtype=float)
    if len(a)<2 or np.std(a)==0 or np.std(b)==0: return float('nan')
    return float(np.corrcoef(a,b)[0,1])

def primitive_stream(is_prime:np.ndarray,n0:int,n1:int,chunk:int=1_000_000):
    nlen=n1-n0; xi=np.empty(nlen,dtype=np.int8)
    prev_q=int(robust_floor_li2(np.array([n0],dtype=np.int64))[0][0])
    near_total=0; max_corr=0.0; off=0
    for lo in range(n0+1,n1+1,chunk):
        hi=min(n1+1,lo+chunk); arr=np.arange(lo,hi,dtype=np.int64)
        q,near,mc=robust_floor_li2(arr); near_total+=near; max_corr=max(max_corr,mc)
        dq=np.empty_like(q); dq[0]=q[0]-prev_q; dq[1:]=np.diff(q)
        if np.any((dq<0)|(dq>1)):
            bad=np.flatnonzero((dq<0)|(dq>1))[:10]
            raise RuntimeError(f'floor-Li increments outside {{0,1}} at {arr[bad]} values {dq[bad]}')
        x=is_prime[lo:hi].astype(np.int8)-dq.astype(np.int8)
        xi[off:off+len(x)]=x; off+=len(x); prev_q=int(q[-1])
    return xi,prev_q,near_total,max_corr

def longest_run(values:np.ndarray,target:int)->int:
    m=(values==target).astype(np.int8)
    if not np.any(m): return 0
    padded=np.concatenate(([0],m,[0])); d=np.diff(padded)
    starts=np.flatnonzero(d==1); ends=np.flatnonzero(d==-1)
    return int(np.max(ends-starts))

def build_actual(r0:int,rmax:int):
    nmax=rmax*rmax
    is_prime,pi=sieve(nmax)
    sq=np.arange(r0,rmax+1,dtype=np.int64)**2
    q_sq,near_sq,mc_sq=robust_floor_li2(sq)
    r=np.arange(r0,rmax,dtype=np.int64)
    p=pi[(r+1)**2]-pi[r**2]
    f=np.diff(q_sq)
    err=p.astype(np.int64)-f.astype(np.int64)
    w=f.astype(float)/r.astype(float)
    var=r.astype(float)*w*(1.0-w)
    if np.any(var<=0): raise RuntimeError('nonpositive floor-Li odd-seat variance')
    z=err.astype(float)/np.sqrt(var)
    d0=int(pi[r0*r0]-q_sq[0])
    endpoints=r+1
    d=d0+np.cumsum(err)
    direct=pi[endpoints**2]-q_sq[1:]
    if not np.array_equal(d,direct): raise RuntimeError('square endpoint backlog telescope failed')
    xi,q_end,near_prim,mc_prim=primitive_stream(is_prime,r0*r0,rmax*rmax)
    xi_cum=np.cumsum(xi,dtype=np.int64)
    if int(d0+xi_cum[-1])!=int(pi[nmax]-q_end): raise RuntimeError('primitive final telescope failed')
    prefix=np.concatenate(([0],xi_cum))
    left=(r*r-r0*r0).astype(np.int64)
    right=((r+1)*(r+1)-r0*r0).astype(np.int64)
    block_xi=prefix[right]-prefix[left]
    if not np.array_equal(block_xi,err):
        bad=np.flatnonzero(block_xi!=err)[:10]
        raise RuntimeError(f'primitive/block mismatch {bad}')
    return dict(is_prime=is_prime,pi=pi,r=r,p=p,f=f,err=err,var=var,z=z,d0=d0,d=d,
        q_sq=q_sq,xi=xi,xi_cum=xi_cum,near_sq=near_sq,mc_sq=mc_sq,
        near_prim=near_prim,mc_prim=mc_prim)

def max_abs_normalized(d,r_end,cut=1000):
    vals=np.abs(d)/(r_end*np.log(r_end)); mask=r_end>=cut
    return float(np.max(vals[mask])) if np.any(mask) else float(np.max(vals))

def path_metrics(zz,z_actual,var,d0,r_end,f_block,r_block,suite,integerize=False,**extra):
    sigma=np.sqrt(var); e=zz*sigma
    if integerize:
        e=np.rint(e)
        implied=f_block.astype(float)+e
        physical_viol=int(np.sum((implied<0)|(implied>r_block.astype(float))))
        implied=np.clip(implied,0,r_block.astype(float)); e=implied-f_block.astype(float)
    else:
        physical_viol=0
    centered=np.cumsum(e); d=d0+centered; b=np.cumsum(var)
    rh=np.abs(d)/(r_end*np.log(r_end))
    return {'suite':suite,'integerized':bool(integerize),**extra,
      'realized_pearson_to_actual':corr(zz,z_actual),
      'realized_spearman_to_actual':float(spearmanr(zz,z_actual).statistic),
      'lag1':corr(zz[:-1],zz[1:]),'lag2':corr(zz[:-2],zz[2:]),
      'mean_z':float(np.mean(zz)),'sd_z':float(np.std(zz,ddof=1)),
      'max_rh_ratio_all':float(np.max(rh)),
      'max_rh_ratio_R_ge_500':float(np.max(rh[r_end>=500])) if np.any(r_end>=500) else float(np.max(rh)),
      'max_rh_ratio_R_ge_1000':float(np.max(rh[r_end>=1000])) if np.any(r_end>=1000) else float(np.max(rh)),
      'final_rh_ratio':float(rh[-1]),
      'max_centered_z':float(np.max(np.abs(centered)/np.sqrt(b))),
      'max_K_log3B':float(np.max(centered**2/((np.log(r_end)**3)*b))),
      'final_D':float(d[-1]),'physical_clip_count':physical_viol}

def ar1(n,phi,rng):
    x=np.empty(n); x[0]=rng.normal(); scale=math.sqrt(max(1e-12,1-phi*phi))
    for i in range(1,n): x[i]=phi*x[i-1]+scale*rng.normal()
    return x

def rank_reorder(values,template):
    order=np.argsort(template,kind='mergesort')
    out=np.empty_like(values); out[order]=np.sort(values)
    return out

def summarize(df,keys):
    columns=['realized_pearson_to_actual','realized_spearman_to_actual','lag1','lag2',
      'max_rh_ratio_all','max_rh_ratio_R_ge_500','max_rh_ratio_R_ge_1000',
      'final_rh_ratio','max_centered_z','max_K_log3B','physical_clip_count']
    if 'realized_spearman_to_template' in df.columns:
        columns.append('realized_spearman_to_template')
    rows=[]; group_arg=keys[0] if len(keys)==1 else keys
    for key,g in df.groupby(group_arg,dropna=False):
        kt=key if isinstance(key,tuple) else (key,)
        row=dict(zip(keys,kt)); row['n']=len(g)
        for col in columns:
            if col not in g.columns: continue
            a=g[col].to_numpy(float)
            for lab,q in [('q05',.05),('median',.5),('q95',.95),('q99',.99),('max',1.0)]:
                row[f'{col}_{lab}']=float(np.quantile(a,q))
        rows.append(row)
    return pd.DataFrame(rows)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,default=Path('numerics/floor_li_discrete_meboot/results'))
    ap.add_argument('--r0',type=int,default=R0_DEFAULT)
    ap.add_argument('--rmax',type=int,default=RMAX_DEFAULT)
    ap.add_argument('--main-reps',type=int,default=199)
    ap.add_argument('--serial-templates',type=int,default=3)
    ap.add_argument('--serial-reps',type=int,default=49)
    args=ap.parse_args()
    out=args.out; out.mkdir(parents=True,exist_ok=True)
    a=build_actual(args.r0,args.rmax)
    r=a['r']; p=a['p']; f=a['f']; err=a['err']; var=a['var']; z=a['z']
    d0=a['d0']; d=a['d']; xi=a['xi']; xi_cum=a['xi_cum']; r_end=r+1
    n_start=args.r0*args.r0; n_end=args.rmax*args.rmax
    n=np.arange(n_start+1,n_end+1,dtype=np.int64); backlog=d0+xi_cum
    nonzero=xi[xi!=0]
    prim={'n_start_exclusive':int(n_start),'n_end_inclusive':int(n_end),'n_values':int(len(xi)),
      'count_minus1':int(np.sum(xi==-1)),'count_zero':int(np.sum(xi==0)),
      'count_plus1':int(np.sum(xi==1)),'nonzero_fraction':float(np.mean(xi!=0)),
      'mean_xi':float(np.mean(xi)),'sd_xi':float(np.std(xi,ddof=1)),
      'lag1_lattice':corr(xi[:-1],xi[1:]),'lag2_lattice':corr(xi[:-2],xi[2:]),
      'lag1_mismatch_event_sign':corr(nonzero[:-1],nonzero[1:]),
      'lag2_mismatch_event_sign':corr(nonzero[:-2],nonzero[2:]),
      'max_consecutive_plus1':longest_run(xi,1),'max_consecutive_minus1':longest_run(xi,-1),
      'backlog_min':int(np.min(backlog)),'backlog_max':int(np.max(backlog)),
      'backlog_final':int(backlog[-1]),
      'max_abs_backlog_over_sqrt_n_log_n':float(np.max(np.abs(backlog)/(np.sqrt(n)*np.log(n)))),
      'max_abs_backlog_over_half_sqrt_n_log_n':float(np.max(np.abs(backlog)/(0.5*np.sqrt(n)*np.log(n)))),
      'near_integer_li_values_rechecked':int(a['near_prim']),
      'max_double_vs_high_precision_li_correction':float(a['mc_prim']),
      'square_endpoint_telescope_verified':True,'primitive_to_square_block_sum_verified':True}
    (out/'primitive_stream_metrics.json').write_text(json.dumps(prim,indent=2)+'\n')
    pd.DataFrame({'R':r,'P_R':p,'F_R_floorLi':f,'block_error_P_minus_F':err,
      'variance_proxy':var,'z_floorLi':z,'E_next':d}).to_csv(out/'floor_li_block_series.csv',index=False)
    nz_idx=np.flatnonzero(xi!=0)
    pd.DataFrame({'n':(n_start+1+nz_idx).astype(np.int64),'xi':xi[nz_idx].astype(np.int8),
      'backlog_after_event':backlog[nz_idx].astype(np.int64)}).to_csv(out/'primitive_mismatch_events.csv',index=False)
    b=np.cumsum(var); centered=np.cumsum(err)
    actual={'R0':args.r0,'Rmax':args.rmax,'n_blocks':len(r),'D0':int(d0),
      'lag1_block_z':corr(z[:-1],z[1:]),'lag2_block_z':corr(z[:-2],z[2:]),
      'lag1_block_error':corr(err[:-1],err[1:]),'lag2_block_error':corr(err[:-2],err[2:]),
      'max_rh_ratio_all':float(np.max(np.abs(d)/(r_end*np.log(r_end)))),
      'max_rh_ratio_R_ge_500':max_abs_normalized(d,r_end,500),
      'max_rh_ratio_R_ge_1000':max_abs_normalized(d,r_end,1000),
      'final_rh_ratio':float(abs(d[-1])/(r_end[-1]*np.log(r_end[-1]))),
      'max_centered_z':float(np.max(np.abs(centered)/np.sqrt(b))),
      'max_K_log3B':float(np.max(centered**2/((np.log(r_end)**3)*b))),
      'F_R_min':int(np.min(f)),'F_R_max':int(np.max(f)),
      'error_min':int(np.min(err)),'error_max':int(np.max(err)),
      'near_integer_square_li_values_rechecked':int(a['near_sq'])}
    (out/'actual_metrics.json').write_text(json.dumps(actual,indent=2)+'\n')
    main_rows=[]
    for method in ('pearson','spearman'):
        offset=0 if method=='pearson' else 10000
        for ri,rho in enumerate(RHO_GRID):
            boot=nns_meboot(z,reps=args.main_reps,rho=float(rho),type=method,drift=True,
                expand_sd=True,force_clt=True,random_seed=20261002+offset+ri*100)
            mat=np.asarray(boot['replicates'],float)
            for j in range(mat.shape[1]):
                for integerize in (False,True):
                    main_rows.append(path_metrics(mat[:,j],z,var,d0,r_end,f,r,
                      'actual_dependence_sweep',integerize=integerize,method=method,
                      target_rho=float(rho),replicate=j))
    main_df=pd.DataFrame(main_rows)
    main_df.to_csv(out/'meboot_replicate_metrics.csv',index=False)
    main_sum=summarize(main_df,['integerized','method','target_rho'])
    main_sum.to_csv(out/'meboot_dependence_summary.csv',index=False)
    serial_rows=[]
    for pi_i,phi in enumerate(PHIS):
        for tid in range(args.serial_templates):
            rng=np.random.default_rng(910000+pi_i*100+tid)
            seed=rank_reorder(z,ar1(len(z),phi,rng))
            boot=nns_meboot(seed,reps=args.serial_reps,rho=.95,type='spearman',drift=False,
                expand_sd=True,force_clt=True,random_seed=920000+pi_i*100+tid)
            mat=np.asarray(boot['replicates'],float)
            for j in range(mat.shape[1]):
                st=float(spearmanr(mat[:,j],seed).statistic)
                for integerize in (False,True):
                    row=path_metrics(mat[:,j],z,var,d0,r_end,f,r,'serial_persistence_stress',
                      integerize=integerize,phi=float(phi),template=tid,replicate=j,
                      seed_lag1=corr(seed[:-1],seed[1:]))
                    row['realized_spearman_to_template']=st; serial_rows.append(row)
    serial_df=pd.DataFrame(serial_rows)
    serial_df.to_csv(out/'meboot_serial_stress_metrics.csv',index=False)
    serial_sum=summarize(serial_df,['integerized','phi'])
    serial_sum.to_csv(out/'meboot_serial_stress_summary.csv',index=False)
    report={'base_nns_paths':int(len(main_df)//2+len(serial_df)//2),
      'reported_paths_including_integerized_companion':int(len(main_df)+len(serial_df))}
    for flag,label in [(False,'continuous'),(True,'integerized')]:
        m=main_df[main_df.integerized==flag]; s=serial_df[serial_df.integerized==flag]
        report[label]={'main_paths':int(len(m)),'serial_paths':int(len(s)),
          'total_paths':int(len(m)+len(s)),
          'main_pooled_q99_RH1000':float(np.quantile(m.max_rh_ratio_R_ge_1000,.99)),
          'main_pooled_max_RH1000':float(m.max_rh_ratio_R_ge_1000.max()),
          'serial_pooled_q99_RH1000':float(np.quantile(s.max_rh_ratio_R_ge_1000,.99)),
          'serial_pooled_max_RH1000':float(s.max_rh_ratio_R_ge_1000.max()),
          'serial_pooled_q99_K':float(np.quantile(s.max_K_log3B,.99)),
          'serial_pooled_max_K':float(s.max_K_log3B.max()),
          'serial_fraction_K_le_1':float(np.mean(s.max_K_log3B<=1)),
          'all_paths_RH1000_lt_1':bool((m.max_rh_ratio_R_ge_1000<1).all()
            and (s.max_rh_ratio_R_ge_1000<1).all()),
          'total_physical_clip_count':int(m.physical_clip_count.sum()+s.physical_clip_count.sum())}
    (out/'suite_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    for flag,label in [(False,'continuous'),(True,'integerized')]:
        ss=main_sum[main_sum.integerized==flag]
        fig,ax=plt.subplots(figsize=(9,6))
        for method,g in ss.groupby('method'):
            g=g.sort_values('target_rho')
            ax.plot(g.target_rho,g.max_rh_ratio_R_ge_1000_median,marker='o',label=f'{method} median')
            ax.fill_between(g.target_rho.to_numpy(float),g.max_rh_ratio_R_ge_1000_q05.to_numpy(float),
              g.max_rh_ratio_R_ge_1000_q95.to_numpy(float),alpha=.18)
        ax.axhline(actual['max_rh_ratio_R_ge_1000'],linestyle='--',label='actual floor-Li backlog')
        ax.set_xlabel('NNS.meboot target correlation')
        ax.set_ylabel('max |E_R|/(R log R), R >= 1000')
        ax.set_title(f'Floor-Li discrete backlog dependence frontier ({label})')
        ax.legend(); fig.tight_layout()
        fig.savefig(out/f'meboot_floor_li_dependence_frontier_{label}.png',dpi=180); plt.close(fig)
        ss2=serial_sum[serial_sum.integerized==flag].sort_values('phi')
        fig,ax=plt.subplots(figsize=(9,6))
        ax.plot(ss2.phi,ss2.max_rh_ratio_R_ge_1000_median,marker='o',label='median')
        ax.fill_between(ss2.phi.to_numpy(float),ss2.max_rh_ratio_R_ge_1000_q05.to_numpy(float),
          ss2.max_rh_ratio_R_ge_1000_q95.to_numpy(float),alpha=.18)
        ax.axhline(actual['max_rh_ratio_R_ge_1000'],linestyle='--',label='actual')
        ax.set_xlabel('latent AR(1) rank-template persistence phi')
        ax.set_ylabel('max |E_R|/(R log R), R >= 1000')
        ax.set_title(f'Floor-Li serial-persistence stress ({label})')
        ax.legend(); fig.tight_layout()
        fig.savefig(out/f'meboot_floor_li_serial_stress_{label}.png',dpi=180); plt.close(fig)
    step=max(1,len(n)//20000); ns=n[::step]; bs=backlog[::step]
    fig,ax=plt.subplots(figsize=(10,6))
    ax.plot(ns,bs,label='pi(n)-floor(Li_2(n))'); ax.set_xscale('log')
    ax.set_xlabel('n'); ax.set_ylabel('integer backlog')
    ax.set_title('Primitive {-1,0,1} floor-Li mismatch backlog')
    ax.legend(); fig.tight_layout(); fig.savefig(out/'primitive_floor_li_backlog.png',dpi=180); plt.close(fig)
    print(json.dumps({'primitive':prim,'actual':actual,'suite':report},indent=2))

if __name__=='__main__':
    main()
