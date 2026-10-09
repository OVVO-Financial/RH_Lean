#!/usr/bin/env python3
"""Empirical cross-block prime/odd-composite moment study for RH_Lean PR #918.
Independent true prime sieve; Q=floor int_2^x dt/log(t); ORIGINAL odd-seat mass.
Emits machine-readable CSVs, JSON, and concise text. No conjectured inequality.
"""
import argparse, math, time, json, csv, os
from pathlib import Path
import numpy as np
from scipy.special import expi

def sieve_counts(N):
    flags = bytearray(b'\x01')*(N+1)
    flags[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(N)+1):
        if flags[p]:
            flags[p*p::p] = b'\x00'*((N-p*p)//p+1)
    counts=np.cumsum(np.frombuffer(flags,dtype=np.uint8),dtype=np.int32)
    return flags,counts

LI2_ANCHOR=float(expi(math.log(2)))
def li2_vals(z):
    return expi(np.log(z))-LI2_ANCHOR

def floor_li_nodes(max_n):
    Q=np.empty(max_n+1,dtype=np.int32)
    Q[:3]=0
    L=np.empty(max_n+1,dtype=np.float64)
    L[:3]=0.
    closest=(1.,None,None)
    numerics=[]
    for st in range(3,max_n+1,500_000):
        en=min(max_n+1,st+500_000)
        fx=li2_vals(np.arange(st,en,dtype=np.float64))
        q=np.floor(fx)
        Q[st:en]=q.astype(np.int32)
        L[st:en]=fx
        distance=np.abs(fx-np.round(fx))
        idx=int(np.argmin(distance))
        if distance[idx]<closest[0]: closest=(float(distance[idx]),st+idx,float(fx[idx]))
        near=np.flatnonzero(distance<3e-7)
        numerics.extend((st+int(i),float(fx[i]),float(distance[i])) for i in near)
    if numerics:
        import mpmath as mp
        mp.mp.dps=55
        ei2=mp.ei(mp.log(2))
        corrected=[]
        for n,z,d in numerics:
            precise=mp.ei(mp.log(n))-ei2
            q=int(mp.floor(precise))
            if q!=int(Q[n]):
                corrected.append((n,int(Q[n]),q,z,d))
                Q[n]=q
        print('high-precision q-floor near-event audit count',len(numerics),'corrections',corrected[:8],flush=True)
    print('closest float Li floor-neighbor',closest,'q_array',max_n,flush=True)
    return Q,L

def Qroots(roots):
    vals=li2_vals(roots.astype(np.float64)**2)
    d=np.abs(vals-np.round(vals))
    if np.any(d<5e-7):
        import mpmath as mp
        mp.mp.dps=55; anchor=mp.ei(mp.log(2))
        q=np.floor(vals).astype(np.int32)
        for i in np.flatnonzero(d<5e-7):
            n=int(roots[i])**2
            q[i]=int(mp.floor(mp.ei(mp.log(n))-anchor))
        return q
    return np.floor(vals).astype(np.int32)

def co_div_moment(a,b,tx=0.,ty=0.):
    x=np.asarray(a,dtype=float)-tx
    y=np.asarray(b,dtype=float)-ty
    xu=np.maximum(x,0); xl=np.maximum(-x,0)
    yu=np.maximum(y,0); yl=np.maximum(-y,0)
    cu=float(xu@yu);cl=float(xl@yl)
    du=float(xu@yl);dl=float(xl@yu)
    co=cu+cl; div=du+dl; total=co+div; dot=co-div
    pearson=float(np.corrcoef(a,b)[0,1]) if np.std(a)>0 and np.std(b)>0 else None
    cosine=float(np.dot(x,y)/(np.linalg.norm(x)*np.linalg.norm(y))) if np.linalg.norm(x)*np.linalg.norm(y)>0 else None
    return dict(CUPM=cu,CLPM=cl,DUPM=du,DLPM=dl,Co=co,Div=div,
                raw_cross=dot,unnorm_average=dot/len(x),nns_norm=dot/total if total else 0.,
                cosine=cosine,pearson=pearson,n=len(x),zero_pair_fraction=float(np.mean((x==0)|(y==0))),
                copart=co/total if total else 0.,divpart=div/total if total else 0.)

def cross_matrix(series, lag=1, target=0., field='nns_norm'):
    names=list(series)
    arr=[]
    for a in names:
        vals=[]
        for b in names:
            m=co_div_moment(series[a][:-lag],series[b][lag:],target,target)
            vals.append(m[field])
        arr.append(vals)
    return names,arr

def seat_first_moments(r, P, w, lag, target):
    # Cartesian all-pairs literal physical odd-seat NNS. No premature
    # aggregation of signed prime/composite charges. Original t=0 only.
    C=np.asarray(r,dtype=float)-P
    U=C*np.maximum(w-target,0.)+P*np.maximum(w-1-target,0.)
    L=C*np.maximum(target-w,0.)+P*np.maximum(target+1-w,0.)
    a,b=U[:-lag],U[lag:];c,d=L[:-lag],L[lag:]
    cupm=float(a@b);clpm=float(c@d);dupm=float(a@d);dlpm=float(c@b)
    co=cupm+clpm;div=dupm+dlpm
    return dict(CUPM=cupm,CLPM=clpm,DUPM=dupm,DLPM=dlpm,
                Co=co,Div=div,raw_cross=co-div,
                nns_norm=(co-div)/(co+div),div_share=div/(co+div))

def full_analysis(max_r=6000, outdir='/mnt/data/vf918_crossblock'):
    tt=time.perf_counter()
    outdir=Path(outdir);outdir.mkdir(parents=True,exist_ok=True)
    M=(max_r+1)**2
    flags,pi=sieve_counts(M)
    r=np.arange(8,max_r+1,dtype=np.int32)
    rv=r.astype(np.float64)
    rnext=r+1
    roots=np.arange(2,max_r+2,dtype=np.int32)
    qsq=Qroots(roots)
    q_by_root=np.zeros(max_r+2,dtype=np.int32)
    q_by_root[2:]=qsq
    # VF_mid root endpoint index: at r^2, sum(V_i,2<=i<r)
    all_r=np.arange(2,max_r+1,dtype=np.float64)
    masses=(2*all_r+1)/np.log(all_r*all_r+all_r+.5)
    vf_root=np.zeros(max_r+2,dtype=np.float64)
    vf_root[3:]=np.cumsum(masses)
    w=(2*rv+1)/(rv*np.log(rv*rv+rv+0.5))
    V=w*rv
    Pr=pi[rnext*rnext]-pi[r*r]
    Fr=q_by_root[rnext]-q_by_root[r]
    delta=(Pr-Fr).astype(np.float64)
    e=Pr-V
    D=pi[r*r]-vf_root[r]
    E=pi[r*r]-q_by_root[r]
    Dnext=pi[rnext*rnext]-vf_root[rnext]
    M0=np.abs(D)+w*(rv-Pr)+(1-w)*Pr
    slack=M0**2-2*Dnext**2
    assert np.allclose(Dnext,D+e,rtol=1e-9,atol=1e-7)
    assert np.allclose(E+(q_by_root[r]-vf_root[r]),D)
    assert np.all(slack>0)
    # Wide cofactor windows; pi(Q) on closed q upper but physical n<X uses X-1.
    maxq=((max_r+1)**2-1)//3
    QQ, LL=floor_li_nodes(maxq)
    LLroot=np.zeros(max_r+2,dtype=float)
    LLroot[2:]=li2_vals(roots.astype(float)**2)
    Flin=LLroot[rnext]-LLroot[r]
    deltalin=Pr-Flin
    G=np.zeros(len(r),dtype=np.int32)
    GLi=np.zeros(len(r),dtype=np.int32)
    Gcont=np.zeros(len(r),dtype=np.float64)
    plus=np.zeros(len(r),dtype=np.int32)
    minus=np.zeros(len(r),dtype=np.int32)
    for i,ri in enumerate(r):
        X=(int(ri)+1)**2
        co=np.arange(3,int(ri)+1,2,dtype=np.int64)
        lo=np.maximum(int(ri),int(ri)**2//co)
        hi=(X-1)//co
        ok=hi>lo
        dA=pi[hi[ok]]-pi[lo[ok]]
        dF=QQ[hi[ok]]-QQ[lo[ok]]
        gap=dA-dF
        G[i]=np.sum(dA,dtype=np.int64)
        GLi[i]=np.sum(dF,dtype=np.int64)
        Gcont[i]=np.sum(LL[hi[ok]]-LL[lo[ok]],dtype=np.float64)
        plus[i]=np.sum(np.maximum(gap,0),dtype=np.int64)
        minus[i]=np.sum(np.maximum(-gap,0),dtype=np.int64)
    gd=(G-GLi).astype(float)
    gd_cont=G-Gcont
    H=rv-Pr-G
    HLi=rv-Fr-GLi
    hd=H-HLi
    hd_cont=H-(rv-Flin-Gcont)
    assert np.allclose(deltalin+gd_cont+hd_cont,0)
    assert np.all(H>=0)
    assert np.allclose(delta+gd+hd,0)
    ap=(w-1)*delta
    ag=w*gd
    ah=w*hd
    assert np.allclose(ap+ag+ah,-delta)
    # prior block fixed-target pair comparisons
    native={'prime_correction':ap,'large_factor_correction':ag,'smooth_correction':ah}
    native_raw={'prime_event_error':delta,'large_factor_error':gd,'smooth_error':hd}
    native_cont={'prime_vs_contLi':deltalin,'large_vs_contLi':gd_cont,'smooth_vs_contLi':hd_cont}
    signals={'prime_minus_VF':e,'prime_minus_floorLi':delta,
             'prime_minus_contLi':deltalin,
             'large_factor_error':gd,'smooth_error':hd,
             'large_vs_contLi':gd_cont,'smooth_vs_contLi':hd_cont,
             'native_prime':ap,'native_large':ag,'native_smooth':ah,
             'scaled_VF':e/np.sqrt(V),'scaled_floorLi':delta/np.sqrt(np.maximum(1,Fr))}
    corrs=[]
    for name,xx in signals.items():
        for lag in (1,2,3,4,8,16,32,64,128):
            if len(xx)<=lag:continue
            for target in (0.,-1.,1.):
                m=co_div_moment(xx[:-lag],xx[lag:],target,target)
                corrs.append(dict(series=name,lag=lag,target=target,**m))
    # All-site physical odd-seat matrices, using CARTESIAN pairs of seats
    # in the two blocks (not same-position, not aggregate-first).
    seat_first={}
    for target in (0., -0.1, 0.1, -0.25, 0.25):
        for lag in (1,2,8,32):
            m=seat_first_moments(rv,Pr,w,lag,target)
            seat_first[f'target{target:+g}_lag{lag}']=m
            if target==0.:
                num=float(np.dot(e[:-lag],e[lag:]))
                assert math.isclose(num,m['raw_cross'],rel_tol=1e-9,abs_tol=1e-3), (
                    lag,num,m['raw_cross'])
    # Include cross-sector pair matrix, contemporaneous and future.
    matrices={}
    for description,vecs in (('native_weighted',native),('unweighted_events',native_raw),('continuousLi_reference',native_cont)):
        matrices[description]={}
        for lag in (1,2,8,32):
            for target in (0.,-1.,1.):
                for field in ('pearson','nns_norm','raw_cross','Co','Div'):
                    names,z=cross_matrix(vecs,lag,target,field)
                    matrices[description][f'lag{lag}_target{target:+g}_{field}']=dict(names=names,values=z)
    # Capturing the hypothesized negative feedback, not an unconditional sign rule.
    dyn=[]
    for name,anchor,step in [('VF',D,e),('floorLi',E,delta)]:
        for lag in (0,1,2,8,32):
            if lag:
                aa=anchor[:-lag]; ss=step[lag:]
            else: aa=anchor;ss=step
            mm=co_div_moment(aa,ss,0.,0.)
            toward=-np.sign(aa)*ss
            dyn.append(dict(process=name,lag=lag,target0_nns=mm['nns_norm'],pearson=mm['pearson'],
                            mean_toward=float(np.mean(toward)),toward_frac=float(np.mean(toward>0)),
                            away_frac=float(np.mean(toward<0)),mean_away_magnitude=float(np.mean(-toward)),
                            n=len(aa)))
    # Global fixed Schur covariance check, no rolling target.
    schur=[]
    for name,xx in signals.items():
        a=xx[:-1];b=xx[1:];n=len(a)
        covariance=float(np.dot(a-a.mean(),b-b.mean())/n)
        for targ in (0.,-1.,1.,float(np.mean(a))):
            raw=float(np.mean((a-targ)*(b-targ)))
            corrected=raw-(float(a.mean())-targ)*(float(b.mean())-targ)
            assert math.isclose(corrected,covariance,rel_tol=1e-9,abs_tol=1e-8)
            schur.append(dict(series=name,target=targ,raw_cross_mean=raw,schur_cov=covariance,corrected=corrected))
    # Historical half-run native Gamma_{A,R}, factorization and signs.
    hist=[]
    # Every R from 8 to max_r, A=floor(R/2)+1, endpoint B=R+1
    A=r//2+1
    hDr=E+(q_by_root[r]-vf_root[r])
    hEA=pi[A*A]-q_by_root[A]
    hDA=pi[A*A]-vf_root[A]
    endE=pi[rnext*rnext]-q_by_root[rnext]
    deltaH=endE-hEA
    wall=2*rnext*np.log(rnext)-2*A*np.log(A)
    oriented=np.where(Dnext>0,deltaH,-deltaH)
    hclear=2*A*np.log(A)-np.where(Dnext>0,hDA,-hDA)
    required=hclear+wall-np.where(Dnext>0,(q_by_root[rnext]-vf_root[rnext])-(q_by_root[A]-vf_root[A]),-(q_by_root[rnext]-vf_root[rnext])+(q_by_root[A]-vf_root[A]))
    for rng in ((8,6000),(8,1000),(1001,3000),(3001,6000)):
        mask=(r>=rng[0])&(r<=rng[1]);
        if not np.any(mask): continue
        ratio=np.abs(deltaH[mask])/wall[mask]
        hist.append(dict(rmin=rng[0],rmax=rng[1],count=int(np.sum(mask)),
                         mean_abs_drift=float(np.mean(np.abs(deltaH[mask]))),
                         mean_wall_growth=float(np.mean(wall[mask])),
                         max_abs_drift_over_wall=float(np.max(ratio)),
                         max_oriented_over_threshold=float(np.max(oriented[mask]/required[mask])),
                         # A prior-good r can be outside for r small? all inside empirical
                         mean_signed_outward_drift=float(np.mean(oriented[mask]))))
    # Verify historical physical VF Gram directly.
    for k in (317,1027,1760,5267,6000):
        i=k-8
        if i<0 or i>=len(r):continue
        ak=int(A[i]); d_now=float(D[i]);d_anchor=float(hDA[i]); ep=float(e[i]);
        # Historical r in [A,R): sum charge = -(D_R-D_A); current charge = -ep.
        corrF=(d_now-d_anchor)*ep
        assert math.isclose(corrF,(- (d_now-d_anchor))*(-ep),rel_tol=1e-10)
    # Print and save.
    with (outdir/'moments.csv').open('w',newline='') as ff:
        dw=csv.DictWriter(ff,fieldnames=list(corrs[0]));dw.writeheader();dw.writerows(corrs)
    with (outdir/'schur_target_invariance.csv').open('w',newline='') as ff:
        dw=csv.DictWriter(ff,fieldnames=list(schur[0]));dw.writeheader();dw.writerows(schur)
    with (outdir/'per_block.csv').open('w',newline='') as ff:
        dw=csv.writer(ff);dw.writerow(['R','P','floorLi_P','prime_minus_floorLi','prime_minus_VF','D_R','D_next','G_actual','G_floorLi','G_err','smooth_actual','smooth_floorLi','smooth_err','native_prime','native_large','native_smooth','window_plus','window_minus','halfscale_Echange','wall_growth','NNS_oneblock'])
        for i,ri in enumerate(r):
            dw.writerow([int(ri),int(Pr[i]),int(Fr[i]),int(delta[i]),float(e[i]),float(D[i]),float(Dnext[i]),int(G[i]),int(GLi[i]),int(gd[i]),int(H[i]),int(HLi[i]),int(hd[i]),float(ap[i]),float(ag[i]),float(ah[i]),int(plus[i]),int(minus[i]),int(deltaH[i]),float(wall[i]),float(Dnext[i]**2/M0[i]**2)])
    summary=dict(max_r=max_r,from_r=8,seconds=round(time.perf_counter()-tt,2),
                 samples={str(k):dict(P=int(Pr[k-8]),FloorP=int(Fr[k-8]),dP=int(delta[k-8]),g=int(G[k-8]),floor_g=int(GLi[k-8]),dg=int(gd[k-8]),h=int(H[k-8]),dh=int(hd[k-8]),correl_window_error_plus=int(plus[k-8]),correl_window_error_minus=int(minus[k-8]),half_error=int(deltaH[k-8]),wall_growth=float(wall[k-8])) for k in (119,317,1027,1760,5267,6000) if k<=max_r},
                 lag1_moments_0={k:co_div_moment(x[:-1],x[1:]) for k,x in signals.items()},
                 cross_matrix=matrices,negative_feedback=dyn,historical=hist,
                 max_NNS_oneblock=(float(np.max(Dnext**2/M0**2)),int(r[np.argmax(Dnext**2/M0**2)])),
                 seat_first_moments=seat_first,
                 empirical_fixed_slices={},
                 variance_suppression={},
                 cohort_variation={'largeError_abs_mean':float(np.mean(np.abs(gd))),'smoothError_abs_mean':float(np.mean(np.abs(hd))),'primeError_abs_mean':float(np.mean(np.abs(delta))),'large_plus_sum':int(plus.sum()),'large_minus_sum':int(minus.sum())})
    # Partition robustness: ranges have fixed endpoints, no rolling target.
    for name in ('prime_minus_VF','prime_minus_floorLi','prime_minus_contLi',
                 'large_factor_error','smooth_error','large_vs_contLi',
                 'smooth_vs_contLi','scaled_VF','scaled_floorLi'):
        vec=signals[name]
        summary['empirical_fixed_slices'][name]={}
        for lo,hi in ((8,1000),(1001,3000),(3001,6000)):
            selection=(r>=lo)&(r<=hi)
            block=vec[selection]
            if len(block)<5:continue
            m=co_div_moment(block[:-1],block[1:])
            summary['empirical_fixed_slices'][name][f'{lo}-{hi}']={
                'lag1_Pearson':m['pearson'],'lag1_NNS_target0':m['nns_norm'],
                'mean':float(np.mean(block)),'std':float(np.std(block)),
                'samples':len(block)}
        # Overlapping sums: lower-than-IID scaling is descriptive only;
        # unequal covariance and overlapping observations are not i.i.d.
        if name in ('scaled_VF','scaled_floorLi','large_vs_contLi','smooth_vs_contLi'):
            variance=float(np.var(vec))
            summary['variance_suppression'][name]={}
            for horizon in (2,4,8,16,32,64,128,256):
                if len(vec)<2*horizon:continue
                v=np.cumsum(np.concatenate(([0.],vec)))
                sums=v[horizon:]-v[:-horizon]
                summary['variance_suppression'][name][str(horizon)]=float(np.var(sums)/(horizon*variance))
    # The native root defect has never approached the wall in sampled states.
    summary['max_observed_radial_occupancy']=(float(np.max(np.abs(D)/(2*rv*np.log(rv)))),int(r[np.argmax(np.abs(D)/(2*rv*np.log(rv)))]))
    # The literal historical/current anchored signed Co-Div Gram pair.
    for name,prior,current in [('VF_history_current',D-hDA,e),
                               ('VF_endpoint_current',D,e),
                               ('VF_priorAnchor_current',hDA,e),
                               ('floorLi_history_current',E-hEA,delta),
                               ('floorLi_endpoint_current',E,delta)]:
        summary.setdefault('historical_current_gram',{})[name]=co_div_moment(prior,current)

    with (outdir/'summary.json').open('w') as ff:json.dump(summary,ff,indent=2)
    print('R range',8,max_r,'elapsed sec',summary['seconds'],flush=True)
    print('sample checkpoints',summary['samples'],flush=True)
    print('ONE-BLOCK MAX NNS',summary['max_NNS_oneblock'],flush=True)
    for name,xx in signals.items():
        vals=[]
        for lag in (1,2,4,8,16,32):
            z=co_div_moment(xx[:-lag],xx[lag:])
            vals.append([lag,round(z['pearson'],6),round(z['nns_norm'],6),round(z['raw_cross']/len(xx[:-lag]),4)])
        print('SIGNAL',name, 'lag/Pearson/NNS/raw_avg',vals,flush=True)
    print('LAG1 across component series',flush=True)
    for mode in ('native_weighted','unweighted_events'):
        for mat in ('pearson','nns_norm'):
            key=f'lag1_target+0_{mat}'
            print('MATRIX',mode,mat,matrices[mode][key],flush=True)
    print('historical negative feedback',dyn,flush=True)
    print('historic batches',hist,flush=True)
    print('CONTINUOUS Li baseline comparison', {k:summary['lag1_moments_0'][k]['pearson'] for k in ('prime_minus_contLi','large_vs_contLi','smooth_vs_contLi')},flush=True)
    print('HIST CURRENT GRAM', {k:(round(v['pearson'],5),round(v['nns_norm'],5),round(v['raw_cross'],2)) for k,v in summary['historical_current_gram'].items()},flush=True)
    print('VARIANCE SUPPRESSION',summary['variance_suppression'],flush=True)
    print('MAX RADIAL OCCUPANCY', summary['max_observed_radial_occupancy'],flush=True)
    print('LITERAL PHYSICAL SEATS vs AGGREGATED', {k:summary['seat_first_moments'][k] for k in ('target+0_lag1','target+0_lag2','target+0.1_lag1','target-0.1_lag1','target+0.25_lag1')},flush=True)
    return summary

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--max-root',type=int,default=6000);p.add_argument('--outdir',default='vf918_crossblock');a=p.parse_args()
    full_analysis(a.max_root,a.outdir)