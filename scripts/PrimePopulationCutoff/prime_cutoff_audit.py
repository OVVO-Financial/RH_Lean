#!/usr/bin/env python3
"""Exact fixed-endpoint prime-by-prime Mobius prime-candidate reconstruction.

Implements the actual Lean PrimeCombVisualizationFrames.lean state:
  n=1: +1; n>=2 with no selected divisor: -1
  selected square factor: 0
  otherwise: (-1)^(number selected distinct prime divisors)

Also tracks the separate smooth-number population generated from Euler
1/zeta, without confusing it with the prime-candidate animation.

For p>sqrt(x), use the *proved* post-root delta 2(1-M(floor(x/p))).
Exact integer checks include a direct site state reconstruction and
post-root corrections.  Does not prove a uniform finite C/A bound.
"""
import argparse
import csv
import json
from array import array
from collections import defaultdict
from math import isqrt, sqrt, ceil
from pathlib import Path
import numpy as np


def mobius_sieve(N):
    spf = array('i',[0])*(N+1)
    mu = array('b',[0])*(N+1)
    omega = array('b',[0])*(N+1)
    greatest = array('i',[0])*(N+1)
    primes=[]
    mu[1]=1
    for n in range(2,N+1):
        if spf[n]==0:
            spf[n]=n
            greatest[n]=n
            mu[n]=-1
            omega[n]=1
            primes.append(n)
        for p in primes:
            k=n*p
            if k>N or p>spf[n]:
                break
            spf[k]=p
            greatest[k]=greatest[n] if greatest[n]>p else p
            if p==spf[n]:
                mu[k]=0
                omega[k]=omega[n]
                break
            mu[k]=-mu[n]
            omega[k]=omega[n]+1
    prefM=array('i',[0])*(N+1)
    prefQ=array('i',[0])*(N+1)
    for n in range(1,N+1):
        prefM[n]=prefM[n-1]+mu[n]
        prefQ[n]=prefQ[n-1]+(mu[n]!=0)
    return primes,spf,mu,omega,greatest,prefM,prefQ


def first_ge_prime(primes,k):
    from bisect import bisect_left
    t=bisect_left(primes,k)
    return primes[t] if t<len(primes) else None


def last_le_prime(primes,k):
    from bisect import bisect_right
    t=bisect_right(primes,k)-1
    return primes[t] if t>=0 else None


def phase(root,x, primes,spf,mu,omega,greatest,M,Q,write_dir, full_rows):
    title=str(x)
    xmu=np.frombuffer(mu,dtype=np.int8,count=x+1)
    state=np.full(x+1,-1,dtype=np.int8)
    state[0]=0
    state[1]=1
    touched=np.zeros(x+1,dtype=np.bool_)
    current=2-x
    positive=1
    negative=x-1
    zeros=0
    correct=int(1+np.count_nonzero(xmu[2:] == -1))
    final=int(M[x]); sf=int(Q[x]); root=isqrt(x)
    running_smooth=1
    # Signed Euler smooth additions indexed by greatest-prime owner.
    by_owner=defaultdict(int)
    by_owner_degree=defaultdict(lambda:defaultdict(int))
    for n in range(2,x+1):
        if mu[n]:
            t=int(greatest[n])
            by_owner[t]+=mu[n]
            by_owner_degree[t][omega[n]]+=1
    rows=[]
    parity_orphans=[]
    prev_x=x
    req95=ceil(0.95*x)
    req99=ceil(0.99*x)
    last_active=last_le_prime(primes,x//2)
    last_square_kill=last_le_prime(primes,root)
    def addrow(p, phase_name, delta, delta_correct, count_changed, newly_zero, nseats, plus_to_minus, minus_to_plus, stage):
        rows.append(dict(x=x,step=stage,prime=p,phase=phase_name,delta=int(delta),step_misfit=int(current-final),
                         candidate_sum=int(current),true_M=int(final),positive=int(positive),
                         negative=int(negative),zero=int(zeros),correct=int(correct),
                         incorrect=int(x-correct),fraction_correct=float(correct/x),
                         signed_to_support=float(abs(current)/(positive+negative)) if positive+negative else 0,
                         smooth_sum=int(running_smooth),smooth_residual=int(final-running_smooth),
                         changed_sites=int(count_changed),new_zeros=int(newly_zero),
                         potential_seats=int(nseats),positive_to_negative=int(plus_to_minus),negative_to_positive=int(minus_to_plus)))
    addrow(1,'seed',0,0,0,0,0,0,0,0)
    stage=0
    for p in primes:
        if p>x:
            break
        stage+=1
        smooth_add=by_owner.get(p,0)
        running_smooth+=smooth_add
        if p<=root:
            ns=np.arange(p,x+1,p,dtype=np.int32)
            before=state[ns]
            sq=(ns%(p*p)==0)
            alive=before!=0
            was_touched=touched[ns]
            after=np.where(sq,0,np.where(was_touched & alive,-before,before)).astype(np.int8)
            # sanity: prime site itself never gets its provisional sign changed
            assert after[0] == -1
            plus_to_minus=int(np.count_nonzero((before==1)&(after==-1)))
            minus_to_plus=int(np.count_nonzero((before==-1)&(after==1)))
            delta=int(np.sum(after,dtype=np.int64)-np.sum(before,dtype=np.int64))
            newly_zero=int(np.count_nonzero((before!=0)&(after==0)))
            delta_correct=int(np.count_nonzero(after==xmu[ns])-np.count_nonzero(before==xmu[ns]))
            count_changed=int(np.count_nonzero(before!=after))
            state[ns]=after
            touched[ns]=True
            current+=delta
            positive+=int(np.count_nonzero(after==1)-np.count_nonzero(before==1))
            negative+=int(np.count_nonzero(after==-1)-np.count_nonzero(before==-1))
            zeros+=newly_zero
            correct+=delta_correct
            phase_name='root-primes'
            if p==last_square_kill:
                assert zeros==x-Q[x], (x,p,zeros,x-Q[x])
        elif p<=x//2:
            k=x//p
            # all k-cofactors are already finalized.  Fresh p flips every
            # *squarefree proper multiple* and corrects its frame entry.
            delta=2*(1-int(M[k]))
            delta_correct=int(Q[k]-1)
            count_changed=delta_correct
            newly_zero=0
            plus_to_minus=sum(1 for c in range(2,k+1) if mu[c]==1)
            minus_to_plus=sum(1 for c in range(2,k+1) if mu[c]==-1)
            assert delta == 2*(minus_to_plus-plus_to_minus)
            current+=delta
            positive+=minus_to_plus-plus_to_minus
            negative+=plus_to_minus-minus_to_plus
            correct+=delta_correct
            phase_name='post-root'
        else:
            delta=0
            delta_correct=0
            count_changed=0
            newly_zero=0
            plus_to_minus=minus_to_plus=0
            phase_name='inert-candidate'
        addrow(p,phase_name,delta,delta_correct,count_changed,newly_zero,max(x//p-1,0),plus_to_minus,minus_to_plus,stage)
        assert positive+negative+zeros==x
        if full_rows:
            pass
        if p==last_active:
            assert current==final and correct==x and zeros==x-Q[x], (x,p,current,final,correct,x,zeros,x-Q[x])
        if p==last_square_kill:
            # Validate full frame at root stage independently at all n.
            exact_check=0
            for n in range(1,x+1):
                val=1 if n==1 else -1
                if n>1:
                    selected=[]
                    rem=n
                    for q in primes:
                        if q>p or q*q>n and q>p:
                            break
                        if q>p:break
                        if n%q==0:
                            selected.append(q)
                            if n%(q*q)==0:
                                val=0
                                break
                    else:
                        pass
                    if val!=0 and selected:
                        val=(-1)**len(selected)
                if val==xmu[n]:
                    exact_check+=1
            assert exact_check==correct,(x,p,correct,exact_check)
    assert current==final and correct==x and running_smooth==final
    # The final candidate phase may be reached before the last prime x but
    # every p>x/2 is inert; smooth mass keeps falling as primes are added.
    def first_when(pred):
        z=next((r for r in rows if pred(r)),None)
        return z['prime'] if z else None
    def permanent_first(predicate):
        t=len(rows)-1
        while t>=0 and predicate(rows[t]):
            t-=1
        return rows[t+1]['prime'] if t+1<len(rows) else None
    rroot=next(r for r in rows if r['prime']==last_square_kill)
    last_act_row=next(r for r in rows if r['prime']==last_active)
    first90=first_when(lambda r:r['correct']>=0.90*x)
    first95=first_when(lambda r:r['correct']>=req95)
    first99=first_when(lambda r:r['correct']>=req99)
    near=first_when(lambda r:abs(r['candidate_sum']-final)<=max(2,isqrt(x)))
    first_signed=first_when(lambda r:abs(r['candidate_sum'])<=max(2,isqrt(x)))
    exactfirst=first_when(lambda r:r['candidate_sum']==final)
    lastwrong=permanent_first(lambda r:r['candidate_sum']==final)
    last_correct_site=permanent_first(lambda r:r['correct']==x)
    # smooth mass against the distinct high-prime sector after root cutoff
    smooth_root=int(rroot['smooth_sum']); high_root=final-smooth_root
    post_delta=final-rroot['candidate_sum']
    sum_abs_post=sum(abs(r['delta']) for r in rows if r['phase']=='post-root')
    sum_sq_post=sum(r['delta']**2 for r in rows if r['phase']=='post-root')
    neg_post=sum(r['delta']<0 for r in rows if r['phase']=='post-root')
    pos_post=sum(r['delta']>0 for r in rows if r['phase']=='post-root')
    zero_post=sum(r['delta']==0 for r in rows if r['phase']=='post-root')
    last_tail=last_le_prime(primes,x//3)
    count_tail=sum(r['phase']=='post-root' and r['prime']>x/3 for r in rows)
    tail_sum=sum(r['delta'] for r in rows if r['phase']=='post-root' and r['prime']>x/3)
    # above x/3 the only proper child is 2p: delta=+2
    assert tail_sum==2*count_tail
    assert all(r['delta']==2 for r in rows if r['phase']=='post-root' and r['prime']>x/3)
    square_endpoint=(isqrt(x+1)**2 == x+1)
    out=dict(x=x,root=isqrt(x),square_endpoint=square_endpoint,prime_count_to_x=sum(p<=x for p in primes),
             last_square_kill_prime=last_square_kill,last_active_prime=last_active,
             true_M=final,true_nonzero=sf, true_zero=x-sf,
             root_stage_sum=rroot['candidate_sum'],root_stage_correct=rroot['correct'],
             root_stage_errors=rroot['incorrect'],root_stage_positive=rroot['positive'],
             root_stage_negative=rroot['negative'],root_stage_zero=rroot['zero'],
             root_smooth_mass=smooth_root,root_large_prime_mass=high_root,
             total_post_root_correction=post_delta,sum_abs_post_corrections=sum_abs_post,
             sum_sq_post_corrections=sum_sq_post,
             root_to_final_cancellation=1-abs(final)/(abs(rroot['candidate_sum'])+abs(post_delta)) if abs(rroot['candidate_sum'])+abs(post_delta) else 0,
             post_root_positive_steps=pos_post,post_root_negative_steps=neg_post,post_root_zero_steps=zero_post,
             min_sign_to_support=min(r['signed_to_support'] for r in rows),
             first_90_correct_prime=first90,first_95_correct_prime=first95,first_99_correct_prime=first99,
             first_near_final_prime=near,first_low_signed_sum_prime=first_signed,
             first_exact_signed_prime=exactfirst,first_permanent_exact_prime=lastwrong,
             first_permanent_all_sites_prime=last_correct_site,
             tail_prime_count=count_tail,tail_exact_correction=tail_sum)
    if square_endpoint:
        R=isqrt(x+1)
        K=max((M[y]-1)**2/(y+1) for y in range(R))
        Qval=2*M[R-1]-final
        out.update(Q=Qval,K=K,C=abs(Qval)/(R*sqrt(K)),A=(final-1)**2/(R*R*K))
        for r in rows:
            r['stage_Q']=2*M[R-1]-r['candidate_sum']
            r['stage_C_proxy']=abs(r['stage_Q'])/(R*sqrt(K))
    with open(write_dir/f'prime_steps_x{x}.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    return out,rows


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--values',type=int,nargs='+',default=[30,210,288,317,1023,1027,3135,9999,100488,999999])
    ap.add_argument('--outdir',type=Path,default=Path(__file__).resolve().parent)
    args=ap.parse_args()
    args.outdir.mkdir(exist_ok=True,parents=True)
    xs=sorted(set(args.values))
    primes,spf,mu,omega,greatest,M,Q=mobius_sieve(max(xs))
    results=[]
    selected_rows={}
    for x in xs:
        summary,rows=phase(isqrt(x),x,primes,spf,mu,omega,greatest,M,Q,args.outdir,False)
        results.append(summary)
        if x in (30,210,288,317,1023,1027,3135,9999,100488,999999):
            selected_rows[str(x)]=[
                row for row in rows if row['prime'] in (1,2,3,5,7,11,13,17,19,23,29,31,37,43,47,53,67,83,97,101,107,127,149,157,173,191,223,251,317,331,401,499,509,997,1009,2003,10007,20011)
                or row['prime'] in (summary['last_square_kill_prime'],summary['last_active_prime'],summary['first_95_correct_prime'],summary['first_99_correct_prime'],summary['first_near_final_prime'],summary['first_exact_signed_prime'])
            ]
        print('x',x,'root',summary['last_square_kill_prime'],'last',summary['last_active_prime'],'M',summary['true_M'],
              'Jroot',summary['root_stage_sum'],'correct',summary['root_stage_correct'],
              'last_correct',summary['first_permanent_all_sites_prime'],'neg_steps',summary['post_root_negative_steps'])
    with open(args.outdir/'cutoff_summary.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(dict.fromkeys(k for item in results for k in item)),extrasaction='ignore');w.writeheader();w.writerows(results)
    with open(args.outdir/'cutoff_summary.json','w') as f:json.dump({'summary':results,'selected_rows':selected_rows},f,indent=2)
    with open(args.outdir/'mobius_factor_depth_x317_x1027.csv','w',newline='') as f:
        w=csv.writer(f);w.writerow(['x','prime_cutoff','smooth_omega','signed_mu_contribution','count'])
        for x in (317,1027):
            for p in primes:
                if p>x:break
                ss=defaultdict(lambda:[0,0])
                for n in range(2,x+1):
                    if mu[n]!=0 and greatest[n]==p:
                        ss[omega[n]][0]+=1;ss[omega[n]][1]+=mu[n]
                for d,(ct,net) in ss.items():
                    w.writerow([x,p,d,net,ct])
    print('complete summaries',len(results))

if __name__=='__main__':main()
