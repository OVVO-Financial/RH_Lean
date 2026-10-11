#!/usr/bin/env python3
"""Exact Fubini conditioning of post-root prime-extension Gram by gcd ancestry.

For c,d>=2 squarefree and p>sqrt(x), extension availability is nested:
N_y(c,d) = #{prime p: sqrt(x)<p<=min(y, x/max(c,d))}.
Signed covariance with c<d is separated by gcd(c,d)>1 versus =1.
The identities are integer exact for every increasing prime-population cutoff.
"""
import csv
import json
from math import gcd, isqrt
from pathlib import Path
from prime_cutoff_audit import mobius_sieve

DIR=Path('/mnt/data/prime_cutoff_experiment')

def main():
    xs=[30,210,288,317,1023,1027,3135,9215,9999,100488,999999]
    primes,spf,mu,omega,gr,M,Q=mobius_sieve(max(xs))
    extended_summaries=[]
    for x in xs:
        r=isqrt(x)
        # One-prime extension c=1 belongs to the prime singleton seat and
        # is deliberately excluded: candidate updates change only proper multiples.
        D=[0]*(r+1);S=[0]*(r+1);C=[0]*(r+1)
        count_sf=0
        for d in range(2,r+1):
            if mu[d]==0:continue
            D[d]=1
            for c in range(2,d):
                if mu[c]==0:continue
                v=mu[c]*mu[d]
                if gcd(c,d)>1:S[d]+=v
                else:C[d]+=v
        for k in range(1,r+1):
            D[k]+=D[k-1];S[k]+=S[k-1];C[k]+=C[k-1]
            if k>=2:
                assert D[k]+2*(S[k]+C[k])==(M[k]-1)**2, (x,k,D[k],S[k],C[k],M[k]-1)
        cs=co=diag=sum_sq=sum_delta=0
        rows=[]; npos=nneg=nzero=0
        for p in primes:
            if p<=r:continue
            if p>x//2:break
            k=x//p
            ds= S[k]
            dc= C[k]
            dd= D[k]
            dsigned=2*(1-M[k])
            cs+=ds;co+=dc;diag+=dd;sum_sq+=(M[k]-1)**2
            sum_delta+=dsigned
            assert diag+2*(cs+co)==sum_sq,(x,p,k,diag,cs,co,sum_sq)
            if dsigned>0:npos+=1
            elif dsigned<0:nneg+=1
            else:nzero+=1
            rows.append(dict(x=x,prime=p,k=k,delta=dsigned,total_correction=sum_delta,
                     cofactor_square_energy=sum_sq,diagonal=diag,shared_gcd_signed_overlap=cs,
                     coprime_signed_overlap=co,combined_signed_overlap=cs+co,
                     shared_over_diagonal=cs/diag if diag else 0,
                     coprime_over_diagonal=co/diag if diag else 0,
                     count_pos=npos,count_neg=nneg,count_zero=nzero))
        assert rows[-1]['total_correction'] if rows else True
        with open(DIR/f'ancestry_prefix_x{x}.csv','w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
        checkpoints={}
        special=[r,2*r,x//95,x//10,x//3,x//2]
        for cutoff in special:
            q=[row for row in rows if row['prime']<=cutoff]
            if q:
                item=q[-1]
                checkpoints[str(cutoff)]={z:item[z] for z in ['prime','total_correction','cofactor_square_energy','diagonal','shared_gcd_signed_overlap','coprime_signed_overlap','count_pos','count_neg','count_zero']}
        if rows:
            posshared=[a for a in rows if a['shared_gcd_signed_overlap']>0]
            negshared=[a for a in rows if a['shared_gcd_signed_overlap']<0]
            lastpositive=posshared[-1]['prime'] if posshared else None
            firstnegative=negshared[0]['prime'] if negshared else None
            lastnegative=next((a['prime'] for a in rows[::-1] if a['delta']<0),None)
            peak=max(rows,key=lambda a:abs(a['shared_gcd_signed_overlap']))
            s=dict(x=x,r=r,postroot_primes=len(rows),postroot_positive=npos,postroot_negative=nneg,
                   first_shared_negative_prime=firstnegative,last_shared_positive_prime=lastpositive,
                   last_negative_update_prime=lastnegative,
                   final_shared_overlap=cs,final_coprime_overlap=co,final_diagonal=diag,
                   final_gram=diag+2*(cs+co),sum_delta=sum_delta,
                   shared_fraction_of_total_signed_overlap=cs/(cs+co) if cs+co else None,
                   prime_largest_shares_peak=peak['prime'],peak_shared=peak['shared_gcd_signed_overlap'],
                   checkpoints=checkpoints)
        else:s=dict(x=x,r=r)
        extended_summaries.append(s)
        print('x',x,'postroot',len(rows),'signs',npos,nneg,'shared',cs,'coprime',co,'diag',diag,'gram',sum_sq,
              'first shared<0',s.get('first_shared_negative_prime'),'last shared>0',s.get('last_shared_positive_prime'),
              'last bad update',s.get('last_negative_update_prime'))
    with open(DIR/'ancestry_cutoff_summary.json','w') as f:json.dump(extended_summaries,f,indent=2)
    with open(DIR/'ancestry_cutoff_summary.csv','w',newline='') as f:
        omit={'checkpoints'}
        w=csv.DictWriter(f,fieldnames=[k for k in extended_summaries[-1] if k not in omit]);w.writeheader()
        for s in extended_summaries:w.writerow({k:v for k,v in s.items() if k not in omit})

if __name__=='__main__': main()
