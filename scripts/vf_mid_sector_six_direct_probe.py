#!/usr/bin/env python3
"""Direct, arithmetic-carrier numerical tests of RH_Lean sector six and #915.

Test A: The literal recursive *sector-six* priority remainder from
research/VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean, carrying the
Dirichlet polarization atom of the real AMP model. This is the genuine
#903 recursive sector, not the #915 anchored partial-moment state.

Test B: The literal #915 *active returned raw-parent* packet, with VF site
charges and full multiplicities, classified into the six chronological/oriented
boundary sectors. This is the weighted boundary that #915 has to pay, not an
inferred sector-six UPM/LPM child-run state.

Numerically tests carrier/Fubini identities. Explicitly does NOT construct a
matched full child-run production of anchored U/L, which has not been specified
by a proved source-to-child positive-mass map.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from collections import defaultdict, Counter
from dataclasses import dataclass, field
from itertools import combinations
from pathlib import Path


@dataclass
class PairLedger:
    positive: float = 0.0
    negative: float = 0.0
    count: int = 0
    pos_count: int = 0
    neg_count: int = 0
    zero_count: int = 0
    def add(self, z: float):
        self.count += 1
        if z > 1e-13:
            self.positive += z
            self.pos_count += 1
        elif z < -1e-13:
            self.negative -= z
            self.neg_count += 1
        else:
            self.zero_count += 1
    @property
    def signed(self): return self.positive - self.negative
    @property
    def absolute(self): return self.positive + self.negative
    @property
    def B(self):
        U,L=self.positive,self.negative
        return 6*U*L-U*U-L*L
    @property
    def normalized(self):
        return (self.signed/self.absolute)**2 if self.absolute else 0.0
    def as_dict(self):
        return dict(count=self.count,positive_count=self.pos_count,negative_count=self.neg_count,
                    zero_count=self.zero_count,U=self.positive,L=self.negative,
                    signed=self.signed,absolute=self.absolute,B=self.B,ratio=self.normalized,
                    cone=self.B >= -1e-8 * max(1.0,self.absolute**2))


class Arithmetic:
    def __init__(self, N: int):
        self.N=N
        self.spf=[0]*(N+1)
        for p in range(2,math.isqrt(N)+1):
            if not self.spf[p]:
                for k in range(p*p,N+1,p):
                    if not self.spf[k]: self.spf[k]=p
        self._factor_cache={1:frozenset()}
        self._prime_list=[i for i in range(2,N+1) if self.spf[i]==0]
    def prime(self,n: int)->bool: return n>=2 and self.spf[n]==0
    def factors(self,n:int)->frozenset[int]:
        if n in self._factor_cache:return self._factor_cache[n]
        initial=n
        res=set()
        while n>1:
            p=self.spf[n] or n
            if p in res:return None  # squareful: not on physical Mobius carrier
            res.add(p)
            n//=p
            if n%p==0:return None
        ans=frozenset(res)
        self._factor_cache[initial]=ans
        return ans
    def mobius(self,n):
        f=self.factors(n)
        return 0 if f is None else (-1 if len(f)%2 else 1)
    def primes_to(self,X):
        return (p for p in self._prime_list if p<=X)


def amp_weight(a:Arithmetic,R:int,n:int)->float:
    W=R*R-1
    total=float(n>=R)
    for q in a.primes_to(R-1):
        if q<=2: continue
        if q*q>=R:break
        if n<=W//(q*q):total+=1/q
    return total


def amp_pair_polarization(a:Arithmetic,R:int,p:int,x:int,y:int)->float:
    # Dirichlet zero extension. Both p*x and p*y <= W in the #903 admitted branch.
    mua=a.mobius(x)
    muy=a.mobius(y)
    wx,wy=amp_weight(a,R,x),amp_weight(a,R,y)
    wpx,wpy=amp_weight(a,R,p*x),amp_weight(a,R,p*y)
    return -(mua*muy)*(wx*wpy+wpx*wy)


def common_postroot_family(a:Arithmetic,W:int,x:int,y:int)->bool:
    # Lean: postRootPrimePhysicalPairUnion W is any common prime q>sqrt W.
    if not(1<=x<y<=W):return False
    fx,fy=a.factors(x),a.factors(y)
    if fx is None or fy is None:raise AssertionError('postRoot tests only squarefree sites')
    return any(q>math.isqrt(W) for q in fx&fy)


def equal_after_first_strip(a:Arithmetic,x:int,y:int)->bool:
    dx=a.factors(x)^a.factors(y)
    if not dx:return False
    p=min(dx)
    return (x//p if x%p==0 else x) == (y//p if y%p==0 else y)


def class_903(a:Arithmetic,W:int,x:int,y:int,r:int):
    # This is literally the ordered filters of #903:
    # 1 current-family / 2 equal-r-parent / 3 clipped-r / 4 lower-family /
    # 5 lower-terminal / 6 recursive remainder.
    if common_postroot_family(a,W,x,y):return '01_current_family',None
    u=x//r if x%r==0 else x
    v=y//r if y%r==0 else y
    if u==v:return '02_equal_parent',None
    lo,hi=sorted((u,v))
    if W<r*hi:return '03_clipped',None
    Q=W//r
    assert hi<=Q, (W,r,u,v)
    if common_postroot_family(a,Q,lo,hi):return '04_lower_family',(lo,hi)
    if equal_after_first_strip(a,lo,hi):return '05_lower_terminal',(lo,hi)
    return '06_recursive',(lo,hi)


def sector_six_903(a:Arithmetic,R:int,W:int)->dict:
    # `R` is the AMP's first argument, `W` is the physical clock.
    # Production agreement requires W=R^2-1.
    assert R>=4 and 2<=W<a.N
    total=PairLedger()
    sectors=defaultdict(PairLedger)
    grouped=defaultdict(PairLedger)
    by_child_clock=defaultdict(PairLedger)
    by_child_owner=defaultdict(PairLedger)
    child_occurrences=defaultdict(int)
    bad_fine=[]
    root_recurrences=0
    for p in a.primes_to(math.isqrt(W)):
        sigmap=defaultdict(list)
        # admitted first-owner p-free a with p*a<=W
        for x in range(1,W//p+1):
            fx=a.factors(x)
            if fx is None or p in fx:continue
            sig=tuple(sorted(q for q in fx if q<p))
            sigmap[sig].append((x,fx))
        for sig,points in sigmap.items():
            if len(points)<2:continue
            for (x,fx),(y,fy) in combinations(points,2):
                diff=fx^fy
                if not diff:raise AssertionError('same squarefree prime set for distinct numbers')
                r=max(diff)
                assert r>p, (p,r,x,y)
                z=amp_pair_polarization(a,R,p,x,y)
                label,parent=class_903(a,W,x,y,r)
                total.add(z)
                sectors[label].add(z)
                if label=='06_recursive':
                    root_recurrences+=1
                    grouped[(p,sig,r)].add(z)
                    by_child_clock[W//r].add(z)
                    by_child_owner[r].add(z)
                    child_occurrences[(p,sig,r,parent)]+=1
                    assert a.factors(parent[0])^a.factors(parent[1]) == diff-{r}, (p,r,x,y,parent)
    for key,led in grouped.items():
        if led.B< -1e-8 * max(1.0,led.absolute**2):
            if len(bad_fine)<12:bad_fine.append({'key':repr(key),'state':led.as_dict()})
    sec6=sectors['06_recursive']
    by_clock=[{'child_clock':clock,**v.as_dict()} for clock,v in sorted(by_child_clock.items())]
    return {
        'carrier':'literal_#903_sector_six_Dirichlet_polarization',
        'R':R,'W':W,'production':W==R*R-1,
        'all_admitted_positive_pairs':total.as_dict(),
        'six_sectors':{k:v.as_dict() for k,v in sorted(sectors.items())},
        'recursive_sector_six_total':sec6.as_dict(),
        'recursive_by_child_clock':by_clock,
        'recursive_by_r':[{'greatest_owner':r,**v.as_dict()} for r,v in sorted(by_child_owner.items())],
        'fine_cell_groups':len(grouped),
        'fine_cell_cone_failures':sum(v.B < -1e-8*max(1.0,v.absolute*v.absolute) for v in grouped.values()),
        'fine_cell_failure_samples':bad_fine,
        'raw_parent_occurrences':len(child_occurrences),
        'raw_parent_max_multiplicity':max(child_occurrences.values(),default=0),
        'raw_parent_mult_hist':dict(Counter(child_occurrences.values()))
    }


def class_915(W:int,p:int,r:int,parent:tuple[int,int])->str:
    # Exactly the six ordered classes of #914/#915; the input is an occurring
    # raw parent from the full greatest-owner fibre. Active retained sources
    # are all incomplete.
    x,y=parent
    if p*x>W or p*y>W:
        return 'first_left' if p*x>W else 'first_right'
    if r*x>W or r*y>W:
        return 'next_left' if r*x>W else 'next_right'
    if p*r*x>W or p*r*y>W:
        return 'returned_left' if p*r*x>W else 'returned_right'
    return 'completed'


def returned_weighted_915(a:Arithmetic,R:int)->dict:
    W=(R+1)*(R+1)-1
    V=(2*R+1)/math.log(R*R+R+0.5)
    w=V/R
    # exactly R odd seats of the open square block; squareful are omitted from
    # #915 active physical field, with their mass treated separately.
    active=[]
    composites=primes=omitted=0
    odd_start=R*R+1
    if odd_start%2==0:odd_start+=1
    for n in range(odd_start,W+1,2):
        f=a.factors(n)
        if f is None:
            omitted+=1
            continue
        isprime=len(f)==1 and n in f
        if isprime:primes+=1
        else:composites+=1
        z=w-(1.0 if isprime else 0.0)
        active.append((n,f,z))
    assert len(active)+omitted==R
    original_unordered=PairLedger()
    recovered=PairLedger()
    sectors=defaultdict(PairLedger)
    per_r=defaultdict(PairLedger)
    per_parent=defaultdict(PairLedger)
    parent_occurrences=defaultdict(int)
    firstowners=Counter()
    samples=[]
    max_retained_weight_weld_error=0.0
    # Each unordered squarefree active pair has a unique first separating prime.
    # Orient p-free endpoint as a, p-divisible endpoint z=p*b, matching #913.
    for (n,fn,zn),(m,fm,zm) in combinations(active,2):
        raw=zn*zm
        original_unordered.add(raw)
        fresh=fn^fm
        assert fresh
        p=min(fresh)
        if p not in fn:
            x,fx,tx=n,fn,zn
            z,fz,tz=m,fm,zm
        else:
            x,fx,tx=m,fm,zm
            z,fz,tz=n,fn,zn
        assert p in fz and p not in fx
        b=z//p
        fb=fz-{p}
        assert frozenset(q for q in fx if q<p) == frozenset(q for q in fb if q<p)
        assert x>W//p and b<=W//p
        # Independently evaluate the literal #913 VF-weighted Dirichlet atom
        # on the returned source. The p*x corner clips, p*b remains physical.
        # This checks the original source is actually preserved, rather than
        # assuming the simpler physical charge product survives the weld.
        wx=amp_weight(a,R+1,x)
        wb=amp_weight(a,R+1,b)
        wpb=amp_weight(a,R+1,z)
        wpx=0.0 if p*x>W else amp_weight(a,R+1,p*x)
        dirichlet_atom=-(a.mobius(x)*a.mobius(b))*(wx*wpb+wpx*wb)
        retained=(tx*a.mobius(x))*(tz*a.mobius(z))*dirichlet_atom
        max_retained_weight_weld_error=max(max_retained_weight_weld_error,abs(raw-retained))
        assert math.isclose(retained,raw,rel_tol=1e-11,abs_tol=1e-11), (R,x,z,p,raw,retained)
        remainder=fx^fb
        assert remainder and min(remainder)>p
        r=max(remainder)
        parent=(x//r if x%r==0 else x, b//r if b%r==0 else b)
        label=class_915(W,p,r,parent)
        assert label!='completed',('physical active source unexpectedly completed',R,n,m,p,r,parent)
        if label in ('first_right','next_left','returned_right'):
            raise AssertionError(('forbidden oriented sector nonzero',R,n,m,p,r,label,parent))
        key=(p,r,parent)
        parent_occurrences[key]+=1
        per_parent[(label,p,r,parent)].add(raw)
        per_r[(label,r)].add(raw)
        firstowners[p]+=1
        recovered.add(raw)
        sectors[label].add(raw)
        if len(samples)<10:samples.append((n,m,p,r,parent,label,raw))
    # exact double-sum/Fubini identity & first-owner pair exhaustion
    sqsum=sum(z for _,_,z in active)
    diag=sum(z*z for _,_,z in active)
    closed=0.5*(sqsum**2-diag)
    assert math.isclose(recovered.signed,original_unordered.signed,abs_tol=1e-5), (R,recovered.signed,original_unordered.signed)
    assert math.isclose(recovered.signed,closed,rel_tol=1e-8,abs_tol=1e-5), (R,recovered.signed,closed)
    U,L=recovered.positive,recovered.negative
    return {
        'carrier':'literal_#915_retained_weight_active_returned_raw_parents',
        'R':R,'W':W,'odd_count':R,'active_squarefree':len(active),
        'squarefree_composites':composites,'primes':primes,'squareful_omitted':omitted,
        'w_R':w,'VF_mass':V,
        'all_active_pairs':original_unordered.as_dict(),
        'recovered_parent_fubini':recovered.as_dict(),
        'reconstruction_closed_signed':closed,
        'max_retained_weight_weld_error':max_retained_weight_weld_error,
        'six_oriented_boundary':{k:sectors[k].as_dict() for k in ['first_left','first_right','next_left','next_right','returned_left','returned_right','completed']},
        'first_owner_hist':dict(firstowners),
        'root_group_by_r':[{'sector':s,'r':r,**v.as_dict()} for (s,r),v in sorted(per_r.items())],
        'raw_parent_occurrences':len(parent_occurrences),
        'raw_parent_max_multiplicity':max(parent_occurrences.values(),default=0),
        'raw_parent_multiplicity_hist':dict(Counter(parent_occurrences.values())),
        'raw_parent_balance':{
            'balanced':sum(v.B>=-1e-8*max(1.,v.absolute*v.absolute) for v in per_parent.values()),
            'unbalanced':sum(v.B < -1e-8*max(1.,v.absolute*v.absolute) for v in per_parent.values()),
            'total':len(per_parent)
        },
        'example_first_pairs':samples,
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mode',choices=['both','sector6','returned'],default='both')
    ap.add_argument('--r',type=int,nargs='*',default=[18,33,56])
    ap.add_argument('--returned-r',type=int,nargs='*',default=[17,32,56,101])
    ap.add_argument('--hand-clocks',action='store_true',help='also test W=317 and W=1027 on explicitly off-production clocks')
    ap.add_argument('--output',default='/tmp/vf_mid_sector_six_direct_results.json')
    opt=ap.parse_args()
    needed=max([(R+1)**2-1 for R in opt.returned_r] + [R*R-1 for R in opt.r] + ([1027] if opt.hand_clocks else []) + [3])
    a=Arithmetic(needed+1)
    results={}
    if opt.mode in ('both','sector6'):
        results['sector_903']=[sector_six_903(a,R,R*R-1) for R in opt.r]
        if opt.hand_clocks:
            results['sector_903'] += [sector_six_903(a,17,317),sector_six_903(a,32,1027)]
    if opt.mode in ('both','returned'):
        results['returned_915']=[returned_weighted_915(a,R) for R in opt.returned_r]
    Path(opt.output).write_text(json.dumps(results,indent=2))
    for row in results.get('sector_903',[]):
        val=row['recursive_sector_six_total']
        print(f"#903 R={row['R']:4d} W={row['W']:5d} production={row['production']} "+
              f"sector-six count={val['count']:7d} U={val['U']:.4f} L={val['L']:.4f} "+
              f"B={val['B']:.3f}, ratio={val['ratio']:.6f}; "+
              f"fine groups failed={row['fine_cell_cone_failures']}/{row['fine_cell_groups']}; "+
              f"parent mult max={row['raw_parent_max_multiplicity']}")
        print('  priority census:', {k:v['count'] for k,v in row['six_sectors'].items()})
        print('  child clock failing:',[(c['child_clock'],c['ratio']) for c in row['recursive_by_child_clock'] if not c['cone']][:10])
    for row in results.get('returned_915',[]):
        val=row['recovered_parent_fubini']
        print(f"#915 R={row['R']:4d} W={row['W']:7d} active={row['active_squarefree']:4d} "+
              f"pairs={val['count']:8d} U={val['U']:.4f} L={val['L']:.4f} "+
              f"B={val['B']:.3f} ratio={val['ratio']:.6f}; "+
              f"parent multiplicity max={row['raw_parent_max_multiplicity']}")
        print('  six oriented sectors:',{k:v['count'] for k,v in row['six_oriented_boundary'].items()})
        print('  raw-parent unbalanced:',row['raw_parent_balance'])
    print('Results:',opt.output)

if __name__=='__main__':main()