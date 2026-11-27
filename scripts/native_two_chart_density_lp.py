"""Finite relaxation: independent unsigned density row bounds plus monotone exposure.
No actual high-prime counts are used in the constraints. Floating LP is diagnostic only.
"""
import math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, vstack

def test(R):
    X=R*R-1
    lp=np.zeros(X+1,dtype=np.int32); hi=np.ones(X+1,dtype=np.int32)
    mu=np.zeros(X+1,dtype=np.int8);mu[1]=1
    ps=[]
    for n in range(2,X+1):
        if not lp[n]:lp[n]=n;ps.append(n);mu[n]=-1
        q=int(lp[n]);hi[n]=max(q,int(hi[n//q]))
        for p in ps:
            if p>q or p*n>X:break
            lp[p*n]=p;mu[p*n]=0 if p==q else -mu[n]
    a=np.flatnonzero(mu[1:R])+1
    smooth=(mu!=0)&(hi<R); signed_smooth=int(mu[smooth].sum()); mh=int(mu[:R].sum())
    M=np.cumsum(mu[:R]);K=float(np.max((M-1.)**2/np.arange(1,R+1))); B=R*math.sqrt(K)
    mapping={int(d):i for i,d in enumerate(a)}; nr=len(a)
    ii=[];jj=[];vv=[];rhs=[];S=[];row_errors=[];row_centers=[]
    for i,d0 in enumerate(a):
        d=int(d0);sd=int(smooth[d::d].sum());S.append(sd)
        t=d;omega=0;den=1
        while t>1:p=int(lp[t]);t//=p;den*=p+1;omega+=1
        center=6/math.pi**2*X/den-sd
        err=(2**omega+2)*math.sqrt(X/d);row_errors.append(err);row_centers.append(center)
        for t in range(d,R,d):
            if t in mapping:ii.append(i);jj.append(mapping[t]);vv.append(1.)
    A=coo_matrix((vv,(ii,jj)),shape=(nr,nr)).tocsr();center=np.array(row_centers);error=np.array(row_errors)
    # Independent admissible interval for differences of prime counts:
    # monotonicity and at most one prime per integer in the exposed interval.
    k=np.arange(nr-1);D=coo_matrix((np.r_[np.ones(nr-1),-np.ones(nr-1)],(np.r_[k,k],np.r_[k,k+1])),shape=(nr-1,nr)).tocsr()
    cap=np.array([X//int(x)-X//int(y) for x,y in zip(a,a[1:])],dtype=float)
    G=vstack([A,-A,D,-D],format='csr');g=np.r_[center+error,-center+error,cap,np.zeros(nr-1)]
    c=mu[a].astype(float);constant=2*mh-signed_smooth
    low=linprog(c,A_ub=G,b_ub=g,bounds=(0,None),method='highs');high=linprog(-c,A_ub=G,b_ub=g,bounds=(0,None),method='highs')
    assert low.success and high.success
    Q=2*mh-int(mu.sum())
    # Exact density feasibility is classical; numerical solve is not a certified bound.
    print(f'{R},{Q},{B:.9f},{constant+low.fun:.9f},{constant-high.fun:.9f},{(constant-high.fun)/B:.9f},{-(constant+low.fun)/B:.9f}',flush=True)
if __name__=='__main__':
    print('R,Q,budget,lp_lower,lp_upper,upper_over_budget,negative_lower_over_budget',flush=True)
    for r in (16,32,64,128,317,512):test(r)
