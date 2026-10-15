"""Exact signed floor-kernel diagnostics; floating values are display-only."""
from pathlib import Path
import json
import math
import numpy as np
from numba import njit

@njit
def sieve(n):
    mu=np.ones(n+1,np.int64); mu[0]=0
    prime=np.ones(n+1,np.uint8); prime[0]=prime[1]=0
    for p in range(2,n+1):
        if prime[p]:
            for v in range(p,n+1,p):
                mu[v]=-mu[v]
            for v in range(p+p,n+1,p):
                prime[v]=0
            if p*p<=n:
                for v in range(p*p,n+1,p*p):
                    mu[v]=0
    return mu

@njit
def floor_budgets(mu,N,x):
    q=0; raw=0; rows=0; cs2=0; support=0
    for i in range(1,N+1):
        row=0
        for j in range(1,N+1):
            k=x//(i*j)
            row += mu[j]*k
            raw += abs(mu[i]*mu[j])*k
        q += mu[i]*row
        rows += abs(mu[i]*row)
        cs2 += row*row
        support += mu[i]*mu[i]
    return q,raw,rows,support,cs2

@njit
def conv_prefix(f, a, N):
    X=len(f)-1
    g=np.zeros(X+1,np.int64)
    for i in range(1,N+1):
        if a[i]:
            for j in range(1,X//i+1):
                g[i*j]+=a[i]*f[j]
    return g

@njit
def conv_ones(f):
    X=len(f)-1
    g=np.zeros(X+1,np.int64)
    for i in range(1,X+1):
        if f[i]:
            for j in range(1,X//i+1):
                g[i*j]+=f[i]
    return g

@njit
def defect(a,N,X):
    d=np.zeros(X+1,np.int64); d[1]=1
    for i in range(1,N+1):
        for j in range(1,X//i+1):
            d[i*j]-=a[i]
    return d

@njit
def defect_square_values(d, xs):
    result=np.zeros(len(xs),np.int64)
    for k in range(len(xs)):
        n=xs[k]
        for i in range(1,n+1):
            if n%i==0:
                result[k]+=d[i]*d[n//i]
    return result

def main():
    root=Path(__file__).parent
    mu=sieve(4_000_000); M=np.cumsum(mu)
    rows=[]
    for N in [10,32,100,317,1000,2000]:
        x=N*N
        q,raw,rowabs,support,cs2=map(int,floor_budgets(mu,N,x))
        pred=2*int(M[N])-q
        assert pred==int(M[x])
        E=max(abs(int(M[i]))/math.sqrt(i) for i in range(1,N+1))
        rec=sum(float(mu[i])/i for i in range(1,N+1))
        rows.append(dict(N=N,x=x,M_N=int(M[N]),M_x=int(M[x]),Q=q,
                         raw_absolute_budget=raw,row_signed_then_absolute=rowabs,
                         cauchy_squared_budget=support*cs2,cauchy_display=math.sqrt(support*cs2),
                         critical_prefix_norm_display=E,
                         normalized_Q_display=abs(q)/(N*E),
                         normalized_row_bound_display=rowabs/(N*E),
                         reciprocal_bulk_display=x*rec*rec))
    higher=[]
    for N,k in [(10,3),(10,4),(30,3),(30,4),(100,3)]:
        X=N**k
        a=np.zeros(X+1,np.int64); a[:N+1]=mu[:N+1]
        f=a.copy(); components=[]
        for j in range(1,k+1):
            s=int(f.sum())
            components.append(((-1)**(j-1))*math.comb(k,j)*s)
            if j<k:
                f=conv_ones(conv_prefix(f,a,N))
        assert sum(components)==int(M[X])
        higher.append(dict(N=N,k=k,x=X,signed_components=components,
                           sum=sum(components),M_x=int(M[X]),
                           separated_absolute_budget=sum(abs(v) for v in components)))
    N=10; d=defect(mu,N,2000)
    vals=[(i,int(d[i])) for i in [1,2,10,11,13,121,143,187]]
    sq=defect_square_values(d,np.array([121,143,187],np.int64)).tolist()
    report=dict(floor_kernel=rows,higher_order=higher,
                defect_N10=vals,defect_square_at_121_143_187=sq)
    (root/'diagnostics.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__': main()
