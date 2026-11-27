import math, json, sys, itertools
from functools import reduce
import numpy as np
from scipy.optimize import linprog
from scipy.special import gammaln

GAMMA=0.5772156649015329
CSTAR=2*math.log(2)-math.pi**2/12

def prime_powers(N):
    isprime=np.ones(N+1,dtype=bool);isprime[:2]=False
    for p in range(2,math.isqrt(N)+1):
        if isprime[p]: isprime[p*p::p]=False
    ps=np.flatnonzero(isprime)
    a=[ps]; b=[np.log(ps)]
    for p in ps[ps<=math.isqrt(N)]:
        q=int(p)*int(p)
        while q<=N:
            a.append(np.array([q]));b.append(np.array([math.log(int(p))]));q*=int(p)
    return np.concatenate(a),np.concatenate(b)

def exact_check(R):
    N=R*R-1;m=R;L=m*N
    lcm=1; index=1; complement=1
    for j in range(1,L+1):
        if (j-1)%m==0:lcm=math.lcm(lcm,(j-1)//m or 1)
        a=math.gcd(j,lcm);index*=a;complement*=j//a
        if R<=6 and j<=100:
            k=(j-1)//m
            g=reduce(math.gcd,(math.comb(j,s) for s in range(1,k+1)),j) # for k=0, convention gcd=j
            assert g==j//a
    v=1
    for p in range(2,N+1):
        if not any(p%d==0 for d in range(2,math.isqrt(p)+1)):
            d=p; e=0
            while d<=N:e+=L//d-m;d*=p
            v*=p**e
    assert v==index and complement*index==math.factorial(L)
    # Determinantal divisor of diag(1,...,L), independently via gcd of minors at small L.
    if L<=24:
        g=0
        for removed in itertools.combinations(range(1,L+1),m):
            g=math.gcd(g,math.factorial(L)//math.prod(removed))
        assert g==index
    return {'R':R,'N':N,'m':m,'L':L,'exact_index_digits':len(str(index))}

def actual(R):
    N=R*R-1;m=R;L=m*N;q,w=prime_powers(N)
    S=float(np.sum(w*(N/q-1)))
    A=float(np.sum(w*(L//q-m)))
    C=float(np.sum(w*(m-(m*(N%q))//q)))
    F=math.lgamma(N+1)
    assert abs((m*F-A)-C)<1e-6*max(1,C)
    G=S-N*math.log(N)+(1+GAMMA)*N
    return {'R':R,'N':N,'m':m,'L':L,'G_over_R':G/R,'rounding_over_R':(S-A/m)/R,'C_normalized':C/(m*N),'certificate_target':GAMMA,'binomial_ceiling':CSTAR,'binomial_gap':GAMMA-CSTAR,'log_A':A,'log_C':C}

def cert(R, grid, masscap, include_witness=False):
    N=R*R-1;m=R
    # Prime-blind basis: evenly spaced factorial arguments, hyperbolic arguments, and small prefix.
    K=np.unique(np.r_[np.arange(1,min(N,grid)+1),np.floor(np.linspace(0,N,grid+1)).astype(int),N//np.arange(1,grid+1)])
    K=K[K>=2].astype(np.int64)
    d=np.arange(2,N+1,dtype=np.int64)
    cap=m-(m*(N%d))//d
    A=d[:,None]; F=K[None,:]//A
    n=len(K)
    # c=cplus-cminus, norm <= masscap; zero linear moment. Work with normalized integer factorial cost.
    obj=gammaln(K+1)/N
    constraint=np.concatenate([F,-F],axis=1).astype(float)
    constraint=np.vstack([constraint,np.ones((1,2*n))]); rhs=np.r_[cap/m,masscap]
    eq=np.r_[K,-K][None,:]/N
    z=linprog(np.r_[-obj,obj],A_ub=constraint,b_ub=rhs,A_eq=eq,b_eq=[0.0],bounds=(0,None),method='highs',options={'time_limit':20.0})
    if not z.success:return {'R':R,'grid':grid,'basis':n,'masscap':masscap,'status':z.message}
    c=z.x[:n]-z.x[n:]; Q=1000000
    v=np.floor(m*Q*c).astype(np.int64)
    # Repair any floating tolerance violation by reducing the N! exponent. Then exact check of all d.
    # Check integer arithmetic cannot overflow, both before and after repair.
    assert (N//2)*sum(abs(int(x)) for x in v)+Q*m < 2**63
    err=F@v-Q*cap
    if np.any(err>0):
        i=int(np.flatnonzero(K==N)[0]);v[i]-=int(np.max((np.maximum(err,0)+(N//d)-1)//(N//d)))
    assert (N//2)*sum(abs(int(x)) for x in v)+Q*m < 2**63
    assert np.all(F@v<=Q*cap)
    val=float(np.dot(v.astype(float),obj)/(m*Q))
    result = {'R':R,'grid':grid,'basis':n,'masscap':masscap,'status':'exact integer cap verified','coefficient_l1':float(np.sum(np.abs(v)))/(m*Q),'normalized_log_lower':val,'deficit_from_gamma_times_R':(GAMMA-val)*R,'support':int(np.count_nonzero(v)),'cert_Q':Q,'linear_moment_after_rounding':sum(int(k)*int(c) for k,c in zip(K,v))}
    if include_witness:
        result['integer_coefficients'] = [[int(k), int(c)] for k,c in zip(K,v) if c]
    return result

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='lp_witnesses':
        for R,grid,cap in [(16,128,64),(32,256,64),(64,256,64),(64,512,128)]:
            print(json.dumps(cert(R,grid,cap,include_witness=True)),flush=True)
    elif len(sys.argv)>1 and sys.argv[1]=='lp_extended':
        for R,grid,cap in [(16,128,64),(32,256,64),(64,256,64),(64,512,128)]:
            print(json.dumps(cert(R,grid,cap)),flush=True)
    elif len(sys.argv)>1 and sys.argv[1]=='lp':
        for R,grid in [(16,32),(32,64),(64,128),(128,128)]:
            for cap in (8,32):
                print(json.dumps(cert(R,grid,cap)),flush=True)
    else:
        for R in (2,3,4,5,6,8): print(json.dumps({'exact':exact_check(R)}),flush=True)
        for R in (16,32,64,128,317,1027,2048,4096):print(json.dumps(actual(R)),flush=True)
