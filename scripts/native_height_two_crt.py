#!/usr/bin/env python3
"""Native height-two local integrality and shared global rational jet experiment.
Exact arithmetic. No theta periods, RH or actual source divisibility assumed.
"""
from fractions import Fraction as F
from math import factorial, isqrt, log
import csv


def primes(n):
    return [p for p in range(2,n+1) if all(p%d for d in range(2,isqrt(p)+1))]


def vp_int(a,p):
    assert a
    a=abs(a); k=0
    while a%p==0:
        a//=p; k+=1
    return k


def vp(a,p):
    if not a: return float('inf')
    return vp_int(a.numerator,p)-vp_int(a.denominator,p)


def frac_p(x,p):
    b=x.denominator; q=1
    while b%p==0:
        b//=p; q*=p
    if q==1: return F(0)
    return F((x.numerator*pow(b,-1,q))%q,q)


def lpower_columns(p,N):
    L=[]; k=1; e=0
    while k<=N:
        L.append((k,F(1,p**e))); k*=p*p; e+=1
    cols=[{0:F(1)}]
    for j in range(1,N+1):
        v={}
        for i,a in cols[-1].items():
            for k,b in L:
                if i+k<=N:
                    v[i+k]=v.get(i+k,F(0))+a*b
        cols.append(v)
    return cols


def shared_jet(N):
    ps=primes(isqrt(N)); cols={p:lpower_columns(p,N) for p in ps}
    c=[F(0),F(1)]; checks=0
    for n in range(2,N+1):
        corrections=F(0)
        for p in ps:
            if p*p>n: break
            r=sum((c[j]*cols[p][j].get(n,0) for j in range(1,n)), F(0))
            corrections+=frac_p(r,p)
        a=-corrections
        a=a-(a.numerator//a.denominator)
        c.append(a if a else F(1))
    for p in ps:
        for n in range(1,N+1):
            a=sum((c[j]*cols[p][j].get(n,0) for j in range(1,n+1)),F(0))
            assert vp(a,p)>=0
            assert vp(c[n],p)>=-((n-1)//(p*p-1))
            checks+=2
    return c,checks


def verify_rows(N):
    c,checks=shared_jet(N)
    rows=[]
    for n in (8,16,32,64,128,256,512):
        if n>N: break
        denom_bound=1
        for p in primes(isqrt(n)):
            denom_bound*=p**((n-1)//(p*p-1))
        assert denom_bound%c[n].denominator==0
        a=factorial(n)*c[n]
        assert a.denominator==1 and a>0
        D=factorial(n)//denom_bound
        assert D*denom_bound==factorial(n) and a.numerator%D==0
        gamma=0.5772156649015329
        main=n*log(n)-(1+gamma)*n
        rows.append((n,str(c[n]),c[n].denominator.bit_length(),log(D)-main,log(a.numerator)-main))
    print('exact local coefficient/valuation checks:',checks)
    with open('native_height_two_crt_results.csv','w') as f:
        w=csv.writer(f);w.writerow(['degree','rational_coeff','denominator_bits','forced_divisor_log_minus_main','actual_derivative_log_minus_main']);w.writerows(rows)
    for r in rows:print(r)


def log_interval(n,k=16):
    e=n.bit_length()-1
    def f(a,b):
        y=F(a-b,a+b); y2=y*y
        s=2*sum((y**(2*j+1)/F(2*j+1) for j in range(k)),F(0))
        t=2*y**(2*k+1)/((2*k+1)*(1-y2))
        return s,s+t
    lo,hi=f(2,1);a,b=f(n,2**e)
    return e*lo+a,e*hi+b


def certify_gap():
    N=2000
    c=sum((log_interval(p)[1]/(p*p-1) for p in primes(N)),F(0))
    c+=(log_interval(N)[1]+1)/N/(1-F(1,(N+1)**2))
    g=sum((F(1,n) for n in range(1,1001)),F(0))-log_interval(1000)[1]-F(1,1000)
    assert c<F(575,1000)<g
    print('rigorous c2 upper:',float(c),'rigorous gamma lower:',float(g),'strict difference >',float(g-c))


if __name__=='__main__':
    verify_rows(512)
    certify_gap()
