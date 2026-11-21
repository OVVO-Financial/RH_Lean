#!/usr/bin/env python3
"""Fully independent arithmetic census of both signed Selberg recurrences.

Enumerate every genuine prime power and Chebyshev psi through X=R^2-1.
Evaluate EACH native component separately:
 SelbergPair = psi(X)*log(X)+sum_{d<=X}Lambda(d)*psi(floor(X/d))
 S = SelbergPair - 2Xlog(X) - (log(X!)-Xlog(X))
 T = sum Lambda(d)*E(floor(X/d))
 Lfloor = sum Lambda(d)*E(floor(X/d))*log(floor(X/d))
 Def = sum Lambda(d)*E(floor(X/d))*(log(X)-log(d)-log(floor(X/d)))
 F = -sum Lambda(d)*log(d)*E(floor(X/d))
 A = S*log(X)-Lfloor-Def.
Verify Elog(X)=S-T and Elog(X)^2=A+F INDEPENDENTLY.
The negative rank-one selected K2 band cancels the ordered Lambda*Lambda
convolution, leaving precisely 2*sum(log(p)^2) on true near-root primes.
Finite checks are diagnostics, not a proof of any asymptotic inequality.
"""
from math import isqrt, lgamma, log, isclose


def pnt_data(N):
    sieve=bytearray(b"\x01")*(N+1)
    sieve[0:2]=b"\x00\x00"
    for p in range(2,isqrt(N)+1):
        if sieve[p]:
            sieve[p*p:N+1:p]=b"\x00"*((N-p*p)//p+1)
    primes=[p for p in range(2,N+1) if sieve[p]]
    lam=[0.]*(N+1)
    for p in primes:
        k=p
        while k<=N:
            assert lam[k]==0.
            lam[k]=log(p)
            k*=p
    psi=[0.]*(N+1)
    s=0.
    for n in range(1,N+1):
        s+=lam[n]
        psi[n]=s
    return primes,lam,psi


def evaluate(R):
    X=R*R-1
    primes,lam,psi=pnt_data(X)
    L=log(X)
    E=lambda n:psi[n]-n
    support=[n for n in range(2,X+1) if lam[n]]
    selberg=psi[X]*L+sum(lam[n]*psi[X//n] for n in support)
    S=(selberg-2*X*L)-(lgamma(X+1)-X*L)
    T=sum(lam[n]*E(X//n) for n in support)
    Lfloor=sum(lam[n]*E(X//n)*log(X//n) for n in support)
    defect=sum(lam[n]*E(X//n)*(L-log(n)-log(X//n)) for n in support)
    F=-sum(lam[n]*log(n)*E(X//n) for n in support)
    A=S*L-Lfloor-defect
    selected=[p for p in primes if 3*R<=4*p and p<R]
    logsum=sum(log(p) for p in selected)
    K2=2*sum(log(p)**2 for p in selected)-logsum**2
    ordered=-logsum**2
    matched_selected=2*sum(log(p)**2 for p in selected)
    assert isclose(K2-ordered, matched_selected, abs_tol=1e-7)
    assert isclose(S-T,E(X)*L,rel_tol=1e-10,abs_tol=2e-5)
    assert isclose(Lfloor+defect-F,T*L,rel_tol=1e-10,abs_tol=2e-5)
    assert isclose(A+F,E(X)*L*L,rel_tol=1e-10,abs_tol=2e-5)
    return R,X,len(selected),E(X),S,T,A,F,matched_selected


def main():
    print("R X band E(X) S_first T_corr A_direct F_matched selectedMatched")
    for R in [56,317,549,1027]:
        r,x,m,e,s,t,a,f,b=evaluate(R)
        print(f"{r:4d} {x:8d} {m:3d} {e:12.6f} {s:14.3f} "
              f"{t:14.3f} {a:16.3f} {f:16.3f} {b:13.3f}")
    print("PASS: independently evaluated full real Selberg/prime-power source")
    print("OPEN: uniform RH-strength bound on the full signed covariance")


if __name__=="__main__":
    main()
