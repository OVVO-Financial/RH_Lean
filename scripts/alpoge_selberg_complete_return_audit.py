#!/usr/bin/env python3
"""Complete signed K2*E recurrence audit at physical square endpoints.

K2(n)=(Lambda*Lambda)(n)-Lambda(n)*log n; Lambda is carried at ALL prime powers.
The F_R subsource is the full [3R/4,R) prime-square plus distinct semiprime
band. This computes every omitted K2 face explicitly: no ghost, square,
low/high or other composite K2 coefficient is silently discarded.

NUMERICAL DIAGNOSTIC ONLY; floating logarithms do not provide an
asymptotic or exact Lean RH-strength bound.
"""
from math import log, isqrt
from array import array

def primes_up_to(N):
    a = bytearray(b'\x01') * (N+1)
    a[:2] = b'\x00\x00'
    for p in range(2, isqrt(N)+1):
        if a[p]:
            a[p*p::p] = b'\x00' * ((N-p*p)//p+1)
    return [p for p in range(2,N+1) if a[p]]

def run(R):
    X=R*R-1
    primes=primes_up_to(X)
    lam=array('d',[0.0])*(X+1)
    support=[]
    for p in primes:
        q=p; ell=log(p)
        while q<=X:
            lam[q]=ell
            support.append(q)
            q*=p
    support.sort()
    psi=array('d',[0.0])*(X+1)
    running=0.0
    for n in range(1,X+1):
        running+=lam[n]
        psi[n]=running
    E=lambda t:psi[t]-t
    k2=array('d',[0.0])*(X+1)
    for n in support:
        k2[n]=-lam[n]*log(n)
    for a in support:
        wa=lam[a]
        for b in support:
            ab=a*b
            if ab>X: break
            k2[ab]+=wa*lam[b]
    full=sum(k2[n]*E(X//n) for n in range(2,X+1) if k2[n])
    band=[p for p in primes if 4*p>=3*R and p<R]
    face=sum(log(p)**2 for p in band)-2*sum(log(p)*log(q)
         for i,p in enumerate(band) for q in band[i+1:])
    direct=0.0
    for i,p in enumerate(band):
        n=p*p
        assert X//n==1
        assert abs(k2[n]+log(p)**2)<1e-10
        direct+=k2[n]*E(X//n)
        for q in band[i+1:]:
            n=p*q
            assert X//n==1
            assert abs(k2[n]-2*log(p)*log(q))<1e-9
            direct+=k2[n]*E(X//n)
    assert abs(face-direct)<1e-8*max(1,abs(face))
    print(f"R={R} band={face:+.2f} "
          f"full_K2_E={full:+.2f} "
          f"remaining_K2_E={full-face:+.2f} "
          f"E={E(X):+.2f} E_log2={E(X)*log(X)**2:+.2f} "
          f"other_signed_recurrence={E(X)*log(X)**2-full:+.2f}")
    return face,full,E(X)*log(X)**2

if __name__=="__main__":
    assert run(100)[0]<0
    assert run(317)[0]<0
    assert run(549)[0]<0
    assert run(1027)[0]<0
    print("PASS: complete Lambda prime-power K2 convolution, exact physical band masks")
