#!/usr/bin/env python3
"""Source-exact high-prime incidence, rank, determinant and coercivity regression.

Finite observations do not prove the external Stadlmann-derived asymptotic
rank estimate or the one-sided Gz supplier needed for RH.
"""
from math import isqrt

def primes(n):
    a=bytearray(b'\x01')*(n+1)
    a[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p::p]=b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]]

def mobius(n):
    v=[1]*(n+1);v[0]=0
    a=bytearray(b'\x01')*(n+1);a[:2]=b'\x00\x00'
    for p in range(2,n+1):
        if a[p]:
            for k in range(p,n+1,p):v[k]=-v[k]
            for k in range(p*p,n+1,p*p):v[k]=0
            for k in range(p*p,n+1,p):a[k]=0
    return v

def mobius_trial(n):
    if n == 1: return 1
    s=1
    for p in range(2,isqrt(n)+1):
        if n%p==0:
            n//=p
            if n%p==0:return 0
            s=-s
    return -s if n>1 else s

def determinant(A):
    # Fraction-free Bareiss integer elimination
    a=[row[:] for row in A]; n=len(a);d=1;sgn=1
    if not n:return 1
    for k in range(n-1):
        if a[k][k]==0:
            ix=next((i for i in range(k+1,n) if a[i][k]),None)
            if ix is None:return 0
            a[ix],a[k]=a[k],a[ix];sgn=-sgn
        z=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                w=z*a[i][j]-a[i][k]*a[k][j]
                assert w%d==0
                a[i][j]=w//d
            a[i][k]=0
        d=z
    return sgn*a[-1][-1]

def run(R):
    X=R*R-1
    ps=[p for p in primes(X) if p>R]
    mu=mobius(R-1)
    byq={}
    for p in ps:byq.setdefault(X//p,p)
    # Rank of nested prefix rows: count new nonzero cofactor coordinates.
    rank=last=0
    for q in sorted(byq):
        if any(mu[c]!=0 for c in range(last+1,q+1)):
            rank+=1;last=q
    Q=max(1,int(R**.8))
    selected=[(q,byq[q]) for q in range(Q,min(2*Q,R))
              if q in byq and mu[q]!=0]
    assert selected
    qq=[q for q,p in selected];pp=[p for q,p in selected]
    for i,p in enumerate(pp):
        for j,q in enumerate(qq):
            assert (-mu[q] if p*q<=X else 0)==(-mu[q] if j<=i else 0)
    sz=min(12,len(selected))
    M=[[mobius_trial(pp[i]*qq[j]) if pp[i]*qq[j]<=X else 0
        for j in range(sz)] for i in range(sz)]
    assert all(M[i][j]==(-mu[qq[j]] if j<=i else 0)
               for i in range(sz) for j in range(sz))
    assert abs(determinant(M))==1
    # Actual signed Gram, all physical prime-row masks retained.
    cf=[c for c in range(1,R) if mu[c]][:8]
    H={c:sum(p*c<=X for p in ps) for c in cf}
    for c in cf:
        for d in cf:
            actual=sum(((-mu[c] if p*c<=X else 0)*
                        (-mu[d] if p*d<=X else 0)) for p in ps)
            assert actual==mu[c]*mu[d]*H[max(c,d)]
    # The signed second Selberg semiprime face is +2 log(p) log(q).
    # All active source cells in this *strict* dyadic band see E(X/(p*q))=E(1)=-1.
    from math import log
    total_negative = 0.0
    for i,p in enumerate(pp):
        for j,q in enumerate(qq):
            if j <= i:
                assert X//(p*q)==1, (R,Q,i,j,X//(p*q))
                # Independent coefficient derivation: (mu*log^2)(pq)
                # = log(pq)^2 - log(p)^2 - log(q)^2.
                k2 = log(p*q)**2-log(p)**2-log(q)**2
                assert abs(k2-2*log(p)*log(q)) < 1e-11
                total_negative -= k2
            else:
                assert p*q>X
    weighted = -2*sum(log(p)*sum(log(q) for q in qq[:i+1]) for i,p in enumerate(pp))
    assert abs(total_negative-weighted)<1e-9*max(1,abs(weighted))
    assert total_negative<0
    # Sample the universal inverse-difference coercivity inequality.
    for seed in range(1,9):
        v=[(seed*(j+3)*17)%31-15 for j in range(len(qq))]
        s=0; y=[]
        for q,z in zip(qq,v):
            s-=mu[q]*z;y.append(s)
        assert sum(z*z for z in v)<=4*sum(z*z for z in y)
    print(f"R={R} high_primes={len(ps)} distinct_quotients={len(byq)} "
          f"rank={rank} unimodular_minor={len(qq)} det_abs=1")
    return rank,len(qq)

if __name__=="__main__":
    expected={31:(15,3),100:(44,13),317:(131,35),
              549:(222,64),1027:(395,103),3000:(1122,292)}
    for R, value in expected.items():
        assert run(R)==value
    print("PASS: source masks, exact rank, determinant, Gram and coercivity checks")
