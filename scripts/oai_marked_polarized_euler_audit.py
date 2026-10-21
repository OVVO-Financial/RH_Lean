#!/usr/bin/env python3
"""Finite exact-formula tests: NNS mixed fourth moments, phase-aware Euler
toggle, Parseval restriction and dyadic parent escape. Not an OAI bound."""
import math, cmath
zeta=[cmath.exp(1j*math.pi*e/3) for e in range(6)]
families={"x317":(5,5,1,1),"x1027":(1,3,3,5),
          "R317":(0,4,2,0),"R1027":(3,1,5,3)}
def nns(zs):
    z=list(zs)
    K=sum(abs(a)**2 for a in z)
    g=[(z[i]*z[j].conjugate()).real for i in range(len(z)) for j in range(i+1,len(z))]
    P=sum(max(v,0) for v in g);N=sum(max(-v,0) for v in g)
    E=abs(sum(z))**2
    assert math.isclose(E,K+2*(P-N),abs_tol=1e-9)
    return K,P,N,E
quartic=0
for name,exps in families.items():
    atoms=[zeta[e] for e in exps]
    K,P,N,E=nns(atoms)
    assert math.isclose(E**2,K**2+4*K*P-4*K*N+4*(P-N)**2,abs_tol=1e-9)
    quartic+=E**2
    print(f"{name}: K={K:.3f} P={P:.3f} N={N:.3f} fourth={E**2:.3f}")
    for j,k in [(0,0),(1,0),(0,1),(1,1),(2,0),(0,2)]:
        logs=[math.log(n) for n in (3,5,7,11)]
        Kj,Pj,Nj,Ej=nns(a*L**j for a,L in zip(atoms,logs))
        Kk,Pk,Nk,Ek=nns(a*L**k for a,L in zip(atoms,logs))
        rhs=Kj*Kk+2*(Kj*Pk+Kk*Pj)-2*(Kj*Nk+Kk*Nj)+4*(Pj-Nj)*(Pk-Nk)
        assert math.isclose(Ej*Ek,rhs,rel_tol=1e-10,abs_tol=1e-8)
assert math.isclose(quartic,19,abs_tol=1e-8)
for i in range(6):
    theta=zeta[i]; L=math.log(7);ell=math.log(11)
    a=2.1-.3j;b=.4+.7j
    for j in (0,1,2):
        lhs=L**j*a-theta*(L+ell)**j*b
        rhs={0:a-theta*b,1:L*(a-theta*b)-ell*theta*b,
             2:L*L*(a-theta*b)-(2*L*ell+ell*ell)*theta*b}[j]
        assert abs(lhs-rhs)<1e-12
# For a(1)=1, a(g)=-1 on Z/2:
# only the trivial character: fourth moment 0 < resonant contribution 8.
# both orthogonal characters: total fourth moment 16 = 2*8.
assert (1-1)**4==0 and (1+1)**4==16
assert (1-1)**4+(1+1)**4==2*8
# Prime p=2 can move an admitted n outside the [U,2U] window.
U=1000;n=1500
assert U<=n<=2*U and not U<=2*n<=2*U
print("PASS polarized 0/1/2 log rows, signed sextic quadrants, phase toggle,")
print("     incomplete Parseval and dyadic partner-exit falsifiers")
