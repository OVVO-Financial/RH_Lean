#!/usr/bin/env python3
"""Finite #915 PNT-star and signed-aggregate audit, NOT an RH proof.

Use ACTUAL primes, not PNT-density replacement. PNT already proves the
root-to-square reciprocal owner mass <1 eventually in Lean. Test the direct
protected-correlation Euler star, signed physical defect, and original #915
sharp-transport/source-inlet margin. Star -> first-bad packet is NOT proved.
The transported stripped parent is a formally tagged heat entry, not an
independently occurring physical source term. No tested first-bad event exists.
"""
import argparse
from array import array
from bisect import bisect_right
from math import isclose, isqrt, log


def near(a, b, tol=3e-5):
    assert isclose(a, b, rel_tol=2e-9, abs_tol=tol), (a, b)


class Sieve:
    def __init__(self, N):
        self.p = bytearray(b'\x01')*(N+1)
        self.p[:2] = b'\x00\x00'
        for q in range(2, isqrt(N)+1):
            if self.p[q]:
                self.p[q*q:N+1:q] = b'\x00'*((N-q*q)//q+1)
        self.primes = array('I', (q for q in range(2, N+1) if self.p[q]))
        self.recip = array('d', [0])
        s = 0.
        for q in self.primes:
            s += 1/q
            self.recip.append(s)
        self.minfac = [0]*(isqrt(N)+2)
        for q in range(2, len(self.minfac)):
            if self.p[q]:
                for n in range(q, len(self.minfac), q):
                    if not self.minfac[n]: self.minfac[n] = q

    def pi(self, x): return bisect_right(self.primes, x)

    def beta(self, R):
        return self.recip[self.pi(R*R)]-self.recip[self.pi(R)]

    def mu(self, m):
        ans = 1
        while m > 1:
            q = self.minfac[m] or m
            m //= q
            if m%q == 0: return 0
            ans = -ans
        return ans


def response(R, m):
    return sum(log(k) for k in range(R*R//m+1, (R+1)**2//m+1))


def stars(a, R):
    """Literal v(m), v(mq), D(m,q): no PNT-to-Li substitution."""
    owner_lo = a.pi(R)
    parent_abs = star_abs = defect_abs = capacity = 0.
    retained_signed = defect_signed = star_signed = 0.
    pairs = 0
    beta = a.beta(R)
    assert beta < 1, (R, beta)
    for m in range(1, R):
        mu = a.mu(m)
        if not mu: continue
        resp = response(R, m)
        v = -mu*resp/m
        betam = D = childsum = 0.
        for q in a.primes[owner_lo:a.pi((R*R-1)//m)]:
            resp_child = response(R, m*q)
            child = mu*resp_child/(m*q)
            d = mu*(resp_child-resp)/(m*q)
            near(child+v/q, d, 1e-8)
            betam += 1/q
            D += d
            childsum += child
            pairs += 1
        star = v+childsum
        near(star, (1-betam)*v+D)
        assert 0 <= betam <= beta+1e-11
        assert abs(D) <= betam*abs(v)+1e-8
        assert abs(star) <= abs(v)+1e-8
        parent_abs += abs(v)
        star_abs += abs(star)
        defect_abs += abs(D)
        capacity += betam*abs(v)
        retained_signed += (1-betam)*v
        defect_signed += D
        star_signed += star
    near(star_signed, retained_signed+defect_signed)
    assert defect_abs <= capacity+1e-5
    assert star_abs <= parent_abs+1e-5
    print('STAR R=%d beta=%.9f retained=%.3f defect=%.3f signedStar=%.3f '
          'absDef/cap=%.6f starAbs/parentAbs=%.6f children=%d PASS'
          % (R,beta,retained_signed,defect_signed,star_signed,
             defect_abs/capacity if capacity else 0,
             star_abs/parent_abs if parent_abs else 0,pairs))


def payment(a, R, vf, check_pairs=True):
    """Independent original anchored and active+residual signed paths."""
    D = a.pi(R*R)-vf
    V = (2*R+1)/log(R*R+R+.5)
    w = V/R
    odd = range((R*R+1)|1, (R+1)**2, 2)
    z = [w-int(bool(a.p[n])) for n in odd]
    assert len(z)==R and 0<w<1
    P = sum(bool(a.p[n]) for n in odd)
    Dn = a.pi((R+1)**2)-(vf+V)
    near(Dn, D+P-V, 2e-6)
    U = max(-D,0)+sum(max(t,0) for t in z)
    L = max(D,0)+sum(max(-t,0) for t in z)
    T = U+L
    near(U-L, -Dn, 2e-6)
    margin = T*T-2*Dn*Dn
    near(margin, 6*U*L-U*U-L*L)

    if check_pairs:
        lo,hi=R*R+1,(R+1)**2
        sqful = bytearray(hi-lo)
        for q in a.primes[:a.pi(isqrt(hi-1))]:
            if q==2: continue
            k=q*q
            for n in range(((lo+k-1)//k)*k,hi,k):
                if n&1: sqful[n-lo]=1
        act,om=[],[]
        for n in odd:
            (om if sqful[n-lo] else act).append(w-int(bool(a.p[n])))
        X=sum(act); C=sum(om)
        H=sum(abs(t) for t in act)
        O=sum(abs(t) for t in om)
        diag=sum(t*t for t in act)
        # Exact active identity root, squareful restoration, and omitted
        # ORIGINAL absolute denominator, per ACTIVE_EXCESS_LEDGER.lean.
        demand=2*(D*D-2*D*X)+2*diag-2*C*(2*Dn+C)
        capacity=D*D+2*abs(D)*H+diag+O*(2*(abs(D)+H)+O)
        residual=demand-capacity
        Z=(X*X-diag)/2
        AZ=(H*H-diag)/2
        if R<=317:
            direct=sum(t*u for i,t in enumerate(act) for u in act[i+1:])
            direct_abs=sum(abs(t*u) for i,t in enumerate(act) for u in act[i+1:])
            near(Z,direct);near(AZ,direct_abs)
        boundary=4*Z-2*AZ
        transport=-4*Z-2*AZ  # algebraic tagged stripped parents
        near(boundary+transport,-4*AZ)
        near(residual+boundary,-margin)
        sharp=transport+4*AZ-residual
        near(sharp,margin)
        print('PAYMENT R=%d P=%d beta=%.8f B=%.6f ratio=%.8f '
              'residual=%.3f transported=%.3f heatAbs=%.3f PASS'
              % (R,P,a.beta(R),margin,(U-L)**2/T**2,
                 residual,transport,AZ))
    assert margin>=-1e-9*T*T, (R,margin)
    return (U-L)**2/T**2,margin


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--extended',action='store_true')
    args=ap.parse_args()
    roots=[8,17,18,32,56,101,119,317,1027]
    if args.extended: roots += [5266,6000]
    Rmax=max(roots)
    a=Sieve((Rmax+1)**2)
    vf={}
    s=0.
    for r in range(2,Rmax+1):
        vf[r]=s
        s+=(2*r+1)/log(r*r+r+.5)
    for R in (8,17,32,56,101,317,1027): stars(a,R)
    for R in roots: payment(a,R,vf[R])
    if args.extended:
        max_ratio=(-1.,0); min_margin=(float('inf'),0)
        max_beta=(-1.,0); max_radial=(-1.,0)
        for R in range(8,Rmax+1):
            D=a.pi(R*R)-vf[R]
            V=(2*R+1)/log(R*R+R+.5)
            P=a.pi((R+1)**2)-a.pi(R*R)
            w=V/R
            U=max(-D,0)+w*(R-P)
            L=max(D,0)+(1-w)*P
            T=U+L
            B=T*T-2*(U-L)**2
            ratio=(U-L)**2/T**2
            beta=a.beta(R)
            radial=abs(D)/(2*R*log(R))
            if ratio>max_ratio[0]:max_ratio=(ratio,R)
            if B<min_margin[0]:min_margin=(B,R)
            if beta>max_beta[0]:max_beta=(beta,R)
            if radial>max_radial[0]:max_radial=(radial,R)
            assert B>=-1e-9*T*T and beta<1
        assert .206<max_ratio[0]<.207 and max_ratio[1]==119
        print('ALL R=8..%d: maximum ratio=%.9f at R=%d, minimum margin=%.6f '
              'at R=%d, max beta=%.9f at R=%d, max |D|/(2RlogR)=%.9f '
              'at R=%d PASS'
              % (Rmax,*max_ratio,*min_margin,*max_beta,*max_radial))
    print('PASS finite signed sharp-transport + original denominator + PNT stars')
    print('OPEN: first-bad payment for all R; literal signed star-to-#915 splice')


if __name__=='__main__':main()
