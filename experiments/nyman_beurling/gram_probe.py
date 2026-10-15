#!/usr/bin/env python3
"""Optional DOUBLE-PRECISION numerical Gram probe; not a proof certificate.

Requires numpy + scipy. The exact infinite Gram is reduced to a finite
lcm-period sum involving digamma (alpha=1/2) or Hurwitz zeta (alpha>1/2).
For an integer k>=2, a_k(m)=(m mod k)/k.
"""
import argparse
import math
import numpy as np
from scipy.linalg import solve
from scipy.special import digamma, zeta

def gram(N=64, alpha=0.5):
    assert N>=2 and 0.5<=alpha<1
    ks=np.arange(2,N+1)
    if alpha==0.5:
        h=np.log(ks)/ks
    else:
        h=zeta(2*alpha,1.0)*(1/ks-ks.astype(float)**(-2*alpha))/(2*alpha)
    g=np.zeros((N-1,N-1))
    for i,k in enumerate(ks):
        for j,l in enumerate(ks[:i+1]):
            L=math.lcm(int(k),int(l))
            r=np.arange(1,L+1,dtype=float)
            if alpha==0.5:
                w=(digamma((r+1)/L)-digamma(r/L))/L
            else:
                w=(zeta(2*alpha,r/L)-zeta(2*alpha,(r+1)/L))/(2*alpha*L**(2*alpha))
            ak=(r%k)/k
            al=(r%l)/l
            g[i,j]=g[j,i]=float(np.dot(ak*al,w))
    return ks,h,g

def solve_subspace(ks,h,g,which):
    if which=="full":
        mask=np.ones(len(ks),dtype=bool)
    elif which=="omit6":
        mask=ks!=6
    elif which=="primes":
        mask=np.array([all(k%d for d in range(2,math.isqrt(k)+1)) for k in ks])
    elif which=="squarefree":
        def is_sqfree(k):
            return all(k%(d*d) for d in range(2,math.isqrt(k)+1))
        mask=np.array([is_sqfree(int(k)) for k in ks])
    else:
        raise ValueError(which)
    c=solve(g[np.ix_(mask,mask)],h[mask],assume_a="pos")
    return float(1.0/(2*ARGS.alpha)-2*h[mask]@c+c@g[np.ix_(mask,mask)]@c)

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--N",type=int,default=64)
    p.add_argument("--alpha",type=float,default=0.5)
    ARGS=p.parse_args()
    ks,h,g=gram(ARGS.N,ARGS.alpha)
    for which in ("full","omit6","primes","squarefree"):
        print(f"N={ARGS.N} alpha={ARGS.alpha} set={which} d2={solve_subspace(ks,h,g,which):.12f}")
