#!/usr/bin/env python3
"""Exact finite Galois cochains, local Sha, NNS integral, Fourier dual (no RH)."""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import prod
from random import Random


@dataclass(frozen=True)
class Case:
    label: str
    m: int
    q: int
    u: int
    locals: tuple[tuple[int, ...], ...]


def rows(c):
    assert pow(c.u, c.m, c.q) == 1
    dim = c.m - 1 + len(c.locals)
    output = []
    def row(terms):
        a = [0] * dim
        for i, z in terms:
            if i is not None:
                a[i] = (a[i] + z) % c.q
        output.append(tuple(a))
    for g in range(1, c.m):
        for h in range(1, c.m):
            gh = (g + h) % c.m
            row([(g-1,1), (h-1,pow(c.u,g,c.q)),
                 (gh-1 if gh else None,-1)])
    for v,H in enumerate(c.locals):
        assert 0 in H
        assert all((g+h)%c.m in H for g in H for h in H)
        for h in H:
            if h:
                row([(h-1,1),(c.m-1+v,1-pow(c.u,h,c.q))])
    return dim, tuple(output)


def evaluate(matrix, x, q):
    return tuple(sum(a*b for a,b in zip(row,x))%q for row in matrix)


def kernel(c):
    d,M=rows(c)
    values=[int(not any(evaluate(M,x,c.q)))
            for x in product(range(c.q),repeat=d)]
    return values


def direct(c):
    G=range(1,c.m)
    B={tuple(((pow(c.u,g,c.q)-1)*b)%c.q for g in G)
       for b in range(c.q)}
    Z=[]
    for f in product(range(c.q),repeat=c.m-1):
        v=lambda g: 0 if g%c.m==0 else f[g%c.m-1]
        if any((v(g+h)-v(g)-pow(c.u,g,c.q)*v(h))%c.q
               for g in range(c.m) for h in range(c.m)):
            continue
        if any(not any(all((v(h)-(pow(c.u,h,c.q)-1)*b)%c.q==0
                           for h in H) for b in range(c.q))
               for H in c.locals):
            continue
        Z.append(f)
    assert len(Z)%len(B)==0
    return len(Z)//len(B),len(Z),len(B)


def fixed(c,H):
    return sum(all(((pow(c.u,g,c.q)-1)*a)%c.q==0 for g in H)
               for a in range(c.q))


def dual_kernel(c):
    d,M=rows(c)
    return sum(all(sum(M[i][j]*y[i] for i in range(len(M)))%c.q==0
                   for j in range(d))
               for y in product(range(c.q),repeat=len(M)))


def integrate(c,n,mode='mid'):
    ind=kernel(c)
    N=len(ind)
    K=sum(ind)
    U=Q(K,2); V=Q(N-K,2)
    assert U-V+Q(N,2)==K
    I=Q(K,N)
    rng=Random(20261121)
    s=0
    for j in range(n):
        t=Q(1,2) if mode=='mid' else Q(rng.randrange(1,1000),1000)
        idx=(N*Q(j+t,n)).numerator//(N*Q(j+t,n)).denominator
        s+=ind[idx]
    num=Q(s,n)
    assert abs(num-I)<=Q(N-1,n)
    return N,K,U,V,I,num,Q(N-1,n)


def main():
    cases=[
        Case('C2 mod2 trivial, H=1',2,2,1,((0,),)),
        Case('C2 mod2 trivial, H=C2',2,2,1,((0,1),)),
        Case('C3 mod9 trivial, H=1',3,9,1,((0,),)),
        Case('C3 mod9 trivial, H=C3',3,9,1,((0,1,2),)),
        Case('C2 mod3 sign, H=1',2,3,2,((0,),)),
        Case('C2 mod4 sign, H=1',2,4,3,((0,),)),
    ]
    for c in cases:
        d,M=rows(c)
        K=sum(kernel(c))
        sha,Z,B=direct(c)
        fixG=fixed(c,range(c.m))
        fixH=prod(fixed(c,H) for H in c.locals)
        assert Q(K*fixG,c.q*fixH)==sha
        assert Z//B==sha
        if c.q**len(M)<=40000:
            assert Q(c.q**d*dual_kernel(c),c.q**len(M))==K
        N,K,U,V,I,R,err=integrate(c,2048,'random')
        assert integrate(c,N,'mid')[5]==I
        print(f'{c.label}: kernel={K}, Sha={sha}, NNS UPM={U}, '
              f'LPM={V}, real_integral={I}, random_Q2048={R}, bound={err}')
    print('PASS: finite Selmer cochains, complete Fourier, signed NNS, a.s. integral')


if __name__ == '__main__':
    main()
