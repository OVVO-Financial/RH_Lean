#!/usr/bin/env python3
"""Actual split-prime Eisenstein sextic-residue correlation sanity probe.

For primary coprime split-prime generators u,v in the SAME physical
mod-4 ray, the CRT solution of the supported fullModulusCorrelation
at a coprime sixth-power frequency w^6 has phase

    chi_u(v)^(-1) * chi_v(-u) = +1.

This tests primary generators and actual residue-field sextic chars.
It is NOT a proof of the full global low Gaussian bound.
"""
from math import isclose


def nrm(v):
    a, b = v
    return a*a-a*b+b*b


def prime(p):
    return p >= 2 and all(p % d for d in range(2, int(p**0.5)+1))


def powmod(x, n, p):
    return pow(x, n, p)


def chi6(base, arg):
    p = nrm(base)
    assert prime(p) and p % 6 == 1
    a, b = base
    assert b % p != 0
    w = (-a * pow(b, -1, p)) % p
    zeta = (1 + w) % p     # primitive global sixth root 1+omega
    assert pow(zeta, 6, p) == 1
    assert all(pow(zeta, j, p) != 1 for j in (1, 2, 3))
    x = (arg[0] + w*arg[1]) % p
    if x == 0:
        return None       # character zero on nonunits
    sixth = powmod(x, (p-1)//6, p)
    for e in range(6):
        if powmod(zeta, e, p) == sixth:
            return e
    raise AssertionError("not a sextic root")


def mul(x, y):
    a,b=x; c,d=y
    return (a*c-b*d, a*d+b*c-b*d)


def corr_exponent(u, v):
    e_uv = chi6(u, v)
    e_vu = chi6(v, u)
    e_vminus = chi6(v, (-1,0))
    if None in (e_uv, e_vu, e_vminus):
        raise AssertionError("noncoprime source primes")
    # χ_u(v)^-1 χ_v(-u) = χ_u(v)^-1 χ_v(u) χ_v(-1)
    return (-e_uv + e_vu + e_vminus) % 6


def main():
    # Verified primary modulo the ramified squared prime (3):
    pairs=[
        ((-2,-3),(-2,9)),    # norms 7,103, ray (2,1)
        ((-2,-3),(10,-3)),   # norms 7,139, ray (2,1)
        ((-2,-3),(-14,-3)),  # norms 7,163, ray (2,1)
        ((1,-3),(1,9)),      # norms 13,73, ray (1,1)
        ((-5,-6),(7,6)),    # norms 31,43, ray (3,2)
        ((-5,-3),(7,9)),    # norms 19,67, ray (3,1)
    ]
    checks=0
    for u,v in pairs:
        assert (u[0]%3,u[1]%3)==(1,0)
        assert (v[0]%3,v[1]%3)==(1,0)
        assert (u[0]%4,u[1]%4)==(v[0]%4,v[1]%4)
        e=corr_exponent(u,v)
        assert e==0,(u,v,e)
        print("same-ray primes",nrm(u),nrm(v),"ray",(u[0]%4,u[1]%4),
              "CRT sixth-frequency phase +1")
        checks+=1
    # Different rays need NOT have +1: the ray sign matters.
    u,v=(-2,-3),(1,-3)
    assert (u[0]%4,u[1]%4)!=(v[0]%4,v[1]%4)
    assert corr_exponent(u,v)==3
    print("cross-ray 7/13 CRT phase -1 (expected control)")

    # Actual sixth-power frequency does not change the local prime
    # factors: χ_p(w^6)=1 on units.
    z=(1,2)
    zz=(1,0)
    for _ in range(6):
        zz=mul(zz,z)
    for u,v in pairs:
        assert chi6(u,zz)==0 and chi6(v,zz)==0
    print("PASS",checks,"same-ray Eisenstein prime pairs, cross-ray control,"
          " and exact character invariance under sixth powers")


if __name__ == "__main__":
    main()
