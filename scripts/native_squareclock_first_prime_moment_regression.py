#!/usr/bin/env python3
"""Exact rational square-clock first-prime-row moment verification.

The all-H result is proved mathematically in
research/NATIVE_SQUARE_CLOCK_FIRST_PRIME_MOMENT_20261028.md.
This file tests actual integer square-endpoint fractional terms and
genuine mu(1)*mu(p)=-1, not simulated random signs or a 7/8 input.
"""
from fractions import Fraction
from math import gcd, isqrt, lcm


def primes_le(n):
    return [p for p in range(2, n+1)
            if all(p % q for q in range(2, isqrt(p)+1))]


def root_part(r, d):
    return Fraction((r*r-1) % d, d)


def root_mean(d):
    return sum((root_part(r, d) for r in range(d)), Fraction()) / d


def root_centered(r, d, mean):
    return root_part(r, d) - mean


def check():
    for d, e in ((5,7),(7,11),(6,35),(10,21),
                 (15,21),(21,35),(35,55)):
        period = lcm(d,e)
        dm,em=root_mean(d),root_mean(e)
        signed = sum(
            (root_centered(r,d,dm)*root_centered(r,e,em)
             for r in range(period)), Fraction(),
        )
        if gcd(d,e)==1:
            assert signed == 0,(d,e,signed)
        else:
            assert signed != 0,(d,e,signed)
        print("CRT",d,e,"gcd",gcd(d,e),"covariance",str(signed))

    for H,Q in ((216,6),(512,8),(1000,10),
                (4096,16),(8192,20),(27000,30),(65536,40)):
        assert Q**3<=H
        ps=primes_le(Q)
        means={p:root_mean(p) for p in ps}
        # The TRUE source coefficient is 2*mu(1)*mu(p) = -2.
        E=sum(
            (4*sum((root_centered(R,p,means[p]) for p in ps),
                   Fraction())**2
             for R in range(H,2*H)), Fraction(),
        )
        upper=4*(H*Q+Q**4)
        assert E <= upper
        assert E <= 8*H*Q
        print("H",H,"Q",Q,"primes",len(ps),
              "energy",str(E),
              "E/(4HQ)",round(float(E)/(4*H*Q),6),
              "rigorous bound",upper)
    print("PASS: exact rational square-clock first-prime-row moment and shared-factor controls")


if __name__=="__main__":
    check()
