#!/usr/bin/env python3
"""Signed NNS resolvent quadrature with exact rational samples and an error bound.

Mathematical proof: research/ALPOGE_NNS_RESOLVENT_DISCRETE_MVT_20261121.md.
This is a regression of the numerical certificate, not a proof of a
Galois-cohomological presentation or of RH.
"""
from fractions import Fraction as F
from math import log
from random import Random

# M=[[1,4],[0,2]], B=M^T M=[[1,4],[4,20]]
D, L, M = 2, 21, 2
U = min(F(1), F(D * D, L))


def kernel(t: F) -> F:
    assert t >= 0
    h_resolvent = F(M, 1) / (1 + t) - (21 + 2*t) / (t*t + 21*t + 4)
    h_simplified = (19*t - 13) / ((1+t)*(t*t + 21*t + 4))
    assert h_resolvent == h_simplified
    return h_simplified


def certified_error(n: int, T: F) -> F:
    assert n >= 1 and T > 0
    return (T/n)*M*(1+1/U) + F(L+M)/(T+U)


def quadrature(n: int, T: F, mode: str = "left") -> tuple[F, F, F]:
    assert n >= 1 and T > 0
    delta = T/n
    rng = Random(20261121)
    up = low = F(0)
    for j in range(n):
        if mode == "left":
            shift = F(0)
        elif mode == "right":
            shift = F(1)
        elif mode == "mid":
            shift = F(1,2)
        elif mode == "random":
            shift = F(rng.randrange(1001),1000)
        else:
            raise ValueError(mode)
        f = kernel((j+shift)*delta)
        up += max(F(0), f)
        low += max(F(0), -f)
    return delta*up, delta*low, delta*(up-low)


def main() -> None:
    assert U == F(4,21)
    assert kernel(F(0)) == F(-13,4)
    assert kernel(F(13,19)) == 0
    assert kernel(F(1)) == F(3,26)
    for n,T in ((100,F(10)), (1000,F(32)), (10000,F(100))):
        bound = certified_error(n,T)
        for mode in ("left", "right", "mid", "random"):
            up, low, q = quadrature(n,T,mode)
            assert up >= 0 and low >= 0 and q == up-low
            # Floating-point regression only. The exact bound is proved
            # analytically for ALL tags in the research document.
            assert abs(float(q)-log(4)) < float(bound) + 1e-12
        up, low, q = quadrature(n,T)
        print(f"n={n} T={T} UPM={float(up):.12f} LPM={float(low):.12f} "
              f"Q={float(q):.12f} certified_error<={float(bound):.12f}")
    print("PASS: exact-rational signed NNS quadrature and numerical error regressions")


if __name__ == "__main__":
    main()
