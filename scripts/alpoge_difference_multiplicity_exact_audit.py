#!/usr/bin/env python3
"""Exact arithmetic audit: Boolean prime differences versus Stepanov multiplicity.

For a prime set S with primorial P, RH_Lean's arithmetic operator
D_S f(X) = sum_{d|P} mu(d)*f(floor(X/d))
acts on f(X)=X at X=P as EulerPhi(P)=prod_{p in S}(p-1).

This test uses exact integer subset expansion, NOT floating point or
a probabilistic model. The newest prime p does not divide the
output when S consists of primes up to p, so no p-adic multiplicity
comes automatically from the formal difference order |S|.

This does NOT rule out a genuine geometric theta-lift multiplicity
construction with additional divisibility/height witnesses.
"""
from fractions import Fraction
from itertools import combinations
from math import prod, isqrt


def primes_upto(n: int) -> list[int]:
    ans = []
    for k in range(2, n+1):
        if all(k % p != 0 for p in range(2, isqrt(k)+1)):
            ans.append(k)
    return ans


def difference_of_linear_on_primorial(primes: tuple[int, ...]) -> int:
    P = prod(primes)
    return sum(
        (-1)**j * (P // prod(factors))
        for j in range(len(primes)+1)
        for factors in combinations(primes, j)
    )


def main() -> None:
    print("k,largest_prime,P,D_S(identity)(P),D/P,divisible_by_largest_prime")
    allprimes = primes_upto(29)
    for k in range(1, len(allprimes)+1):
        ps = tuple(allprimes[:k])
        P = prod(ps)
        actual = difference_of_linear_on_primorial(ps)
        predicted = prod(p-1 for p in ps)
        assert actual == predicted
        assert actual % ps[-1] != 0
        print(k, ps[-1], P, actual, Fraction(actual,P), "NO", sep=",")
    assert difference_of_linear_on_primorial((2,3)) == 2
    assert difference_of_linear_on_primorial((2,3,5,7)) == 48
    print("PASS: no automatic high prime divisibility from Boolean order")

if __name__ == "__main__":
    main()
