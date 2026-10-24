#!/usr/bin/env python3
"""Independent standard-library counterexample to universal one-block VF capture.

The statement vfMidIntegerBlockCaptured R is that floor(F_R) lies between
pi(R^2) and pi((R+1)^2) inclusive. This exact arithmetic check at R=549
falsifies the universal quantifier, not the weaker von Koch channel goal.
"""
import math


def prime_counts_at(n1, n2):
    assert 0 < n1 < n2
    sieve = bytearray([1]) * (n2 + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, math.isqrt(n2) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n2 + 1 : p] = bytes(len(sieve[start : n2 + 1 : p]))
    return sum(sieve[: n1 + 1]), sum(sieve)


def main():
    R = 549
    left, right = prime_counts_at(R * R, (R + 1) ** 2)
    mass = math.fsum(
        (2 * r + 1) / math.log(r * r + r + 0.5)
        for r in range(2, R)
    )
    raw_level = math.floor(mass)
    canon_level = math.floor(mass + math.sqrt(2))
    print(f"R={R} pi(R^2)={left} pi((R+1)^2)={right}")
    print(f"F_R={mass:.12f} floor(F_R)={raw_level}")
    print(f"floor(F_R+sqrt(2))={canon_level}")
    assert left == 26112
    assert right == 26193
    assert raw_level == 26194
    assert canon_level == 26196
    assert not (left <= raw_level <= right)
    assert not (left <= canon_level <= right)
    print("PASS: universal literal one-block capture is false")


if __name__ == "__main__":
    main()
