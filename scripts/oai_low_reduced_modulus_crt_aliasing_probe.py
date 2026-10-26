#!/usr/bin/env python3
"""Exact CRT zero-mode, but no short-box saving: a rigorous test diagnostic.

This is an ABSTRACT periodic Hermitian Gram-kernel counterexample, not the
original OAI jointExtension. It falsifies the claim that CRT factoring and
zero average over a small modulus automatically yield a period-box power
saving uniformly in a much larger slot modulus.

Take M0=2, slot q odd, full period 2q. Define
  z(n)=exp(2 pi i n/(2q)),  F(x,y)=z(x) conj(z(y)).
Changing the 2-CRT coordinate while holding the q-CRT coordinate fixed
changes x to x+q, and hence z(x) to -z(x). Therefore the conditional
average of F over both 2-coordinates is EXACTLY zero for every pair
of q-slot coordinates; the full Gram F is positive semidefinite rank one.

Yet a short LxL physical box with q>=100L gives
  sum_{x,y=1}^L F(x,y) = |sum_{n=1}^L z(n)|^2
                      >= L^2 cos(pi/100)^2.
The lower bound is deterministic, not an empirical inference.
"""

import cmath
import math


def z(n: int, q: int) -> complex:
    return cmath.exp(1j * math.pi * n / q)


def assert_witness(q: int, length: int) -> None:
    assert q % 2 == 1 and q >= 100 * length
    # For fixed slot residue, the two modulo-(2q) CRT lifts differ by q.
    # The small-factor conditional mean cancels *identically*.
    for s in range(min(q, 31)):
        assert abs(z(s, q) + z(s + q, q)) < 1e-12

    # The two-column Hermitian Gram is PSD by construction:
    # F(x,y)=z(x) conjugate(z(y)).
    short_sum = sum((z(n, q) for n in range(1, length + 1)), 0j)
    gram_box = abs(short_sum) ** 2
    deterministic_lower = length * length * math.cos(math.pi / 100) ** 2
    assert gram_box + 1e-10 >= deterministic_lower
    print(
        f"PASS q={q}, L={length}: CRT bad-factor mean=0 in EVERY "
        f"slot fiber; PSD short-box gram={gram_box:.9f}; "
        f"proven lower bound={deterministic_lower:.9f}; "
        f"ratio={gram_box/(length*length):.9f}"
    )


if __name__ == "__main__":
    for q, length in [(101, 1), (1009, 10), (10007, 100), (100003, 1000)]:
        assert_witness(q, length)
