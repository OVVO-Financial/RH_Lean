#!/usr/bin/env python3
"""Exact physical-prime-power audit for RH_Lean's R-order square-clock jet.

At n=R^2-1 and R>=2,
 Delta^R [psi(n)-n] = sum_{j=0}^{R-1} (-1)^(R-1-j)*C(R-1,j)*Lambda(R^2+j).

All signed binomial coefficients are exact integers; each nonzero
Lambda(m) is represented symbolically as log(p) for the UNIQUE prime
base p of m=p^a. By unique factorization, this logarithmic linear
combination vanishes exactly when EVERY grouped prime coefficient
is zero. No floating-point zero test is used.

The universal coefficient l1 mass is 2^(R-1). The effective physical
prime-power mass is computed exactly, without assuming random primes.
None of this supplies a p-adic geometric multiplicity/covolume bound.
"""
from __future__ import annotations

from collections import defaultdict
from math import comb, gcd, isqrt


def prime_power_base(n: int) -> int | None:
    """Return p when n=p^a for a prime p, else None."""
    if n < 2:
        return None
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return p if m == 1 else None
        p += 1 if p == 2 else 2
    return n


def prime_power_symbolic_root_jet(R: int) -> tuple[dict[int, int], int, int]:
    assert R >= 2
    c: dict[int, int] = defaultdict(int)
    hits = 0
    l1_physical = 0
    for j in range(R):
        n = R * R + j
        p = prime_power_base(n)
        if p is None:
            continue
        weight = (-1 if (R - 1 - j) & 1 else 1) * comb(R - 1, j)
        c[p] += weight
        hits += 1
        l1_physical += abs(weight)
    return {p: w for p, w in c.items() if w}, hits, l1_physical


def run() -> None:
    # The two first native square clocks can be inspected exactly.
    assert prime_power_symbolic_root_jet(2)[0] == {2: -1, 5: 1}
    assert prime_power_symbolic_root_jet(3)[0] == {3: 1, 11: 1}
    assert gcd(48, 7) == 1  # Prior prime-wheel audit's P=2*3*5*7
    print("R,X_R,order,prime_power_hits,distinct_nonzero_log_primes,"
          "universal_l1,physical_l1,ratio_physical_to_universal,"
          "nonzero_by_unique_factorization")
    for R in (2, 3, 4, 5, 8, 16, 32, 64, 127, 317, 1027):
        coeffs, hits, physical = prime_power_symbolic_root_jet(R)
        universal = 1 << (R - 1)
        assert 0 <= physical <= universal
        assert coeffs, "the actual prime-power jet unexpectedly vanished"
        print(",".join(map(str, (
            R, R * R - 1, R, hits, len(coeffs), universal,
            physical, f"{physical/universal:.8g}", "YES"
        ))))
    print("PASS: exact prime-power order-R jet is not automatic vanishing")


if __name__ == "__main__":
    run()
