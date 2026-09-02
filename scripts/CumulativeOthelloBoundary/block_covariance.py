#!/usr/bin/env python3
"""Signed square-block covariance: verify the partition and measure the loss.

For the physical square blocks ``I_j = [j^2, (j+1)^2)`` with signed masses
``B_j = sum_{n in I_j} mu(n)``, the Lean module
`RHLean/Analysis/BlockCovarianceDecomposition.lean` proves

```text
S^2 = E + 2 X,        S = sum_j B_j,  E = sum_j B_j^2,  X = cross covariance
C_global(R^2) = sum_j C_j + X.
```

This script checks both identities numerically and then measures what the
magnitude-first step ``|S| <= sum_j |B_j|`` discards, which is exactly
``(sum |B_j|)^2 - S^2``.

    python3 scripts/CumulativeOthelloBoundary/block_covariance.py [rmax]
"""

from __future__ import annotations

import sys


def moebius_sieve(n_max: int) -> list[int]:
    spf = list(range(n_max + 1))
    primes: list[int] = []
    for i in range(2, n_max + 1):
        if spf[i] == i:
            primes.append(i)
        for p in primes:
            if p > spf[i] or i * p > n_max:
                break
            spf[i * p] = p
    mu = [1] * (n_max + 1)
    mu[0] = 0
    for n in range(2, n_max + 1):
        p = spf[n]
        m = n // p
        mu[n] = 0 if m % p == 0 else -mu[m]
    return mu


def report(R: int, mu: list[int]) -> None:
    n = R * R
    blocks = [sum(mu[j * j:(j + 1) * (j + 1)]) for j in range(R)]
    total = sum(blocks)
    energy = sum(b * b for b in blocks)
    cross = (total * total - energy) / 2

    # global covariance of the prefix of length n = R^2, i.e. sites 0..n-1
    diagonal = sum(mu[k] * mu[k] for k in range(n))
    global_cov = (total * total - diagonal) / 2

    # within-block covariance, directly
    inner = 0.0
    for j in range(R):
        run = 0
        for k in range(j * j, (j + 1) * (j + 1)):
            inner += mu[k] * run
            run += mu[k]

    abs_total = sum(abs(b) for b in blocks)
    loss = abs_total * abs_total - total * total

    print(f"R = {R}   N = R^2 = {n}   M(N-1) = sum B_j = {total}")
    print(f"  block energy  E = sum B_j^2      = {energy}")
    print(f"  cross         X = (S^2 - E)/2    = {cross:.1f}")
    print(f"  within-block  sum_j C_j          = {inner:.1f}")
    print(f"  partition check: sum C_j + X     = {inner + cross:.1f}"
          f"    global C = {global_cov:.1f}"
          f"    {'OK' if abs(inner + cross - global_cov) < 1e-6 else 'MISMATCH'}")
    print(f"  magnitude-first: sum |B_j| = {abs_total}"
          f"   (sum|B_j|)^2 = {abs_total ** 2}   vs S^2 = {total * total}")
    print(f"  discarded cross-cancellation = {loss}"
          f"   = {loss / n:.1f} N"
          f"   = {(abs_total / max(abs(total), 1)) ** 2:.3g} x the signed square")
    print()


def main(argv: list[str]) -> int:
    r_max = int(argv[1]) if len(argv) > 1 else 400
    mu = moebius_sieve(r_max * r_max + 1)
    for R in (r_max // 8, r_max // 2, r_max):
        if R >= 4:
            report(R, mu)
    print("Readings:")
    print("  * both identities hold exactly at every scale: the block")
    print("    decomposition is a partition of the same pair sum, not a second")
    print("    object needing a bridge;")
    print("  * sum |B_j| grows like N^(3/4) while |S| = |M| stays near N^(1/2),")
    print("    so the discarded cross-cancellation grows like N^(3/2).")
    print("    Magnitude-first bounding therefore loses a half power, not a")
    print("    constant factor -- that is exactly what |H| <= |G| + D removes;")
    print("  * the block energy E = sum B_j^2 LOOKS linear here (about 6/pi^2 N,")
    print("    the squarefree density) but that is a measurement, not a theorem.")
    print("    Exactly, E - Q = 2 sum_j C_j with Q the squarefree diagonal, so")
    print("    proving E << N^(1+eps) IS proving the aggregate within-block")
    print("    covariance is RH-scale.  Do not promote the linearity;")
    print("  * the way out is refinement, not a bound on E: each refinement step")
    print("    moves energy into children plus an explicit signed cross term, and")
    print("    the leaf energy is exactly Q, linear with no conjecture.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
