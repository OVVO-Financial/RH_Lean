#!/usr/bin/env python3
"""Exact finite Euler square-root cutoff and C/A diagnostic.

Runs finite arithmetic identities only; does NOT certify a universal C or A.

Example:
    python3 scripts/euler_finite_ca_cutoff_audit.py 2 3 5 10 56 317
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from fractions import Fraction


def mobius_sieve(limit: int):
    mu = [0] * (limit + 1)
    spf = [0] * (limit + 1)
    mu[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p > spf[n] or n * p > limit:
                break
            spf[n * p] = p
            if p == spf[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return mu, spf, primes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "roots", type=int, nargs="*", default=[2, 3, 5, 10, 56, 317]
    )
    args = parser.parse_args(argv)
    roots = sorted(set(args.roots))
    if not roots or min(roots) < 2:
        parser.error("all roots must be integers >= 2")

    limit = max(r * r - 1 for r in roots)
    mu, spf, primes = mobius_sieve(limit)
    m = [0] * (limit + 1)
    largest_prime = [0] * (limit + 1)
    for n in range(1, limit + 1):
        m[n] = m[n - 1] + mu[n]
        if n > 1:
            largest_prime[n] = max(spf[n], largest_prime[n // spf[n]])

    weighted_prefix = [0.0] * (max(roots) + 1)
    for n in range(1, max(roots) + 1):
        weighted_prefix[n] = (
            weighted_prefix[n - 1] + (mu[n] ** 2) / n
        )

    fields = [
        "R", "X", "M_X", "M_R_minus_1", "low_smooth",
        "high_descendants", "Q_direct", "Q_Euler", "K", "C_ratio",
        "A_ratio", "prime_reciprocal_sum", "high_energy_over_history",
    ]
    writer = csv.DictWriter(sys.stdout, fieldnames=fields)
    writer.writeheader()

    for r in roots:
        x = r * r - 1
        low = sum(
            mu[n] for n in range(1, x + 1) if largest_prime[n] < r
        )
        high_primes = [p for p in primes if r <= p <= x]
        high = -sum(m[x // p] for p in high_primes)
        assert low + high == m[x], (r, low, high, m[x])

        # Original signed bilinear floor kernel, computed independently.
        q = 0
        for a in range(1, r):
            if mu[a]:
                for b in range(1, r):
                    if mu[b]:
                        q += mu[a] * mu[b] * (x // (a * b))
        q_euler = 2 * m[r - 1] - m[x]
        assert q == q_euler, (r, q, q_euler)

        # Strict historical K uses only y < r, including y=0.
        k = max(
            (Fraction((m[y] - 1) ** 2, y + 1) for y in range(r)),
            default=Fraction(1),
        )
        assert k >= 1
        c_ratio = abs(q) / (r * math.sqrt(float(k)))
        a_ratio = (m[x] - 1) ** 2 / (r * r * float(k))

        # Critical-line Euler mean square and reciprocal descendant energy.
        inv_sum = sum(1.0 / p for p in high_primes)
        hist_energy = weighted_prefix[r - 1]
        new_energy = sum(
            weighted_prefix[x // p] / p for p in high_primes
        )
        assert inv_sum <= 5 / 6 + 1e-12, (r, inv_sum)
        assert new_energy <= (5 / 6) * hist_energy + 1e-12

        # Only verifies the algebraic pointwise implication; not a
        # universal C estimate.
        assert (
            math.sqrt(a_ratio)
            <= c_ratio + math.sqrt(2) + 0.5 + 1e-10
        )

        writer.writerow(
            dict(
                R=r, X=x, M_X=m[x], M_R_minus_1=m[r - 1],
                low_smooth=low, high_descendants=high,
                Q_direct=q, Q_Euler=q_euler, K=str(k),
                C_ratio=f"{c_ratio:.10f}",
                A_ratio=f"{a_ratio:.10f}",
                prime_reciprocal_sum=f"{inv_sum:.10f}",
                high_energy_over_history=f"{new_energy / hist_energy:.10f}",
            )
        )


if __name__ == "__main__":
    main()
