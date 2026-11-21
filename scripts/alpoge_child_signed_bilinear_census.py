#!/usr/bin/env python3
"""Exact-integer carrier and finite-precision log audit of the Alpoge 2*p slice.

The native source is K2(2*p)*E(floor((R^2-1)/(2*p))).
For genuine odd primes, K2(2*p)=2 log(2) log(p).

Reports weighted L1/L2 coherence of the child G and Chebyshev E channels,
the exact integer quotient injectivity, and double-counted Lambda-minus-one
census equality using the physical incidence kernel. This is finite
evidence, not an RH asymptotic theorem or a geometric covolume estimate.
"""

from __future__ import annotations

import argparse
import json
import math


EULER_GAMMA = 0.57721566490153286060


def census(Rs: list[int]) -> list[dict]:
    max_r = max(Rs)
    sieve = bytearray(b"\x01") * (max_r + 1)
    sieve[0:2] = b"\x00\x00"
    for d in range(2, math.isqrt(max_r) + 1):
        if sieve[d]:
            sieve[d * d : max_r + 1 : d] = b"\x00" * (
                (max_r - d * d) // d + 1
            )
    primes = [p for p in range(2, max_r + 1) if sieve[p]]
    mangoldt = [0.0] * (max_r + 1)
    for p in primes:
        j = p
        while j <= max_r:
            mangoldt[j] = math.log(p)
            j *= p
    psi = [0.0] * (max_r + 1)
    reciprocal = [0.0] * (max_r + 1)
    for n in range(1, max_r + 1):
        psi[n] = psi[n - 1] + mangoldt[n]
        reciprocal[n] = reciprocal[n - 1] + mangoldt[n] / n

    rows = []
    for R in Rs:
        X = R * R - 1
        selected = [p for p in primes if p > 2 and R <= 2 * p and 3 * p <= 2 * R]
        pairs = [(p, X // (2 * p)) for p in selected]
        children = [t for _, t in pairs]
        assert len(set(children)) == len(children), f"quotient collision R={R}"
        assert all(p <= t < R for p, t in pairs), f"ancestry fails R={R}"
        a = [2 * math.log(2) * math.log(p) for p, _ in pairs]
        error = [psi[t] - t for t in children]
        gz = [
            t * (reciprocal[t] - math.log(t) + EULER_GAMMA) - e
            for t, e in zip(children, error)
        ]

        # Reproduce the exact arithmetic finite Fubini sum:
        # Sum_p a_p E(t_p) = Sum_n (Lambda(n)-1)*W(n).
        # W(n) = sum_{p:2pn<=X} a_p; no double counting or dropped powers.
        diff = [0.0] * (R + 1)
        for weight, t in zip(a, children):
            diff[1] += weight
            diff[t + 1] -= weight
        cur = 0.0
        terms = []
        for n in range(1, R):
            cur += diff[n]
            terms.append((mangoldt[n] - 1) * cur)
        bilinear = math.fsum(terms)
        selected_sum = math.fsum(w * e for w, e in zip(a, error))
        assert math.isclose(
            bilinear, selected_sum, rel_tol=1e-8, abs_tol=0.001
        ), (R, bilinear, selected_sum)

        record = {
            "R": R, "m": len(pairs),
            "distinct_child_arguments": len(set(children)),
            "min_t": min(children), "max_t": max(children),
            "bilinear_selected": round(selected_sum, 6),
            "bilinear_reindexed": round(bilinear, 6),
        }
        for name, vector in (("E", error), ("Gz", gz)):
            entries = [w * v for w, v in zip(a, vector)]
            signed = math.fsum(entries)
            diagonal = math.fsum(v * v for v in entries)
            coherence = signed / math.sqrt(diagonal) if diagonal else 0.0
            record[name] = {
                "negative_fraction": round(
                    sum(v < 0 for v in vector) / len(vector), 6
                ),
                "min_value": round(min(vector), 6),
                "max_value": round(max(vector), 6),
                "signed_over_diagonal_L2": round(coherence, 6),
                "effective_coherent_count": round(coherence**2, 6),
                "sqrt_m": round(math.sqrt(len(vector)), 6),
            }
        rows.append(record)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--roots", type=int, nargs="+", default=[317, 549, 1027, 3000, 10000, 30000])
    args = parser.parse_args()
    if any(R < 8 for R in args.roots):
        parser.error("R must be >= 8 for a nonempty child-prime band")
    print(json.dumps(census(args.roots), indent=2))


if __name__ == "__main__":
    main()
