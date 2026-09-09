#!/usr/bin/env python3
"""Finite diagnostic for the frozen second-contact window ledger.

Diagnostic only.  Numerical evidence is a filter, never proof; the compiled
identities live in
`RHLean/Proof/LowWheelFrozenSecondContactWindowReassembly.lean`.

Objects, with `X = squareRootEndpoint R = R^2 - 1` and

    F_{q^-}(y) = sum over squarefree m <= y with P+(m) < q of mu(m):

  * repo window   D_q = F_{q^-}(X/q) - F_{q^-}(X/q^2)          -- #628 as compiled
  * plan window   D_q = F_{q^-}(X/q) - F_{q^-}(max(R, X/q^2))  -- with an added
                                                                  floor at R

What this script checks:

1. The child-owner reassembly identity is exact (it agrees with the direct
   ledger sum term by term).
2. The reassembled double sum has an exact closed form: it is a single signed
   sum over the largest-prime-factor region

       sum_q D_q = - sum over squarefree n <= X with P+(n) < R
                     and n * P+(n) > X of mu(n),

   i.e. the reassembly is an exact re-partition of the same family by top
   prime.  It reorganizes the ledger; it does not cancel any part of it.
3. The two windows live at different scales.  The compiled #628 window grows
   like c * R^2 / (log R)^2; the floored window stays near R and changes sign.

Run: python3 scripts/FrozenSecondContactReassembly/second_contact_window_scale.py
"""

from __future__ import annotations

import argparse
import math


def sieve(n_max: int) -> tuple[list[int], bytearray, list[int]]:
    """Return (mobius, squarefree flag, largest prime factor) up to n_max."""
    mu = [1] * (n_max + 1)
    squarefree = bytearray([1]) * (n_max + 1)
    largest = [0] * (n_max + 1)
    composite = bytearray(n_max + 1)
    for p in range(2, n_max + 1):
        if composite[p]:
            continue
        for k in range(p, n_max + 1, p):
            if k > p:
                composite[k] = 1
            mu[k] = -mu[k]
            largest[k] = p
        for k in range(p * p, n_max + 1, p * p):
            squarefree[k] = 0
            mu[k] = 0
    return mu, squarefree, largest


def frozen_window(a: int, b: int, q: int, mu, squarefree, largest) -> int:
    """F_{q^-}(b) - F_{q^-}(a) over the half-open window (a, b]."""
    total = 0
    for m in range(a + 1, b + 1):
        if m == 1:
            total += 1
        elif squarefree[m] and largest[m] < q:
            total += mu[m]
    return total


def ledger_direct(R: int, primes, mu, squarefree, largest, floor_at_R: bool) -> int:
    X = R * R - 1
    total = 0
    for q in primes:
        if q >= R:
            break
        lower = X // (q * q)
        if floor_at_R:
            lower = max(R, lower)
        total += frozen_window(lower, X // q, q, mu, squarefree, largest)
    return total


def ledger_reassembled(R: int, primes, mu, squarefree, largest) -> int:
    """-sum_r sum_{q>r} (F_{r^-}(X/(q r)) - F_{r^-}(X/(q^2 r)))."""
    X = R * R - 1
    live = [q for q in primes if q < R]
    total = 0
    for r in live:
        for q in live:
            if q > r:
                total -= frozen_window(
                    X // (q * q * r), X // (q * r), r, mu, squarefree, largest
                )
    return total


def ledger_closed_form(R: int, mu, squarefree, largest) -> int:
    """-sum over squarefree n <= X, P+(n) < R, n * P+(n) > X of mu(n)."""
    X = R * R - 1
    return -sum(
        mu[n]
        for n in range(2, X + 1)
        if squarefree[n] and largest[n] < R and n * largest[n] > X
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--identity-max", type=int, default=210)
    parser.add_argument("--scale-max", type=int, default=1600)
    args = parser.parse_args()

    n_max = max(args.identity_max, args.scale_max) ** 2
    mu, squarefree, largest = sieve(n_max)
    primes = [p for p in range(2, args.scale_max) if largest[p] == p]

    print("== 1/2. reassembly identity and closed form (#628 window) ==")
    print(f"{'R':>6} {'direct':>10} {'reassembled':>12} {'closed form':>12} {'agree':>6}")
    failures = 0
    checks = [R for R in (5, 7, 10, 13, 20, 31, 50, 64, 100, 137, 200, 210)
              if R <= args.identity_max]
    for R in checks:
        direct = ledger_direct(R, primes, mu, squarefree, largest, floor_at_R=False)
        reassembled = ledger_reassembled(R, primes, mu, squarefree, largest)
        closed = ledger_closed_form(R, mu, squarefree, largest)
        agree = direct == reassembled == closed
        failures += 0 if agree else 1
        print(f"{R:>6} {direct:>10} {reassembled:>12} {closed:>12} {str(agree):>6}")

    print()
    print("== 3. scale of the two windows ==")
    print(
        f"{'R':>6} {'#628 window':>12} {'/(R^2/log^2 R)':>15} "
        f"{'floored window':>15} {'/R':>8}"
    )
    scales = [R for R in (100, 200, 400, 800, 1600) if R <= args.scale_max]
    for R in scales:
        repo = ledger_closed_form(R, mu, squarefree, largest)
        floored = ledger_direct(R, primes, mu, squarefree, largest, floor_at_R=True)
        norm = R * R / math.log(R) ** 2
        print(
            f"{R:>6} {repo:>12} {repo / norm:>15.4f} {floored:>15} "
            f"{floored / R:>8.3f}"
        )

    print()
    if failures:
        print(f"FAIL: {failures} identity check(s) disagreed.")
        return 1
    print("All identity checks agree.")
    print(
        "Reading: the compiled #628 window tracks c*R^2/(log R)^2 with c ~ 0.3 and "
        "never changes sign; the floored window stays near R and oscillates.  The "
        "floor at R is therefore load-bearing, and it is not supplied by the "
        "second-contact geometry."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
