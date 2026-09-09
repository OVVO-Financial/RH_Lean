#!/usr/bin/env python3
"""Finite diagnostics for the frozen second-contact ledger.

Diagnostic only.  Numerical evidence is a filter, never proof.  The compiled
identities live in `RHLean/Proof/LowWheelFrozenSecondContactWindowDescent.lean`
(#629, the saturated carrier) and
`RHLean/Proof/LowWheelFrozenSecondContactWindowReassembly.lean` (the superseded
`X_R/q^2` carrier, kept as a recorded no-go).

With `X = squareRootEndpoint R = R^2 - 1` and

    F_{q^-}(y) = sum over squarefree m <= y with P+(m) < q of mu(m),

two carriers are compared:

  * loose (#628)     D_q = F_{q^-}(X/q) - F_{q^-}(X/q^2)
  * saturated (#629) D_q = F_{q^-}(X/q) - F_{q^-}(max(R, X/q^2))

Section 1 verifies the closed forms.  Reindexing each ledger by `n = q * m`,
the loose ledger is a largest-prime-factor sum and the saturated one adds the
root floor `n / P+(n) > R`:

    loose      = - sum mu(n) over squarefree n <= X, P+(n) < R, n*P+(n) > X
    saturated  = - sum of the same terms with additionally n/P+(n) > R

Section 2 measures both.  Section 3 sweeps the saturated ledger densely for its
envelope.  Section 4 splits the saturated ledger into the child-owner columns of
`lowWheelFrozenSecondContactChildOwnerColumn` (group by `r = P+(n/P+(n))`) and
compares `sum_r |col_r|` against `|sum_r col_r|` -- i.e. asks whether a triangle
inequality at the column level is affordable.

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


def ledger_direct(R, mu, squarefree, largest, *, floored: bool) -> int:
    """sum over prime owners q < R of the owner window mass."""
    X = R * R - 1
    total = 0
    for q in range(2, R):
        if largest[q] != q:
            continue
        lower = X // (q * q)
        if floored:
            lower = max(R, lower)
        for m in range(lower + 1, X // q + 1):
            if m == 1:
                total += 1
            elif squarefree[m] and largest[m] < q:
                total += mu[m]
    return total


def ledger_closed(R, mu, squarefree, largest, *, floored: bool) -> int:
    X = R * R - 1
    total = 0
    for n in range(2, X + 1):
        if not squarefree[n]:
            continue
        q = largest[n]
        if q < R and n * q > X and (not floored or n > R * q):
            total += mu[n]
    return -total


def child_owner_columns(R, mu, squarefree, largest) -> dict[int, int]:
    """Saturated ledger split by child owner r = P+(n / P+(n))."""
    X = R * R - 1
    columns: dict[int, int] = {}
    for n in range(R + 1, X + 1):
        if not squarefree[n]:
            continue
        q = largest[n]
        if q < R and n * q > X and n > R * q:
            m = n // q
            r = largest[m] if m > 1 else 1
            columns[r] = columns.get(r, 0) - mu[n]
    return columns


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--identity-max", type=int, default=200)
    parser.add_argument("--scale-max", type=int, default=800)
    parser.add_argument("--sweep-max", type=int, default=800)
    parser.add_argument("--sweep-step", type=int, default=10)
    args = parser.parse_args()

    n_max = max(args.identity_max, args.scale_max, args.sweep_max) ** 2
    mu, squarefree, largest = sieve(n_max)
    failures = 0

    print("== 1. closed forms ==")
    print(f"{'R':>6} {'loose':>9} {'closed':>9} {'saturated':>11} {'closed':>9} {'ok':>5}")
    for R in (50, 100, 200, 400):
        if R > args.identity_max:
            continue
        a = ledger_direct(R, mu, squarefree, largest, floored=False)
        b = ledger_closed(R, mu, squarefree, largest, floored=False)
        c = ledger_direct(R, mu, squarefree, largest, floored=True)
        d = ledger_closed(R, mu, squarefree, largest, floored=True)
        ok = a == b and c == d
        failures += 0 if ok else 1
        print(f"{R:>6} {a:>9} {b:>9} {c:>11} {d:>9} {str(ok):>5}")

    print()
    print("== 2. what the root floor of #629 buys ==")
    print(f"{'R':>6} {'loose':>10} {'/(R^2/log^2R)':>14} {'saturated':>11} {'/(R log R)':>11}")
    for R in (100, 200, 400, 800):
        if R > args.scale_max:
            continue
        loose = ledger_closed(R, mu, squarefree, largest, floored=False)
        sat = ledger_closed(R, mu, squarefree, largest, floored=True)
        print(
            f"{R:>6} {loose:>10} {loose / (R * R / math.log(R) ** 2):>14.4f} "
            f"{sat:>11} {sat / (R * math.log(R)):>11.4f}"
        )

    print()
    print("== 3. envelope of the saturated ledger ==")
    values = []
    for R in range(100, args.sweep_max + 1, args.sweep_step):
        values.append((R, ledger_closed(R, mu, squarefree, largest, floored=True)))
    changes = sum(1 for i in range(1, len(values)) if values[i][1] * values[i - 1][1] < 0)
    worst = max(values, key=lambda t: abs(t[1]) / (t[0] * math.log(t[0])))
    print(f"  {len(values)} samples, {changes} sign changes")
    print(
        f"  max |L|/(R log R) = "
        f"{abs(worst[1]) / (worst[0] * math.log(worst[0])):.4f} at R={worst[0]}"
    )

    print()
    print("== 4. is a triangle inequality on the child-owner columns affordable? ==")
    print(f"{'R':>6} {'|ledger|':>9} {'sum|col_r|':>11} {'cols':>5} {'loss factor':>12}")
    for R in (200, 400, 800):
        if R > args.scale_max:
            continue
        columns = child_owner_columns(R, mu, squarefree, largest)
        total = sum(columns.values())
        abs_sum = sum(abs(v) for v in columns.values())
        loss = abs_sum / abs(total) if total else float("inf")
        print(f"{R:>6} {abs(total):>9} {abs_sum:>11} {len(columns):>5} {loss:>11.1f}x")

    print()
    if failures:
        print(f"FAIL: {failures} closed-form check(s) disagreed.")
        return 1
    print("All closed-form checks agree.")
    print(
        "Reading: the root floor of #629 moves the ledger from ~0.3 R^2/(log R)^2 "
        "with constant sign to a sign-changing ~0.2 R log R -- a full power.  But "
        "the child-owner columns must NOT be normed: sum_r |col_r| grows back to "
        "~R^2/(log R)^2, so the entire remaining gain is cancellation BETWEEN "
        "columns, not inside them."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
