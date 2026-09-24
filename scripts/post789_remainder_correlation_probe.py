#!/usr/bin/env python3
"""Exact finite audit: the post-789 signed remainder is the CORR square.

Every quantity is transcribed from a compiled definition:

    squareRootEndpoint R        = R^2 - 1
    canonicalRoughLowQ2Owners R = odd primes q < R with q*q < R
    rawQ2ChildCutoff R q        = (R^2 - 1) // (q*q)
    Q_R  = lowOwnerReciprocalMertensColumnReal R = sum_q M(cutoff_q) / q
    G_R  = lowOwnerPost789EndpointGapReal R      = M(R^2 - 1) - M(R - 1)
    D_R  = lowOwnerZeroFrequencyMobiusDiagonal R = sum_{n sqfree} w(n)^2,
           w(n) = [n >= R] + sum_q [n <= cutoff_q] / q
    E_R  = canonicalRoughLowQ2DaughterEnergy R   = sum_q M(cutoff_q)^2
    X_R  = lowOwnerPost789SignedCrossDiagonalRemainder R
         = G_R^2 + 2 Q_R G_R - D_R
    corr = squareRootCanonicalRoughCorrelation R = M(R - 1) - M(R^2 - 1) = -G_R

The weight is the one used by `top_two_completed_branch_probe.py`, whose
assertions tie it to the compiled final Stokes boundary.  All arithmetic is
exact over the common denominator prod(q).

The script checks the two-sided comparison proved in
`research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean`:

    corr^2 / 2 - 2 Q_R^2 - D_R  <=  X_R  <=  2 corr^2 + Q_R^2,

and reports where the sign of X_R comes from.  Numerical output is a filter,
not a proof.
"""

from __future__ import annotations

import argparse
from math import prod


def mobius_table(limit: int) -> list[int]:
    mu = [1] * (limit + 1)
    is_composite = bytearray(limit + 1)
    primes: list[int] = []
    mu[0] = 0
    for n in range(2, limit + 1):
        if not is_composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            m = n * p
            if m > limit:
                break
            is_composite[m] = 1
            if n % p == 0:
                mu[m] = 0
                break
            mu[m] = -mu[n]
    return mu


def odd_primes_with_square_below(root: int) -> list[int]:
    return [
        q for q in range(3, root, 2)
        if q * q < root and all(q % d for d in range(3, int(q ** 0.5) + 1, 2))
    ]


def measure(root: int, mertens: list[int], squarefree: list[int]) -> dict:
    endpoint = root * root - 1
    owners = odd_primes_with_square_below(root)
    denom = prod(owners)
    cutoffs = [endpoint // (q * q) for q in owners]

    gap = mertens[endpoint] - mertens[root - 1]
    column_num = sum((denom // q) * mertens[c] for q, c in zip(owners, cutoffs))
    energy = sum(mertens[c] ** 2 for c in cutoffs)

    # D_R * denom^2: the weight is a step function with jumps after R - 1 and
    # after every cutoff, so sum squarefree counts over constant pieces.
    breaks = sorted({0, root - 1, endpoint, *cutoffs})
    diagonal_num = 0
    for lo, hi in zip(breaks, breaks[1:]):
        n = hi  # representative of the constant piece (lo, hi]
        w = (denom if n >= root else 0) + sum(
            denom // q for q, c in zip(owners, cutoffs) if n <= c
        )
        diagonal_num += (squarefree[hi] - squarefree[lo]) * w * w

    d2 = denom * denom
    corr_sq_num = gap * gap * d2
    remainder_num = corr_sq_num + 2 * column_num * gap * denom - diagonal_num
    column_sq_num = column_num * column_num

    # Exact two-sided comparison, cleared of denominators (times 2).
    lower_num = corr_sq_num - 4 * column_sq_num - 2 * diagonal_num
    upper_num = 4 * corr_sq_num + 2 * column_sq_num
    assert lower_num <= 2 * remainder_num <= upper_num, root
    # Quarter frame used on both sides: Q_R^2 <= E_R / 4.
    assert 4 * column_sq_num <= energy * d2, root

    return {
        "R": root,
        "corr_sq": gap * gap,
        "Q": column_num / denom,
        "E": energy,
        "D": diagonal_num / d2,
        "X": remainder_num / d2,
        "X_plus_D": (remainder_num + diagonal_num) / d2,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-root", type=int, default=400)
    parser.add_argument("--min-root", type=int, default=56)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    if args.min_root < 56:
        parser.error("the post-789 consumer requires R >= 56")

    limit = args.max_root * args.max_root - 1
    mu = mobius_table(limit)
    mertens = [0] * (limit + 1)
    squarefree = [0] * (limit + 1)
    for n in range(1, limit + 1):
        mertens[n] = mertens[n - 1] + mu[n]
        squarefree[n] = squarefree[n - 1] + (1 if mu[n] else 0)

    rows = [measure(r, mertens, squarefree)
            for r in range(args.min_root, args.max_root + 1)]
    # Exact lower critical envelope: K_R = max_{y < R} (M(y) - 1)^2 / (y + 1).
    envelope, running = {}, 0.0
    for y in range(args.max_root):
        running = max(running, (mertens[y] - 1) ** 2 / (y + 1))
        envelope[y + 1] = running
    if args.verbose:
        for row in rows:
            print(" ".join(f"{k}={v:.6g}" if isinstance(v, float) else f"{k}={v}"
                           for k, v in row.items()))

    negative = [row for row in rows if row["X"] < 0]
    diagonal_only = [row for row in negative if row["X_plus_D"] > 0]
    worst = max(rows, key=lambda row: row["X_plus_D"] / row["R"] ** 2)
    print(f"roots checked: {len(rows)} ({args.min_root}..{args.max_root})")
    print(f"X_R < 0 at {len(negative)} roots; of these, X_R + D_R > 0 at "
          f"{len(diagonal_only)} (sign supplied only by the diagonal)")
    print(f"max (X_R + D_R)/R^2 = {worst['X_plus_D'] / worst['R'] ** 2:.4f} "
          f"at R = {worst['R']} (corr^2/R^2 = {worst['corr_sq'] / worst['R'] ** 2:.4f}, "
          f"D_R/R^2 = {worst['D'] / worst['R'] ** 2:.4f})")
    print(f"max D_R/R^2 = {max(row['D'] / row['R'] ** 2 for row in rows):.4f} "
          "(compiled bound: 3)")
    needed = max(rows, key=lambda row: (row["X"] - 1.5 * row["E"])
                 / (row["R"] ** 2 * envelope[row["R"]]))
    needed_c = (needed["X"] - 1.5 * needed["E"]) / (
        needed["R"] ** 2 * envelope[needed["R"]])
    print(f"smallest C with X_R <= (3/2) E_R + C R^2 K_R on this range: "
          f"{needed_c:.4f} (attained at R = {needed['R']}); a finite range "
          "cannot certify a uniform constant")
    print("Two-sided CORR comparison and quarter frame hold at every root.")


if __name__ == "__main__":
    main()
