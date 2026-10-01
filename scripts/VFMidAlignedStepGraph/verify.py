#!/usr/bin/env python3
"""Finite diagnostic for the aligned VF-mid full step graph.

This mirrors the Lean definitions on PR #842:

    F_R = sum_{r=2}^{R-1} (2r+1)/log(r^2+r+1/2)
    c0  = pi(9) - F_3 = 4 - F_3
    K_R(c) = floor(F_R + c)

A square block R is counted as intersecting the prime-count staircase if any
of the following holds:

  horizontal: K_R <= pi((R+1)^2) and pi(R^2) <= K_R
  left face:  K_{R-1} <= pi(R^2) <= K_R
  right face: K_R <= pi((R+1)^2) <= K_{R+1}

This is a finite verification only.  It is not a proof of universal
bracketing.
"""

from __future__ import annotations

import argparse
import math


def prime_counts_at_squares(r_max: int) -> list[int]:
    """Return pi(R^2) for R=0,...,r_max+1 using a bytearray sieve."""
    n_max = (r_max + 1) ** 2
    sieve = bytearray(b"\x01") * (n_max + 1)
    sieve[0:2] = b"\x00\x00"

    for p in range(2, math.isqrt(n_max) + 1):
        if sieve[p]:
            start = p * p
            count = (n_max - start) // p + 1
            sieve[start : n_max + 1 : p] = b"\x00" * count

    pi_sq = [0] * (r_max + 2)
    running = 0
    previous_square = 0

    for r in range(r_max + 2):
        square = r * r
        if square >= previous_square + 1:
            running += sum(sieve[previous_square + 1 : square + 1])
        pi_sq[r] = running
        previous_square = square

    return pi_sq


def vf_finished_masses(r_max: int) -> list[float]:
    """Return F_R through R=r_max+1."""
    f = [0.0] * (r_max + 2)
    for r in range(2, r_max + 1):
        midpoint = r * r + r + 0.5
        band_mass = (2 * r + 1) / math.log(midpoint)
        f[r + 1] = f[r] + band_mass
    return f


def integer_levels(f: list[float], c: float) -> list[int]:
    return [math.floor(x + c) for x in f]


def scan(r_max: int, pi_sq: list[int], f: list[float], c: float):
    k = integer_levels(f, c)
    horizontal_failures: list[int] = []
    full_failures: list[int] = []
    vertical_rescues: list[tuple[int, str]] = []

    for r in range(2, r_max + 1):
        horizontal = pi_sq[r] <= k[r] <= pi_sq[r + 1]
        left_vertical = k[r - 1] <= pi_sq[r] <= k[r]
        right_vertical = k[r] <= pi_sq[r + 1] <= k[r + 1]

        if not horizontal:
            horizontal_failures.append(r)
        if not (horizontal or left_vertical or right_vertical):
            full_failures.append(r)
        elif not horizontal:
            vertical_rescues.append((r, "L" if left_vertical else "R"))

    return horizontal_failures, full_failures, vertical_rescues, k


def phase_window(
    r_max: int,
    pi_sq: list[int],
    f: list[float],
    start: float = 0.0,
    stop: float = 3.0,
    step: float = 0.001,
):
    good: list[float] = []
    n = int(round((stop - start) / step))
    for j in range(n + 1):
        c = start + j * step
        _, failures, _, _ = scan(r_max, pi_sq, f, c)
        if not failures:
            good.append(c)
    return (min(good), max(good)) if good else None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-max", type=int, default=10_000)
    parser.add_argument("--phase-step", type=float, default=0.001)
    args = parser.parse_args()

    pi_sq = prime_counts_at_squares(args.r_max)
    f = vf_finished_masses(args.r_max)

    c0 = 4.0 - f[3]

    h0, full0, rescue0, _ = scan(args.r_max, pi_sq, f, 0.0)
    hc, fullc, rescuec, kc = scan(args.r_max, pi_sq, f, c0)
    window = phase_window(
        args.r_max, pi_sq, f, step=args.phase_step
    )

    print(f"R_max = {args.r_max}")
    print(f"F_3   = {f[3]:.15f}")
    print(f"c0    = {c0:.15f}")
    print()
    print(f"unaligned horizontal failures: {h0}")
    print(f"unaligned full-graph failures: {full0}")
    print(f"unaligned vertical rescues:    {rescue0}")
    print()
    print(f"aligned horizontal failures:   {hc}")
    print(f"aligned full-graph failures:   {fullc}")
    print(f"aligned vertical rescues:      {rescuec}")
    print(f"grid phase window:             {window}")

    r = 549
    if args.r_max >= r:
        print()
        print("R = 549 diagnostic")
        print(
            f"K_548={kc[548]}, pi(549^2)={pi_sq[549]}, "
            f"K_549={kc[549]}, pi(550^2)={pi_sq[550]}, "
            f"K_550={kc[550]}"
        )


if __name__ == "__main__":
    main()
