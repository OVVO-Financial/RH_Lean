#!/usr/bin/env python3
"""Finite diagnostic for the VF-mid corner-channel construction.

This script mirrors research/VF_MID_CORNER_CHANNEL.lean.  It is diagnostic
only: no finite scan is used as a premise of any Lean theorem.

For each square block [R^2,(R+1)^2], it checks:
  * the literal adjacent-corner channel;
  * the canonical widened channel with
        L_R = min(R//2, floor(A * log(R)^2));
  * the minimal endpoint lag needed to bracket pi(R^2).

The pathwise check is exact for the real-x staircase convention
pi_floor(x) = pi(floor x):
  * upper-channel violations can occur only immediately after a prime jump;
  * lower-channel violations are maximized in the left limit before a prime
    jump, or at a square endpoint.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np


def prime_sieve_bytes(nmax: int) -> bytearray:
    sieve = bytearray(b"\x01") * (nmax + 1)
    if nmax >= 0:
        sieve[0] = 0
    if nmax >= 1:
        sieve[1] = 0
    for p in range(2, math.isqrt(nmax) + 1):
        if sieve[p]:
            start = p * p
            count = (nmax - start) // p + 1
            sieve[start : nmax + 1 : p] = b"\x00" * count
    return sieve


def band_mass(r: int) -> float:
    rf = float(r)
    return (2.0 * rf + 1.0) / math.log(rf * rf + rf + 0.5)


def finished_mass_table(n: int) -> np.ndarray:
    f = np.zeros(n + 1, dtype=float)
    for r in range(2, n):
        f[r + 1] = f[r] + band_mass(r)
    return f


def prime_counts_at_squares(rmax: int, sieve: bytearray) -> np.ndarray:
    out = np.zeros(rmax + 2, dtype=np.int64)
    running = 0
    prev = 0
    view = memoryview(sieve)
    for r in range(rmax + 2):
        sq = r * r
        running += sum(view[prev + 1 : sq + 1])
        out[r] = running
        prev = sq
    return out


def canonical_lag(a: float, r: int) -> int:
    return min(r // 2, max(0, math.floor(a * math.log(r) ** 2)))


def endpoint_required_lag(
    r: int, pi_sq: np.ndarray, finished: np.ndarray
) -> tuple[int, int, int]:
    y = float(pi_sq[r])
    lower_lag = 0
    while r - lower_lag >= 2 and finished[r - lower_lag] > y:
        lower_lag += 1
    upper_lag = 0
    while r + upper_lag < len(finished) and finished[r + upper_lag] < y:
        upper_lag += 1
    return max(lower_lag, upper_lag), lower_lag, upper_lag


def block_path_defects(
    r: int,
    lower0: float,
    lower1: float,
    upper0: float,
    upper1: float,
    primes: np.ndarray,
) -> tuple[float, float, int, int]:
    """Return max(lower-pi), max(pi-upper), and locations.

    The lower value at an interior prime q is evaluated in the left limit
    q^- against pi(q-1), which is the supremum over real x in [q-1,q).
    """
    a = r * r
    b = (r + 1) * (r + 1)
    width = 2 * r + 1
    lower_slope = (lower1 - lower0) / width
    upper_slope = (upper1 - upper0) / width

    i0 = int(np.searchsorted(primes, a, side="right"))
    i1 = int(np.searchsorted(primes, b, side="right"))

    pi_a = i0
    max_lower = lower0 - pi_a
    max_upper = pi_a - upper0
    where_lower = a
    where_upper = a

    ps = primes[i0:i1]
    if ps.size:
        idx = np.arange(i0, i1, dtype=np.int64)
        dx = ps - a
        lower_at_prime = lower0 + lower_slope * dx
        upper_at_prime = upper0 + upper_slope * dx

        lower_defect = lower_at_prime - idx
        upper_defect = (idx + 1) - upper_at_prime

        jl = int(np.argmax(lower_defect))
        ju = int(np.argmax(upper_defect))
        if float(lower_defect[jl]) > max_lower:
            max_lower = float(lower_defect[jl])
            where_lower = int(ps[jl])
        if float(upper_defect[ju]) > max_upper:
            max_upper = float(upper_defect[ju])
            where_upper = int(ps[ju])

    # The right square endpoint is composite for r >= 2.
    pi_b = i1
    right_lower = lower1 - pi_b
    right_upper = pi_b - upper1
    if right_lower > max_lower:
        max_lower = float(right_lower)
        where_lower = b
    if right_upper > max_upper:
        max_upper = float(right_upper)
        where_upper = b

    return max_lower, max_upper, where_lower, where_upper


def literal_failures(
    rstart: int, rmax: int, finished: np.ndarray, primes: np.ndarray
) -> list[dict]:
    out = []
    for r in range(rstart, rmax + 1):
        dlow, dupp, xlow, xupp = block_path_defects(
            r,
            finished[r - 1],
            finished[r],
            finished[r],
            finished[r + 1],
            primes,
        )
        if dlow > 1e-12 or dupp > 1e-12:
            out.append(
                {
                    "R": r,
                    "max_lower_minus_pi": dlow,
                    "max_pi_minus_upper": dupp,
                    "lower_location_or_left_limit": xlow,
                    "upper_location": xupp,
                }
            )
    return out


def widened_failures(
    acoef: float,
    rstart: int,
    rmax: int,
    finished: np.ndarray,
    primes: np.ndarray,
) -> list[dict]:
    out = []
    for r in range(rstart, rmax + 1):
        l0 = canonical_lag(acoef, r)
        l1 = canonical_lag(acoef, r + 1)
        dlow, dupp, xlow, xupp = block_path_defects(
            r,
            finished[r - l0],
            finished[r + 1 - l1],
            finished[r + l0],
            finished[r + 1 + l1],
            primes,
        )
        if dlow > 1e-12 or dupp > 1e-12:
            out.append(
                {
                    "R": r,
                    "lag_R": l0,
                    "lag_R_plus_1": l1,
                    "max_lower_minus_pi": dlow,
                    "max_pi_minus_upper": dupp,
                    "lower_location_or_left_limit": xlow,
                    "upper_location": xupp,
                }
            )
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-max", type=int, default=10_000)
    ap.add_argument("--r-start", type=int, default=56)
    ap.add_argument("--A", type=float, default=0.125)
    ap.add_argument(
        "--out",
        type=Path,
        default=Path("numerics/vf_corner_channel/results/summary.json"),
    )
    args = ap.parse_args()

    if args.r_start < 4 or args.r_max < args.r_start:
        raise SystemExit("require 4 <= r-start <= r-max")
    if args.A < 0:
        raise SystemExit("A must be nonnegative")

    max_lag = max(canonical_lag(args.A, r) for r in range(args.r_start, args.r_max + 2))
    table_max = args.r_max + max(max_lag + 8, 1024)
    finished = finished_mass_table(table_max)

    nmax = (args.r_max + 1) ** 2
    sieve = prime_sieve_bytes(nmax)
    primes = np.flatnonzero(np.frombuffer(sieve, dtype=np.uint8)).astype(np.int64)
    pi_sq = prime_counts_at_squares(args.r_max, sieve)

    literal = literal_failures(args.r_start, args.r_max, finished, primes)
    widened = widened_failures(args.A, args.r_start, args.r_max, finished, primes)

    endpoint_rows = []
    for r in range(args.r_start, args.r_max + 1):
        lag, lower_lag, upper_lag = endpoint_required_lag(r, pi_sq, finished)
        norm_a = lag / (math.log(r) ** 2)
        endpoint_rows.append((norm_a, r, lag, lower_lag, upper_lag))

    endpoint_rows.sort(reverse=True)
    max_a, argmax_r, lag, lower_lag, upper_lag = endpoint_rows[0]

    summary = {
        "status": "finite diagnostic only; not a proof premise",
        "r_start": args.r_start,
        "r_max": args.r_max,
        "x_max": args.r_max**2,
        "A": args.A,
        "canonical_lag_formula": "min(R//2, floor(A*log(R)^2))",
        "literal_channel": {
            "failure_count": len(literal),
            "failure_R": [row["R"] for row in literal],
            "failures": literal,
        },
        "widened_channel": {
            "failure_count": len(widened),
            "failure_R": [row["R"] for row in widened],
            "failures": widened,
        },
        "endpoint_minimum_lag": {
            "max_required_L_over_logR_squared": max_a,
            "argmax_R": argmax_r,
            "required_lag": lag,
            "required_lower_lag": lower_lag,
            "required_upper_lag": upper_lag,
        },
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
