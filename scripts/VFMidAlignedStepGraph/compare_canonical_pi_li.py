#!/usr/bin/env python3
"""Genuine-prime numerical autopsy: canonical VF vs Li_2 and standard li.

No fantasy prime staircase or independence assumptions. Canonical real VF
is raw midpoint-complete-plus-LIVE path + sqrt(2), never the integer floor.
Both logarithmic-integral normalizations are reported. Li_2 is evaluated by
composite Simpson quadrature and li(2) by the convergent Ei series.
Experiments are finite and DO NOT prove an all-x comparison theorem.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

EULER_GAMMA = 0.5772156649015328606
SAMPLE_ROOTS = {2, 3, 4, 10, 17, 317, 1027, 5561, 10000}
SAMPLE_X = {4, 5, 6, 7, 8, 9, 16, 100, 317, 1000, 10000,
            100489, 1_000_000, 100_000_000}


def classical_li_at_two() -> float:
    t = math.log(2.0)
    term = 1.0
    series = 0.0
    for k in range(1, 36):
        term *= t / k
        series += term / k
    return EULER_GAMMA + math.log(t) + series


def integral_invlog(a: float, b: float, panels: int) -> float:
    if a == b:
        return 0.0
    h = (b - a) / panels
    total = 1.0 / math.log(a) + 1.0 / math.log(b)
    for i in range(1, panels):
        total += (4 if i % 2 else 2) / math.log(a + i * h)
    return h * total / 3.0


def actual_prime_sieve(n: int) -> bytearray:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            q = p * p
            sieve[q:n + 1:p] = b"\x00" * ((n - q) // p + 1)
    return sieve


def record(x: int, pi: int, vf: float, li2: float, classical_li: float) -> dict:
    return {
        "x": x, "actual_pi": pi, "canonical_vf_real": vf,
        "Li2_integral_from_two": li2, "classical_li": classical_li,
        "absolute_pi_VF": abs(pi - vf),
        "absolute_pi_Li2": abs(pi - li2),
        "absolute_pi_classical_li": abs(pi - classical_li)
    }


def compare(r_max: int = 10000, integer_max: int = 1_000_000) -> dict:
    if not 3 <= r_max <= 10000:
        raise ValueError("r_max must be between 3 and 10000")
    if not 16 <= integer_max <= r_max * r_max:
        raise ValueError("integer_max must be between 16 and r_max^2")

    f = [0.0] * (r_max + 1)
    li2_square = [0.0] * (r_max + 1)
    li2_square[2] = integral_invlog(2.0, 4.0, 512)
    for R in range(2, r_max):
        f[R + 1] = f[R] + (2 * R + 1) / math.log(R * R + R + .5)
        li2_square[R + 1] = li2_square[R] + integral_invlog(
            float(R * R), float((R + 1) ** 2), 64)

    prime = actual_prime_sieve(r_max * r_max)
    pi_sq = [0] * (r_max + 1)
    pi_running = 0
    for R in range(2, r_max + 1):
        a = 2 if R == 2 else (R - 1) ** 2 + 1
        pi_running += prime[a:R * R + 1].count(1)
        pi_sq[R] = pi_running

    phase = math.sqrt(2.0)
    li_at_two = classical_li_at_two()
    sq_losses_li2 = []
    sq_losses_classical = []
    sq_raw_wins_li2 = 0
    total_error = [0.0, 0.0, 0.0]
    samples = {}
    for R in range(2, r_max + 1):
        x = R * R
        pi = pi_sq[R]
        vf = f[R] + phase
        li2 = li2_square[R]
        classical = li2 + li_at_two
        errors = (abs(pi - vf), abs(pi - li2), abs(pi - classical))
        for j, val in enumerate(errors):
            total_error[j] += val
        if errors[0] >= errors[1]:
            sq_losses_li2.append(R)
        if errors[0] >= errors[2]:
            sq_losses_classical.append(R)
        sq_raw_wins_li2 += abs(pi - f[R]) < errors[1]
        if R in SAMPLE_ROOTS:
            samples[str(x)] = record(x, pi, vf, li2, classical)

    if r_max >= 1027:
        assert (pi_sq[17], pi_sq[317], pi_sq[1027]) == (61, 9631, 82462)
    if r_max == 10000:
        assert pi_sq[10000] == 5_761_455
        assert sq_losses_li2 == [2], sq_losses_li2
        assert sq_losses_classical == [], sq_losses_classical
        assert sq_raw_wins_li2 == 9997

    # A SEPARATE actual-prime sieve evaluates every integer, not just squares.
    # The Li_2 live integral uses 16-panel Simpson quadrature on [R^2,x].
    small_prime = actual_prime_sieve(integer_max)
    npi = 0
    integer_losses_li2 = []
    integer_losses_classical = []
    for x in range(2, integer_max + 1):
        npi += small_prime[x]
        if x < 4:
            continue
        R = math.isqrt(x)
        vf = f[R] + phase + (x - R * R) / math.log((R * R + x) / 2)
        li2 = li2_square[R] + integral_invlog(float(R * R), float(x), 16)
        classical = li2 + li_at_two
        if abs(npi - vf) >= abs(npi - li2):
            integer_losses_li2.append(x)
        if abs(npi - vf) >= abs(npi - classical):
            integer_losses_classical.append(x)
        if x in SAMPLE_X:
            samples[str(x)] = record(x, npi, vf, li2, classical)

    if integer_max == 1_000_000:
        assert npi == 78_498
        assert integer_losses_li2 == [4, 5, 6, 7, 8]
        assert integer_losses_classical == [5, 7]

    return {
        "definition": "VF=raw midpoint square/live path + sqrt(2), not floor",
        "Li2": "integral from 2 to x of 1/log(t), Simpson quadrature",
        "classical_li": "Ei(log x)=Li2(x)+li(2)",
        "li_two": li_at_two,
        "status": "finite exact-prime census, no universal pointwise claim",
        "square_endpoints": {
            "root_range": [2, r_max], "count": r_max - 1,
            "canonical_VF_wins_Li2": r_max - 1 - len(sq_losses_li2),
            "Li2_wins_or_ties_roots": sq_losses_li2,
            "canonical_VF_wins_classical_li":
                r_max - 1 - len(sq_losses_classical),
            "classical_li_wins_or_ties_roots": sq_losses_classical,
            "raw_VF_wins_Li2": sq_raw_wins_li2,
            "mean_absolute_pi_VF": total_error[0] / (r_max - 1),
            "mean_absolute_pi_Li2": total_error[1] / (r_max - 1),
            "mean_absolute_pi_classical_li": total_error[2] / (r_max - 1)
        },
        "integer_cutoffs": {
            "range": [4, integer_max], "count": integer_max - 3,
            "canonical_VF_wins_Li2":
                integer_max - 3 - len(integer_losses_li2),
            "Li2_wins_or_ties_x": integer_losses_li2,
            "canonical_VF_wins_classical_li":
                integer_max - 3 - len(integer_losses_classical),
            "classical_li_wins_or_ties_x": integer_losses_classical,
        },
        "examples": dict(sorted(samples.items(), key=lambda item: int(item[0]))),
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--r-max", type=int, default=10000)
    p.add_argument("--integer-max", type=int, default=1_000_000)
    p.add_argument("--json-out", type=Path)
    args = p.parse_args()
    result = compare(args.r_max, args.integer_max)
    content = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.write_text(content, encoding="utf-8")
    print(content, end="")


if __name__ == "__main__":
    main()
