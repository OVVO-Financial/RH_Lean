#!/usr/bin/env python3
"""Explore death shells through factor pairs rather than all m < T^2.

For fixed Lambda and stage cutoff T, every death shell satisfies

    2 Lambda t < |q^2-c^2| <= 2 Lambda (t+1),

with q = P+(m), c = m/q, and m = q*c < (t+1)^2.  Writing

    |q^2-c^2| = u*v,

allows enumeration in O(K log K), where K = floor(2 Lambda (T+1)), instead
of sieving every integer through T^2.

The output includes overall drift/variance statistics and stratification by
orientation q>c versus c>q, parity of (u,v), q/(t+1) quartile, and
squarefreeness (equivalently nonzero Mobius weight).
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np
import pandas as pd


def linear_sieve(limit: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return smallest prime factors, primes, and Mobius values through limit."""
    spf = np.zeros(limit + 1, dtype=np.int32)
    mu = np.zeros(limit + 1, dtype=np.int8)
    mu[1] = 1
    primes: list[int] = []

    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = n
            primes.append(n)
            mu[n] = -1
        for prime in primes:
            if prime > spf[n] or n * prime > limit:
                break
            spf[n * prime] = prime
            mu[n * prime] = 0 if prime == spf[n] else -mu[n]

    return spf, np.asarray(primes, dtype=np.int32), mu


def run_experiment(max_stage: int, lam: float) -> tuple[pd.DataFrame, pd.DataFrame]:
    if max_stage < 1:
        raise ValueError("max_stage must be positive")
    if lam <= 0:
        raise ValueError("Lambda must be positive")

    max_height = math.floor(2.0 * lam * (max_stage + 1) + 1e-12)
    sieve_limit = max(max_height, max_stage + 2)
    spf, primes, mu = linear_sieve(sieve_limit)

    is_prime = np.zeros(sieve_limit + 1, dtype=np.bool_)
    is_prime[primes] = True
    largest_prime_factor = np.ones(sieve_limit + 1, dtype=np.int32)
    for n in range(2, sieve_limit + 1):
        p = int(spf[n])
        largest_prime_factor[n] = max(p, largest_prime_factor[n // p])

    shell_size = np.zeros(max_stage + 1, dtype=np.int32)
    delta = np.zeros(max_stage + 1, dtype=np.int32)
    groups: dict[tuple[str, str], dict[str, int]] = {}

    def record(section: str, group: str, weight: int) -> None:
        row = groups.setdefault(
            (section, group),
            {"candidates": 0, "mass": 0, "squarefree": 0, "zero_mu": 0},
        )
        row["candidates"] += 1
        row["mass"] += weight
        if weight == 0:
            row["zero_mu"] += 1
        else:
            row["squarefree"] += 1

    def add_candidate(
        q: int,
        c: int,
        height: int,
        orientation: str,
        parity: str,
    ) -> None:
        if c < 1 or q < 2 or q > sieve_limit or not is_prime[q]:
            return
        if largest_prime_factor[c] > q:
            return

        stage = math.ceil(height / (2.0 * lam) - 1e-12) - 1
        if not 0 <= stage <= max_stage:
            return
        if q * c >= (stage + 1) ** 2:
            return

        # Since q is prime and every prime factor of c is <= q,
        # mu(q*c) is zero when q divides c and otherwise equals -mu(c).
        weight = 0 if c % q == 0 else -int(mu[c])
        shell_size[stage] += 1
        delta[stage] += weight

        quartile = min(3, int(4.0 * q / (stage + 1)))
        q_group = f"{quartile / 4:.2f}-{(quartile + 1) / 4:.2f}"
        record("orientation", orientation, weight)
        record("parity", parity, weight)
        record("q_ratio", q_group, weight)
        record("orientation_q_ratio", f"{orientation}:{q_group}", weight)

    # Enumerate factor pairs u*v = |q^2-c^2| with u <= v and equal parity.
    for u in range(1, max_height + 1):
        max_v = max_height // u
        first_v = u if (u % 2) == (u % 2) else u + 1
        for v in range(first_v, max_v + 1, 2):
            height = u * v
            parity = "odd_odd" if u % 2 else "even_even"

            q = (u + v) // 2
            c = (v - u) // 2
            add_candidate(q, c, height, "q>c", parity)

            c = (u + v) // 2
            q = (v - u) // 2
            add_candidate(q, c, height, "c>q", parity)

    death = np.cumsum(delta)
    abs_delta = np.abs(delta)
    correlation = float(np.corrcoef(shell_size, abs_delta)[0, 1])

    overall = {
        "section": "overall",
        "group": "all",
        "T": max_stage,
        "Lambda": lam,
        "total_shell_atoms": int(shell_size.sum()),
        "nonempty_shells": int(np.count_nonzero(shell_size)),
        "max_shell_size": int(shell_size.max()),
        "mean_shell_size": float(shell_size.mean()),
        "rms_deltaD": float(np.sqrt(np.mean(delta.astype(float) ** 2))),
        "mean_deltaD": float(delta.mean()),
        "max_abs_deltaD": int(abs_delta.max()),
        "D_T": int(death[-1]),
        "rms_D": float(np.sqrt(np.mean(death.astype(float) ** 2))),
        "corr_size_absdelta": correlation,
    }

    rows: list[dict[str, int | float | str]] = [overall]
    for (section, group), values in sorted(groups.items()):
        candidates = values["candidates"]
        rows.append(
            {
                "section": section,
                "group": group,
                **values,
                "mean_weight": values["mass"] / candidates if candidates else np.nan,
            }
        )

    summary = pd.DataFrame(rows)
    series = pd.DataFrame(
        {
            "t": np.arange(max_stage + 1),
            "shell_size": shell_size,
            "deltaD": delta,
            "D": death,
        }
    )
    return summary, series


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-stage", type=int, default=100_000)
    parser.add_argument("--lambda-value", type=float, default=1.0)
    parser.add_argument("--output-dir", type=Path, default=Path("."))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    summary, series = run_experiment(args.max_stage, args.lambda_value)
    summary.to_csv(
        args.output_dir / f"death_shell_factor_summary_T{args.max_stage}.csv",
        index=False,
    )
    series.to_csv(
        args.output_dir / f"death_shell_factor_series_T{args.max_stage}.csv",
        index=False,
    )
    print(summary.to_string(index=False))


if __name__ == "__main__":
    main()
