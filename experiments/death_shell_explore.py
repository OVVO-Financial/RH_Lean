#!/usr/bin/env python3
"""Explore the exact death shells from the Lean formalization.

For each integer m and cutoff parameter Lambda, assign m to the unique shell t
satisfying

    2 Lambda t < |P+(m)^2 - (m/P+(m))^2| <= 2 Lambda (t+1)

and enforce the square-prefix eligibility m < (t+1)^2.  The script reports
shell cardinalities, Möbius shell masses Delta D_t, and the cumulative process
D_t.  It is exploratory and does not establish an asymptotic estimate.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import pandas as pd


def sieve_moebius_and_lpf(limit: int) -> tuple[np.ndarray, np.ndarray]:
    """Return Möbius values and largest prime factors through ``limit``."""
    mu = np.ones(limit + 1, dtype=np.int8)
    lpf = np.zeros(limit + 1, dtype=np.int32)
    composite = np.zeros(limit + 1, dtype=np.bool_)
    primes: list[int] = []
    mu[0] = 0

    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            mu[n] = -1
            lpf[n] = n
        for prime in primes:
            value = n * prime
            if value > limit:
                break
            composite[value] = True
            lpf[value] = max(lpf[n], prime)
            if n % prime == 0:
                mu[value] = 0
                break
            mu[value] = -mu[n]

    lpf[1] = 1
    return mu, lpf


def run_experiment(
    max_stage: int,
    lambdas: list[float],
    cutoffs: list[int],
) -> tuple[pd.DataFrame, pd.DataFrame]:
    endpoint = (max_stage + 1) ** 2 - 1
    mu, lpf = sieve_moebius_and_lpf(endpoint)

    m = np.arange(endpoint + 1, dtype=np.int64)
    cofactor = np.ones(endpoint + 1, dtype=np.int64)
    cofactor[2:] = m[2:] // lpf[2:]
    height = np.abs(
        lpf.astype(np.float64) ** 2 - cofactor.astype(np.float64) ** 2
    )

    summary_rows: list[dict[str, float | int]] = []
    series_rows: list[tuple[float, int, int, int, int]] = []

    for lam in lambdas:
        if lam <= 0:
            raise ValueError("Every Lambda must be positive.")

        delta = np.zeros(max_stage + 1, dtype=np.int64)
        shell_size = np.zeros(max_stage + 1, dtype=np.int64)

        # The strict-left, weak-right shell convention gives
        # t = ceil(height/(2 Lambda)) - 1.
        crossing_stage = np.ceil(height / (2.0 * lam)).astype(np.int64) - 1
        eligible = (
            (m >= 1)
            & (crossing_stage >= 0)
            & (crossing_stage <= max_stage)
            & (m < (crossing_stage + 1) ** 2)
        )

        stages = crossing_stage[eligible]
        np.add.at(delta, stages, mu[eligible].astype(np.int64))
        np.add.at(shell_size, stages, 1)
        death_process = np.cumsum(delta)

        for cutoff in cutoffs:
            if cutoff > max_stage:
                continue
            local_delta = delta[: cutoff + 1]
            local_size = shell_size[: cutoff + 1]
            local_death = death_process[: cutoff + 1]
            abs_delta = np.abs(local_delta)
            correlation = np.nan
            if np.std(local_size) > 0 and np.std(abs_delta) > 0:
                correlation = float(np.corrcoef(local_size, abs_delta)[0, 1])

            summary_rows.append(
                {
                    "Lambda": lam,
                    "T": cutoff,
                    "total_shell_atoms": int(local_size.sum()),
                    "nonempty_shells": int(np.count_nonzero(local_size)),
                    "max_shell_size": int(local_size.max()),
                    "rms_shell_size": float(
                        np.sqrt(np.mean(local_size.astype(float) ** 2))
                    ),
                    "rms_deltaD": float(
                        np.sqrt(np.mean(local_delta.astype(float) ** 2))
                    ),
                    "max_abs_deltaD": int(abs_delta.max()),
                    "D_T": int(local_death[-1]),
                    "rms_D": float(
                        np.sqrt(np.mean(local_death.astype(float) ** 2))
                    ),
                    "sum_D2": float(np.sum(local_death.astype(float) ** 2)),
                    "sum_D2_over_T3": float(
                        np.sum(local_death.astype(float) ** 2) / cutoff**3
                    ),
                    "corr_size_absdelta": correlation,
                }
            )

        for stage in range(max_stage + 1):
            series_rows.append(
                (
                    lam,
                    stage,
                    int(shell_size[stage]),
                    int(delta[stage]),
                    int(death_process[stage]),
                )
            )

    summary = pd.DataFrame(summary_rows)
    series = pd.DataFrame(
        series_rows,
        columns=["Lambda", "t", "shell_size", "deltaD", "D"],
    )
    return summary, series


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-stage", type=int, default=2000)
    parser.add_argument(
        "--lambdas", type=float, nargs="+", default=[0.5, 1.0, 2.0, 4.0]
    )
    parser.add_argument(
        "--cutoffs", type=int, nargs="+", default=[100, 200, 500, 1000, 2000]
    )
    parser.add_argument("--output-dir", type=Path, default=Path("."))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    summary, series = run_experiment(args.max_stage, args.lambdas, args.cutoffs)
    summary.to_csv(args.output_dir / "death_shell_scaling.csv", index=False)
    series.to_csv(
        args.output_dir / f"death_shell_series_T{args.max_stage}.csv", index=False
    )
    print(summary.to_string(index=False))


if __name__ == "__main__":
    main()
