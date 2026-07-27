#!/usr/bin/env python3
"""Test the corrected dynamic-denominator Viole baseline through 10^8.

The effective logarithmic base is constrained by

    log b(x) = 1 + a / log x + b / (log x)^2,

so b(x) -> e. The coefficients are fitted only on square-block midpoints from
10^3 through 10^5, frozen, and then evaluated on later decades.

Dependencies: numpy, pandas, scipy.
"""

import json
import math
import time
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.optimize import least_squares
from scipy.special import expi

OUT = Path(__file__).with_name("vf_dynamic_e_results")
OUT.mkdir(exist_ok=True)
NMAX = 100_000_000
LI2 = float(expi(math.log(2.0)))


def prime_counts_at(checkpoints: np.ndarray, nmax: int) -> tuple[np.ndarray, int]:
    """Return exact pi(x) at sorted checkpoints using a segmented sieve."""
    limit = int(math.isqrt(nmax))
    base = np.ones(limit + 1, dtype=np.bool_)
    base[:2] = False
    for p in range(2, int(math.isqrt(limit)) + 1):
        if base[p]:
            base[p * p:limit + 1:p] = False
    base_primes = np.flatnonzero(base)

    truth = np.empty(len(checkpoints), dtype=np.int64)
    checkpoint_index = 0
    count = 0
    segment_size = 2_000_000

    for low in range(0, nmax + 1, segment_size):
        high = min(low + segment_size, nmax + 1)
        segment = np.ones(high - low, dtype=np.bool_)
        if low == 0:
            segment[:2] = False
        for p in base_primes:
            start = max(p * p, ((low + p - 1) // p) * p)
            if start < high:
                segment[start - low:high - low:p] = False
        cumulative = np.cumsum(segment, dtype=np.int32)
        while checkpoint_index < len(checkpoints) and checkpoints[checkpoint_index] < high:
            x = int(checkpoints[checkpoint_index])
            truth[checkpoint_index] = count + int(cumulative[x - low])
            checkpoint_index += 1
        count += int(cumulative[-1])

    return truth, count


def li(x: np.ndarray) -> np.ndarray:
    return expi(np.log(np.asarray(x, dtype=np.float64))) - LI2


def correction_from_log_base_exponent(log_x: np.ndarray, exponent: np.ndarray) -> np.ndarray:
    t = log_x / exponent
    return (1.0 + t) * np.log1p(1.0 / t)


def fit_dynamic(log_x: np.ndarray, target: np.ndarray, mask: np.ndarray):
    def residual(parameters: np.ndarray) -> np.ndarray:
        a, b = parameters
        L = log_x[mask]
        exponent = 1.0 + a / L + b / L**2
        if np.any(exponent <= 0):
            return np.full(mask.sum(), 1e6)
        return correction_from_log_base_exponent(L, exponent) - target[mask]

    return least_squares(
        residual,
        [0.0, 0.0],
        bounds=([-1000.0, -10000.0], [1000.0, 10000.0]),
        max_nfev=100_000,
    )


def main() -> None:
    started = time.time()
    rmax = int((math.sqrt(1 + 4 * (NMAX - 0.5)) - 1) // 2)
    r = np.arange(2, rmax + 1, dtype=np.int64)
    xi = r.astype(np.float64) ** 2 + r + 0.5
    integer_midpoints = (r * r + r).astype(np.int64)

    pi_x, pi_nmax = prime_counts_at(integer_midpoints, NMAX)
    pi_x = pi_x.astype(np.float64)
    log_xi = np.log(xi)

    target_correction = np.log(r.astype(np.float64) ** 2) - (
        r.astype(np.float64) ** 2
    ) / pi_x
    train = (xi >= 1_000) & (xi <= 100_000)
    fit = fit_dynamic(log_xi, target_correction, train)
    a_dynamic, b_dynamic = map(float, fit.x)

    exponent = 1.0 + a_dynamic / log_xi + b_dynamic / log_xi**2
    correction = correction_from_log_base_exponent(log_xi, exponent)
    dynamic_vf = r.astype(np.float64) ** 2 / (
        np.log(r.astype(np.float64) ** 2) - correction
    )
    logarithmic_integral = li(xi)

    ranges = [
        (1e3, 1e5, "train 1e3-1e5"),
        (1e5, 1e6, "test 1e5-1e6"),
        (1e6, 1e7, "test 1e6-1e7"),
        (1e7, 1e8, "test 1e7-1e8"),
    ]

    rows = []
    for lo, hi, label in ranges:
        mask = (xi >= lo) & (xi < hi)
        vf_error = dynamic_vf[mask] - pi_x[mask]
        li_error = logarithmic_integral[mask] - pi_x[mask]
        for name, error, other_error in [
            ("Dynamic VF e-asymptotic", vf_error, li_error),
            ("Li", li_error, vf_error),
        ]:
            rows.append({
                "range": label,
                "model": name,
                "n": int(mask.sum()),
                "bias": float(error.mean()),
                "mae": float(np.abs(error).mean()),
                "rmse": float(np.sqrt(np.mean(error * error))),
                "max_abs": float(np.abs(error).max()),
                "pointwise_win_rate": float(
                    np.mean(np.abs(error) < np.abs(other_error))
                ),
                "min_log_base_exponent": float(exponent[mask].min()),
                "max_log_base_exponent": float(exponent[mask].max()),
            })

    metrics = pd.DataFrame(rows)
    metrics.to_csv(OUT / "global_midpoint_metrics.csv", index=False)

    summary = {
        "NMAX": NMAX,
        "pi_NMAX": int(pi_nmax),
        "fit_range": [1000, 100000],
        "formula": "log b(x)=1+a/log(x)+b/log(x)^2",
        "a": a_dynamic,
        "b": b_dynamic,
        "asymptotic_base": "e",
        "elapsed_seconds": time.time() - started,
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2))

    report = [
        "# Corrected e-asymptotic dynamic Viole test",
        "",
        f"`a = {a_dynamic:.15f}`",
        f"`b = {b_dynamic:.15f}`",
        "",
        metrics.pivot(index="range", columns="model", values="rmse")
        .round(6)
        .to_markdown(),
        "",
        "## Pointwise win rates",
        "",
        metrics.pivot(index="range", columns="model", values="pointwise_win_rate")
        .round(6)
        .to_markdown(),
    ]
    (OUT / "REPORT.md").write_text("\n".join(report))

    print(summary)
    print(metrics.to_string(index=False))


if __name__ == "__main__":
    main()
