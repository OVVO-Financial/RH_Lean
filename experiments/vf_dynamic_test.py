#!/usr/bin/env python3
"""Reproduce the dynamic-denominator Viole baseline study.

The script fits the two dynamic-base coefficients only on square-block
midpoints from 10^3 through 10^5, freezes them, evaluates later decades, and
compares exact-activity interval residuals against Li.

Dependencies: numpy, pandas, scipy, matplotlib.
"""

import json
import math
import time
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy.optimize import least_squares
from scipy.special import expi

OUT = Path(__file__).with_name("vf_dynamic_results")
OUT.mkdir(exist_ok=True)
NMAX = 10_000_000
LI2 = float(expi(math.log(2.0)))


def sieve_pi(n):
    isp = np.ones(n + 1, dtype=np.bool_)
    isp[:2] = False
    lim = int(math.isqrt(n))
    for p in range(2, lim + 1):
        if isp[p]:
            isp[p * p:n + 1:p] = False
    pi = np.cumsum(isp, dtype=np.int32)
    return isp, pi


def mobius_upto(n):
    isp = np.ones(n + 1, dtype=np.bool_)
    isp[:2] = False
    for p in range(2, int(math.isqrt(n)) + 1):
        if isp[p]:
            isp[p * p:n + 1:p] = False
    primes = np.flatnonzero(isp)
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    for p in primes:
        mu[p::p] *= -1
        pp = int(p) * int(p)
        if pp <= n:
            mu[pp::pp] = 0
    return mu


def li(x):
    x = np.asarray(x, dtype=np.float64)
    return expi(np.log(x)) - LI2


def correction_from_log_base_exponent(log_x, exponent):
    t = log_x / exponent
    return (1.0 + t) * np.log1p(1.0 / t)


def fit_dynamic(log_x, target_correction, mask):
    def residual(parameters):
        a, b = parameters
        exponent = 2.0 + a / log_x[mask] + b / log_x[mask] ** 2
        if np.any(exponent <= 0):
            return np.full(mask.sum(), 1e3)
        return correction_from_log_base_exponent(
            log_x[mask], exponent) - target_correction[mask]

    return least_squares(
        residual,
        [0.0, 0.0],
        bounds=([-100, -1000], [100, 1000]),
    )


print("sieving")
t0 = time.time()
isprime, pi = sieve_pi(NMAX)
print("sieve seconds", time.time() - t0, "pi", int(pi[-1]))

rmax = int((math.sqrt(1 + 4 * (NMAX - 0.5)) - 1) // 2)
r = np.arange(2, rmax + 1, dtype=np.int64)
xi = r.astype(np.float64) ** 2 + r + 0.5
xf = (r * r + r).astype(np.int64)
pi_x = pi[xf].astype(np.float64)
log_xi = np.log(xi)

# The dynamic model retains the original VF numerator r^2 and fits only the
# convergence correction in its denominator.
target_correction = np.log(r.astype(np.float64) ** 2) - (
    r.astype(np.float64) ** 2
) / pi_x
midpoint_target = log_xi - xi / pi_x
train = (xi >= 1_000) & (xi <= 100_000)
fit = fit_dynamic(log_xi, target_correction, train)
a_dynamic, b_dynamic = map(float, fit.x)
print("fit", a_dynamic, b_dynamic)

# Direct denominator fits are diagnostics, not the recommended final model.
x2 = np.column_stack([1 / log_xi[train], 1 / log_xi[train] ** 2])
coef2 = np.linalg.lstsq(x2, midpoint_target[train] - 1, rcond=None)[0]
x3 = np.column_stack([
    1 / log_xi[train],
    1 / log_xi[train] ** 2,
    1 / log_xi[train] ** 3,
])
coef3 = np.linalg.lstsq(x3, midpoint_target[train] - 1, rcond=None)[0]

rr = r.astype(np.float64)


def original_architecture_anchor(exponent):
    return rr ** 2 / (
        np.log(rr ** 2)
        - correction_from_log_base_exponent(log_xi, exponent)
    )


anchors = {}
anchors["VF base10"] = original_architecture_anchor(
    np.full_like(log_xi, math.log(10.0))
)
anchors["VF base e^2"] = original_architecture_anchor(
    np.full_like(log_xi, 2.0)
)
dynamic_exponent = (
    2.0 + a_dynamic / log_xi + b_dynamic / log_xi ** 2
)
anchors["VF dynamic base"] = original_architecture_anchor(dynamic_exponent)
asymptotic_correction = (
    1 + 1 / log_xi + 3 / log_xi ** 2 + 13 / log_xi ** 3
)
anchors["VF asym3 midpoint"] = xi / (log_xi - asymptotic_correction)
correction2 = 1 + coef2[0] / log_xi + coef2[1] / log_xi ** 2
anchors["VF fitted denom 2"] = xi / (log_xi - correction2)
correction3 = (
    1
    + coef3[0] / log_xi
    + coef3[1] / log_xi ** 2
    + coef3[2] / log_xi ** 3
)
anchors["VF fitted denom 3"] = xi / (log_xi - correction3)
anchors["Li"] = li(xi)

ranges = [
    (1e3, 1e5, "train 1e3-1e5"),
    (1e5, 1e6, "test 1e5-1e6"),
    (1e6, 1e7, "test 1e6-1e7"),
]
rows = []
for lo, hi, label in ranges:
    mask = (xi >= lo) & (xi < hi)
    truth = pi_x[mask]
    for name, prediction in anchors.items():
        error = prediction[mask] - truth
        rows.append({
            "range": label,
            "model": name,
            "n": int(mask.sum()),
            "bias": float(error.mean()),
            "mae": float(np.abs(error).mean()),
            "rmse": float(np.sqrt(np.mean(error * error))),
            "max_abs": float(np.abs(error).max()),
            "rel_rmse": float(np.sqrt(np.mean((error / truth) ** 2))),
        })
global_df = pd.DataFrame(rows)
global_df.to_csv(OUT / "global_midpoint_metrics.csv", index=False)

# Rolling-origin stability.
rolling_rows = []
for cutoff, next_hi in [(1e4, 1e5), (1e5, 1e6), (1e6, 1e7)]:
    train_mask = (xi >= 1e3) & (xi <= cutoff)
    rolling_fit = fit_dynamic(log_xi, target_correction, train_mask)
    aa, bb = rolling_fit.x
    dynamic_prediction = original_architecture_anchor(
        2 + aa / log_xi + bb / log_xi ** 2
    )
    test_mask = (xi >= cutoff) & (xi < next_hi)
    truth = pi_x[test_mask]
    for name, prediction in [
        ("dynamic", dynamic_prediction),
        ("base10", anchors["VF base10"]),
        ("Li", anchors["Li"]),
    ]:
        error = prediction[test_mask] - truth
        rolling_rows.append({
            "train_max": cutoff,
            "test_max": next_hi,
            "model": name,
            "a": float(aa) if name == "dynamic" else np.nan,
            "b": float(bb) if name == "dynamic" else np.nan,
            "rmse": float(np.sqrt(np.mean(error * error))),
            "bias": float(error.mean()),
            "mae": float(np.abs(error).mean()),
        })
rolling_df = pd.DataFrame(rolling_rows)
rolling_df.to_csv(OUT / "rolling_origin_metrics.csv", index=False)

# Precompute cumulative baselines on an integer grid for exact-activity tests.
interval_models = ["VF base10", "VF dynamic base", "VF asym3 midpoint", "Li"]
max_grid = 3_300_000
xgrid = np.arange(max_grid + 1, dtype=np.float64)
baselines = {}
for name in interval_models:
    print("grid", name)
    if name == "Li":
        values = np.zeros(max_grid + 1, dtype=np.float64)
        values[2:] = li(xgrid[2:])
    else:
        values = np.interp(xgrid, xi, anchors[name]).astype(np.float64)
    baselines[name] = values
mu = mobius_upto(100_000)


def interval_metrics(N, sample_t, min_ratio):
    if sample_t is None or sample_t >= N:
        stages = np.arange(N, 2 * N, dtype=np.int64)
    else:
        stages = np.unique(
            np.linspace(N, 2 * N - 1, sample_t, dtype=np.int64)
        )

    bands = []
    for j in range(1, int(round(math.log2(min_ratio))) + 1):
        lo = max(1, N // (2 ** j))
        hi = max(lo + 1, N // (2 ** (j - 1)))
        bands.append((lo, hi))

    diagonal_total = {model: 0.0 for model in interval_models}
    signed_total = {
        model: np.zeros(len(stages), dtype=np.float64)
        for model in interval_models
    }
    output = []
    chunk = 32

    for lo, hi in bands:
        cofactors = np.arange(lo, hi, dtype=np.int64)
        mu_cofactors = mu[cofactors].astype(np.float64)
        diagonal = {model: 0.0 for model in interval_models}
        signed = {
            model: np.zeros(len(stages), dtype=np.float64)
            for model in interval_models
        }

        for start in range(0, len(stages), chunk):
            stage_chunk = stages[start:start + chunk]
            square = (stage_chunk[:, None] + 1) ** 2
            cofactor_grid = cofactors[None, :]
            lower = np.maximum(
                stage_chunk[:, None] + 2,
                (square + 2 * cofactor_grid - 1) // (2 * cofactor_grid),
            )
            upper = (square - 1) // cofactor_grid
            if upper.max() > max_grid:
                raise RuntimeError((N, lo, int(upper.max()), max_grid))
            prime_count = pi[upper] - pi[lower - 1]

            for model in interval_models:
                residual = prime_count - (
                    baselines[model][upper] - baselines[model][lower - 1]
                )
                diagonal[model] += float(np.sum(residual * residual))
                signed[model][start:start + len(stage_chunk)] = (
                    residual @ mu_cofactors
                )

        for model in interval_models:
            diagonal_norm = diagonal[model] / len(stages) / (N * N)
            signed_norm = float(np.mean(signed[model] ** 2) / (N * N))
            output.append({
                "N": N,
                "nt": len(stages),
                "band_lo": lo,
                "band_hi": hi,
                "model": model,
                "D_norm": diagonal_norm,
                "E_norm": signed_norm,
                "aggregate": False,
            })
            diagonal_total[model] += diagonal_norm
            signed_total[model] += signed[model]

    for model in interval_models:
        output.append({
            "N": N,
            "nt": len(stages),
            "band_lo": bands[-1][0],
            "band_hi": bands[0][1],
            "model": model,
            "D_norm": diagonal_total[model],
            "E_norm": float(np.mean(signed_total[model] ** 2) / (N * N)),
            "aggregate": True,
        })
    return output


interval_rows = []
configs = [
    (1000, None, 64),
    (2000, None, 64),
    (5000, None, 64),
    (10000, 1500, 64),
    (20000, 800, 32),
    (50000, 400, 16),
]
for config in configs:
    print("interval", config)
    interval_rows.extend(interval_metrics(*config))
interval_df = pd.DataFrame(interval_rows)
interval_df.to_csv(OUT / "exact_activity_interval_metrics.csv", index=False)

# Plots.
pivot = global_df.pivot(index="range", columns="model", values="rmse")
ratio = pivot.div(pivot["Li"], axis=0)
fig, axis = plt.subplots(figsize=(10, 6))
for name in [
    "VF base10",
    "VF base e^2",
    "VF dynamic base",
    "VF asym3 midpoint",
    "VF fitted denom 2",
    "VF fitted denom 3",
]:
    axis.plot(range(len(ratio.index)), ratio[name].values, marker="o", label=name)
axis.axhline(1, linestyle="--")
axis.set_xticks(range(len(ratio.index)))
axis.set_xticklabels(ratio.index, rotation=15)
axis.set_ylabel("RMSE / Li RMSE")
axis.set_title("Square-midpoint out-of-sample accuracy")
axis.legend(fontsize=8)
fig.tight_layout()
fig.savefig(OUT / "global_rmse_ratio.png", dpi=180)
plt.close(fig)

aggregate = interval_df[interval_df["aggregate"]].copy()
pivot = aggregate.pivot(index="N", columns="model", values="D_norm")
ratio = pivot.div(pivot["Li"], axis=0)
fig, axis = plt.subplots(figsize=(9, 6))
for name in ["VF base10", "VF dynamic base", "VF asym3 midpoint"]:
    axis.plot(ratio.index, ratio[name], marker="o", label=name)
axis.axhline(1, linestyle="--")
axis.set_xscale("log")
axis.set_xlabel("N")
axis.set_ylabel("sign-blind interval energy / Li energy")
axis.set_title("Exact-activity interval residual energy")
axis.legend()
fig.tight_layout()
fig.savefig(OUT / "interval_energy_ratio.png", dpi=180)
plt.close(fig)

summary = {
    "NMAX": NMAX,
    "fit_range": [1000, 100000],
    "dynamic_log_base": {
        "formula": "log b(L)=2+a/L+b/L^2",
        "a": a_dynamic,
        "b": b_dynamic,
    },
    "direct_fit2_coefficients": coef2.tolist(),
    "direct_fit3_coefficients": coef3.tolist(),
    "files": [
        "global_midpoint_metrics.csv",
        "rolling_origin_metrics.csv",
        "exact_activity_interval_metrics.csv",
        "global_rmse_ratio.png",
        "interval_energy_ratio.png",
    ],
}
(OUT / "summary.json").write_text(json.dumps(summary, indent=2))

report_lines = [
    "# Dynamic-denominator VF empirical test",
    "",
    (
        f"Exact prime counts were sieved through {NMAX:,}. The dynamic base was "
        "fit only on square-block midpoints from 1,000 through 100,000 and then "
        "frozen."
    ),
    "",
    "## Fitted denominator",
    "",
    (
        f"`log b(L) = 2 + {a_dynamic:.15f}/L "
        f"{b_dynamic:+.14f}/L^2`, where `L=log x`."
    ),
    "",
    "## Global midpoint RMSE",
    "",
    global_df.pivot(index="range", columns="model", values="rmse")
    .round(3)
    .to_markdown(),
    "",
    "## Rolling-origin RMSE",
    "",
    rolling_df.pivot_table(
        index=["train_max", "test_max"], columns="model", values="rmse"
    ).round(3).to_markdown(),
    "",
    "## Exact-activity aggregate sign-blind energy",
    "",
    aggregate.pivot(index="N", columns="model", values="D_norm")
    .round(6)
    .to_markdown(),
    "",
    "## Exact-activity aggregate signed energy",
    "",
    aggregate.pivot(index="N", columns="model", values="E_norm")
    .round(6)
    .to_markdown(),
]
(OUT / "REPORT.md").write_text("\n".join(report_lines))

print(global_df.to_string(index=False))
print("\nROLLING\n", rolling_df.to_string(index=False))
print("\nINTERVAL AGG\n", aggregate.to_string(index=False))
print("done", OUT)
