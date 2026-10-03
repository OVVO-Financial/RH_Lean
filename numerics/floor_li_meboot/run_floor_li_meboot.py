from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy.special import expi
from scipy.stats import spearmanr

from nns.meboot import nns_meboot


R0_DEFAULT = 56
RMAX_DEFAULT = 3162
RHO_GRID = np.array([-0.95, -0.75, -0.50, -0.25, 0.0, 0.25, 0.50, 0.75, 0.95])
PHIS = [-0.90, -0.50, 0.0, 0.50, 0.90, 0.97, 0.99]


def sieve_bool(limit: int) -> np.ndarray:
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            is_prime[p * p : limit + 1 : p] = False
    return is_prime


def li2(x: np.ndarray | float) -> np.ndarray | float:
    """Repository Li normalization: Li(x) - Li(2)."""
    return expi(np.log(x)) - expi(math.log(2.0))


def corr(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.corrcoef(a, b)[0, 1])


def classify_preserve_marginal(
    continuous: np.ndarray,
    observed_discrete: np.ndarray,
) -> np.ndarray:
    """Rank-project each replicate onto the exact observed discrete multiset."""
    values = np.sort(np.asarray(observed_discrete, dtype=np.float64))
    out = np.empty_like(continuous, dtype=np.float64)
    for j in range(continuous.shape[1]):
        order = np.argsort(continuous[:, j], kind="mergesort")
        out[order, j] = values
    return out


def primitive_stats(
    is_prime: np.ndarray,
    limit: int,
    chunk: int = 500_000,
) -> dict[str, object]:
    counts = {-1: 0, 0: 0, 1: 0}
    transition = np.zeros((3, 3), dtype=np.int64)
    bad_floor_jumps = 0
    floor_jumps = 0
    prime_jumps = 0
    matched = 0

    lag1_n = lag2_n = 0
    lag1_xy = lag1_x = lag1_y = lag1_x2 = lag1_y2 = 0.0
    lag2_xy = lag2_x = lag2_y = lag2_x2 = lag2_y2 = 0.0

    previous: list[int] = []
    last_q = int(math.floor(float(li2(2.0))))

    for start in range(3, limit + 1, chunk):
        end = min(limit + 1, start + chunk)
        n = np.arange(start, end, dtype=np.float64)
        q = np.floor(li2(n)).astype(np.int64)
        q_prev = np.empty_like(q)
        q_prev[0] = last_q
        q_prev[1:] = q[:-1]
        floor_step = q - q_prev

        bad_floor_jumps += int(np.count_nonzero((floor_step < 0) | (floor_step > 1)))
        floor_jumps += int(floor_step.sum())

        prime_step = is_prime[start:end].astype(np.int8)
        prime_jumps += int(prime_step.sum())
        xi = prime_step - floor_step.astype(np.int8)

        for value in (-1, 0, 1):
            counts[value] += int(np.count_nonzero(xi == value))
        matched += int(np.count_nonzero((prime_step == 1) & (floor_step == 1)))

        seq = (
            np.concatenate((np.asarray(previous[-2:], dtype=np.int8), xi))
            if previous
            else xi
        )
        offset = 2 if previous else 0

        if len(seq) >= 2:
            a = seq[:-1]
            b = seq[1:]
            begin = max(0, offset - 1)
            a = a[begin:]
            b = b[begin:]
            np.add.at(transition, (a + 1, b + 1), 1)
            lag1_xy += float(np.sum(a * b))
            lag1_x += float(np.sum(a))
            lag1_y += float(np.sum(b))
            lag1_x2 += float(np.sum(a * a))
            lag1_y2 += float(np.sum(b * b))
            lag1_n += len(a)

        if len(seq) >= 3:
            a = seq[:-2]
            b = seq[2:]
            begin = max(0, offset - 2)
            a = a[begin:]
            b = b[begin:]
            lag2_xy += float(np.sum(a * b))
            lag2_x += float(np.sum(a))
            lag2_y += float(np.sum(b))
            lag2_x2 += float(np.sum(a * a))
            lag2_y2 += float(np.sum(b * b))
            lag2_n += len(a)

        previous = list(xi[-2:])
        last_q = int(q[-1])

    def streaming_corr(
        n: int, xy: float, x: float, y: float, x2: float, y2: float
    ) -> float:
        num = n * xy - x * y
        den = math.sqrt((n * x2 - x * x) * (n * y2 - y * y))
        return num / den

    total = sum(counts.values())
    return {
        "counts": counts,
        "n": total,
        "nonzero_fraction": (counts[-1] + counts[1]) / total,
        "bad_floor_jumps": bad_floor_jumps,
        "floor_jumps": floor_jumps,
        "prime_jumps": prime_jumps,
        "matched_prime_floor_jumps": matched,
        "lag1": streaming_corr(
            lag1_n, lag1_xy, lag1_x, lag1_y, lag1_x2, lag1_y2
        ),
        "lag2": streaming_corr(
            lag2_n, lag2_xy, lag2_x, lag2_y, lag2_x2, lag2_y2
        ),
        "transition_matrix": transition.tolist(),
    }


def path_metrics(
    error: np.ndarray,
    actual_error: np.ndarray,
    d0: float,
    r_end: np.ndarray,
    suite: str,
    **extra: float | int | str,
) -> dict[str, float | int | str]:
    backlog = d0 + np.cumsum(error)
    rh = np.abs(backlog) / (r_end * np.log(r_end))
    return {
        "suite": suite,
        **extra,
        "realized_pearson_to_actual": corr(error, actual_error),
        "realized_spearman_to_actual": float(
            spearmanr(error, actual_error).statistic
        ),
        "lag1": corr(error[:-1], error[1:]),
        "lag2": corr(error[:-2], error[2:]),
        "max_rh_ratio_all": float(rh.max()),
        "max_rh_ratio_R_ge_500": float(rh[r_end >= 500].max()),
        "max_rh_ratio_R_ge_1000": float(rh[r_end >= 1000].max()),
        "final_rh_ratio": float(rh[-1]),
        "final_backlog": float(backlog[-1]),
    }


def ar1(n: int, phi: float, rng: np.random.Generator) -> np.ndarray:
    x = np.empty(n, dtype=np.float64)
    x[0] = rng.normal()
    scale = math.sqrt(max(1e-12, 1.0 - phi * phi))
    for i in range(1, n):
        x[i] = phi * x[i - 1] + scale * rng.normal()
    return x


def rank_reorder(values: np.ndarray, template: np.ndarray) -> np.ndarray:
    order = np.argsort(template, kind="mergesort")
    out = np.empty_like(values)
    out[order] = np.sort(values)
    return out


def summarize(df: pd.DataFrame, keys: list[str]) -> pd.DataFrame:
    columns = [
        "realized_pearson_to_actual",
        "realized_spearman_to_actual",
        "lag1",
        "lag2",
        "max_rh_ratio_all",
        "max_rh_ratio_R_ge_500",
        "max_rh_ratio_R_ge_1000",
        "final_rh_ratio",
    ]
    if "realized_spearman_to_template" in df.columns:
        columns.append("realized_spearman_to_template")

    rows: list[dict[str, float | int | str]] = []
    group_arg: str | list[str] = keys[0] if len(keys) == 1 else keys
    for key, group in df.groupby(group_arg, dropna=False):
        key_tuple = key if isinstance(key, tuple) else (key,)
        row: dict[str, float | int | str] = dict(zip(keys, key_tuple))
        row["n"] = len(group)
        for col in columns:
            a = group[col].to_numpy(dtype=np.float64)
            for label, q in (
                ("q05", 0.05),
                ("median", 0.50),
                ("q95", 0.95),
                ("q99", 0.99),
                ("max", 1.0),
            ):
                row[f"{col}_{label}"] = float(np.quantile(a, q))
        rows.append(row)
    return pd.DataFrame(rows)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Discrete floor-Li NNS.meboot dependence stress suite"
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("numerics/floor_li_meboot/results"),
    )
    parser.add_argument("--r0", type=int, default=R0_DEFAULT)
    parser.add_argument("--rmax", type=int, default=RMAX_DEFAULT)
    parser.add_argument("--main-reps", type=int, default=199)
    parser.add_argument("--serial-templates", type=int, default=3)
    parser.add_argument("--serial-reps", type=int, default=49)
    args = parser.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    limit = args.rmax * args.rmax

    is_prime = sieve_bool(limit)
    pi = np.cumsum(is_prime, dtype=np.int64)

    primitive = primitive_stats(is_prime, limit)
    (args.out / "primitive_metrics.json").write_text(
        json.dumps(primitive, indent=2) + "\n"
    )

    r = np.arange(args.r0, args.rmax, dtype=np.int64)
    p_block = pi[(r + 1) ** 2] - pi[r**2]

    endpoint_r = np.arange(args.r0, args.rmax + 1, dtype=np.float64)
    q = np.floor(li2(endpoint_r**2)).astype(np.int64)
    f_block = np.diff(q)
    error = p_block - f_block

    d0 = int(pi[args.r0**2] - q[0])
    r_end = r + 1
    actual_backlog = d0 + np.cumsum(error)
    actual_rh = np.abs(actual_backlog) / (r_end * np.log(r_end))

    actual_metrics = {
        "R0": int(args.r0),
        "Rmax": int(args.rmax),
        "n_blocks": int(len(r)),
        "xmax": int(limit),
        "D0": d0,
        "block_error_min": int(error.min()),
        "block_error_max": int(error.max()),
        "block_error_mean": float(error.mean()),
        "block_error_sd": float(error.std(ddof=1)),
        "lag1": corr(error[:-1], error[1:]),
        "lag2": corr(error[:-2], error[2:]),
        "max_rh_ratio_all": float(actual_rh.max()),
        "max_rh_ratio_R_ge_500": float(actual_rh[r_end >= 500].max()),
        "max_rh_ratio_R_ge_1000": float(actual_rh[r_end >= 1000].max()),
        "final_rh_ratio": float(actual_rh[-1]),
        "final_backlog": int(actual_backlog[-1]),
        "endpoint_identity_check": int(
            actual_backlog[-1] - (int(pi[args.rmax**2]) - int(q[-1]))
        ),
    }
    (args.out / "actual_block_metrics.json").write_text(
        json.dumps(actual_metrics, indent=2) + "\n"
    )
    pd.DataFrame(
        {"R": r, "P_R": p_block, "F_R": f_block, "P_minus_F": error}
    ).to_csv(args.out / "actual_floor_li_blocks.csv", index=False)

    main_rows: list[dict[str, float | int | str]] = []
    for method in ("pearson", "spearman"):
        offset = 0 if method == "pearson" else 10_000
        for ri, rho in enumerate(RHO_GRID):
            boot = nns_meboot(
                error,
                reps=args.main_reps,
                rho=float(rho),
                type=method,
                drift=True,
                expand_sd=True,
                force_clt=True,
                random_seed=20261002 + offset + ri * 100,
            )
            continuous = np.asarray(boot["replicates"], dtype=np.float64)
            discrete = classify_preserve_marginal(continuous, error)
            for j in range(discrete.shape[1]):
                main_rows.append(
                    path_metrics(
                        discrete[:, j],
                        error,
                        d0,
                        r_end,
                        "actual_dependence_sweep",
                        method=method,
                        target_rho=float(rho),
                        replicate=j,
                        projection="rank_classification",
                    )
                )

    main_df = pd.DataFrame(main_rows)
    main_df.to_csv(args.out / "meboot_replicate_metrics.csv", index=False)
    main_summary = summarize(main_df, ["method", "target_rho"])
    main_summary.to_csv(args.out / "meboot_dependence_summary.csv", index=False)

    serial_rows: list[dict[str, float | int | str]] = []
    for pi_idx, phi in enumerate(PHIS):
        for template_id in range(args.serial_templates):
            rng = np.random.default_rng(910000 + pi_idx * 100 + template_id)
            seed_series = rank_reorder(
                error, ar1(len(error), phi, rng)
            )
            boot = nns_meboot(
                seed_series,
                reps=args.serial_reps,
                rho=0.95,
                type="spearman",
                drift=False,
                expand_sd=True,
                force_clt=True,
                random_seed=920000 + pi_idx * 100 + template_id,
            )
            continuous = np.asarray(boot["replicates"], dtype=np.float64)
            discrete = classify_preserve_marginal(continuous, error)
            for j in range(discrete.shape[1]):
                row = path_metrics(
                    discrete[:, j],
                    error,
                    d0,
                    r_end,
                    "serial_persistence_stress",
                    phi=float(phi),
                    template=template_id,
                    replicate=j,
                    seed_lag1=corr(seed_series[:-1], seed_series[1:]),
                    projection="rank_classification",
                )
                row["realized_spearman_to_template"] = float(
                    spearmanr(discrete[:, j], seed_series).statistic
                )
                serial_rows.append(row)

    serial_df = pd.DataFrame(serial_rows)
    serial_df.to_csv(args.out / "meboot_serial_stress_metrics.csv", index=False)
    serial_summary = summarize(serial_df, ["phi"])
    serial_summary.to_csv(
        args.out / "meboot_serial_stress_summary.csv", index=False
    )

    suite = {
        "main_paths": int(len(main_df)),
        "serial_paths": int(len(serial_df)),
        "total_paths": int(len(main_df) + len(serial_df)),
        "main_pooled_q99_RH1000": float(
            np.quantile(main_df.max_rh_ratio_R_ge_1000, 0.99)
        ),
        "main_pooled_max_RH1000": float(
            main_df.max_rh_ratio_R_ge_1000.max()
        ),
        "serial_pooled_q99_RH1000": float(
            np.quantile(serial_df.max_rh_ratio_R_ge_1000, 0.99)
        ),
        "serial_pooled_max_RH1000": float(
            serial_df.max_rh_ratio_R_ge_1000.max()
        ),
        "serial_max_realized_lag1": float(serial_df.lag1.max()),
        "serial_phi_099_median_lag1": float(
            serial_df.loc[serial_df.phi == 0.99, "lag1"].median()
        ),
        "serial_phi_099_max_lag1": float(
            serial_df.loc[serial_df.phi == 0.99, "lag1"].max()
        ),
        "all_paths_RH1000_lt_1": bool(
            (main_df.max_rh_ratio_R_ge_1000 < 1.0).all()
            and (serial_df.max_rh_ratio_R_ge_1000 < 1.0).all()
        ),
        "classification_projection":
            "rank-map each continuous NNS.meboot replicate onto exact "
            "observed integer block-error multiset",
    }
    (args.out / "suite_summary.json").write_text(
        json.dumps(suite, indent=2) + "\n"
    )

    serial_summary = serial_summary.sort_values("phi")
    fig, ax = plt.subplots(figsize=(9, 6))
    ax.plot(
        serial_summary.phi,
        serial_summary.max_rh_ratio_R_ge_1000_median,
        marker="o",
        label="median",
    )
    ax.plot(
        serial_summary.phi,
        serial_summary.max_rh_ratio_R_ge_1000_q95,
        marker="o",
        label="95th percentile",
    )
    ax.axhline(
        actual_metrics["max_rh_ratio_R_ge_1000"],
        linestyle="--",
        label="actual",
    )
    ax.set_xlabel("latent AR(1) rank-template persistence phi")
    ax.set_ylabel("max |E_R|/(R log R), R >= 1000")
    ax.set_title("Discrete floor-Li NNS.meboot persistence stress")
    ax.legend()
    fig.tight_layout()
    fig.savefig(args.out / "serial_persistence_stress.png", dpi=180)
    plt.close(fig)

    print(json.dumps({"primitive": primitive, "actual": actual_metrics, "suite": suite}, indent=2))


if __name__ == "__main__":
    main()
