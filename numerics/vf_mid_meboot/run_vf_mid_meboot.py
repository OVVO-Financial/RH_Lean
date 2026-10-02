from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy.stats import spearmanr

from nns.meboot import nns_meboot


R0_DEFAULT = 56
RMAX_DEFAULT = 3162
RHO_GRID = np.array([-0.95, -0.75, -0.50, -0.25, 0.0, 0.25, 0.50, 0.75, 0.95])
PHIS = [-0.90, -0.50, 0.0, 0.50, 0.90, 0.97, 0.99]


def sieve_prime_counts(limit: int) -> np.ndarray:
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[p]:
            is_prime[p * p : limit + 1 : p] = False
    return np.cumsum(is_prime, dtype=np.int64)


def vf_mass(r: np.ndarray) -> np.ndarray:
    rr = r.astype(np.float64)
    midpoint = rr * rr + rr + 0.5
    return (2.0 * rr + 1.0) / np.log(midpoint)


def build_actual_series(r0: int, rmax: int) -> dict[str, np.ndarray | float]:
    if r0 < 3:
        raise ValueError("r0 must be at least 3 so the odd-seat variance is positive")
    if rmax <= r0:
        raise ValueError("rmax must exceed r0")

    pi = sieve_prime_counts(rmax * rmax)
    all_r = np.arange(2, rmax, dtype=np.int64)
    all_v = vf_mass(all_r)
    vf_prefix = np.concatenate(([0.0], np.cumsum(all_v)))

    r = np.arange(r0, rmax, dtype=np.int64)
    p_block = pi[(r + 1) ** 2] - pi[r**2]
    v = vf_mass(r)
    error = p_block.astype(np.float64) - v
    w = v / r
    variance = r * w * (1.0 - w)
    z = error / np.sqrt(variance)

    # vf_prefix[j] = sum_{r=2}^{2+j-1} V_r. For R=r0, sum through r0-1.
    idx = r0 - 2
    vf_at_r0_sq = vf_prefix[idx]
    d0 = float(pi[r0 * r0] - vf_at_r0_sq)

    return {
        "r": r,
        "p_block": p_block,
        "v": v,
        "error": error,
        "w": w,
        "variance": variance,
        "z": z,
        "d0": d0,
    }


def corr(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.corrcoef(a, b)[0, 1])


def path_metrics(
    zz: np.ndarray,
    z_actual: np.ndarray,
    variance: np.ndarray,
    d0: float,
    r_end: np.ndarray,
    suite: str,
    **extra: float | int | str,
) -> dict[str, float | int | str]:
    sigma = np.sqrt(variance)
    ee = zz * sigma
    centered = np.cumsum(ee)
    d = d0 + centered
    b = np.cumsum(variance)
    rh = np.abs(d) / (r_end * np.log(r_end))
    out: dict[str, float | int | str] = {
        "suite": suite,
        **extra,
        "realized_pearson_to_actual": corr(zz, z_actual),
        "realized_spearman_to_actual": float(spearmanr(zz, z_actual).statistic),
        "lag1": corr(zz[:-1], zz[1:]),
        "lag2": corr(zz[:-2], zz[2:]),
        "mean_z": float(np.mean(zz)),
        "sd_z": float(np.std(zz, ddof=1)),
        "max_rh_ratio_all": float(np.max(rh)),
        "max_rh_ratio_R_ge_500": float(np.max(rh[r_end >= 500])),
        "max_rh_ratio_R_ge_1000": float(np.max(rh[r_end >= 1000])),
        "final_rh_ratio": float(rh[-1]),
        "max_centered_z": float(np.max(np.abs(centered) / np.sqrt(b))),
        "max_K_log3B": float(np.max(centered**2 / ((np.log(r_end) ** 3) * b))),
        "final_D": float(d[-1]),
    }
    return out


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
        "max_centered_z",
        "max_K_log3B",
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
            if col not in group.columns:
                continue
            a = group[col].to_numpy(dtype=np.float64)
            for label, q in (("q05", 0.05), ("median", 0.50), ("q95", 0.95), ("q99", 0.99), ("max", 1.0)):
                row[f"{col}_{label}"] = float(np.quantile(a, q))
        rows.append(row)
    return pd.DataFrame(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description="VF-mid NNS.meboot dependence stress suite")
    parser.add_argument("--out", type=Path, default=Path("numerics/vf_mid_meboot/results"))
    parser.add_argument("--r0", type=int, default=R0_DEFAULT)
    parser.add_argument("--rmax", type=int, default=RMAX_DEFAULT)
    parser.add_argument("--main-reps", type=int, default=199)
    parser.add_argument("--serial-templates", type=int, default=3)
    parser.add_argument("--serial-reps", type=int, default=49)
    args = parser.parse_args()

    outdir: Path = args.out
    outdir.mkdir(parents=True, exist_ok=True)

    actual = build_actual_series(args.r0, args.rmax)
    r = np.asarray(actual["r"], dtype=np.int64)
    z = np.asarray(actual["z"], dtype=np.float64)
    variance = np.asarray(actual["variance"], dtype=np.float64)
    e_actual = np.asarray(actual["error"], dtype=np.float64)
    d0 = float(actual["d0"])
    r_end = r + 1
    b = np.cumsum(variance)
    centered_actual = np.cumsum(e_actual)
    d_actual = d0 + centered_actual
    rh_actual = np.abs(d_actual) / (r_end * np.log(r_end))

    actual_metrics = {
        "R0": int(args.r0),
        "Rmax": int(args.rmax),
        "n_blocks": int(len(r)),
        "D0": d0,
        "lag1": corr(z[:-1], z[1:]),
        "lag2": corr(z[:-2], z[2:]),
        "max_rh_ratio_all": float(rh_actual.max()),
        "max_rh_ratio_R_ge_500": float(rh_actual[r_end >= 500].max()),
        "max_rh_ratio_R_ge_1000": float(rh_actual[r_end >= 1000].max()),
        "final_rh_ratio": float(rh_actual[-1]),
        "max_centered_z": float(np.max(np.abs(centered_actual) / np.sqrt(b))),
        "max_K_log3B": float(np.max(centered_actual**2 / ((np.log(r_end) ** 3) * b))),
    }
    (outdir / "actual_metrics.json").write_text(json.dumps(actual_metrics, indent=2) + "\n")

    main_rows: list[dict[str, float | int | str]] = []
    for method in ("pearson", "spearman"):
        offset = 0 if method == "pearson" else 10000
        for ri, rho in enumerate(RHO_GRID):
            boot = nns_meboot(
                z,
                reps=args.main_reps,
                rho=float(rho),
                type=method,
                drift=True,
                expand_sd=True,
                force_clt=True,
                random_seed=20261001 + offset + ri * 100,
            )
            mat = np.asarray(boot["replicates"], dtype=np.float64)
            for j in range(mat.shape[1]):
                main_rows.append(
                    path_metrics(
                        mat[:, j],
                        z,
                        variance,
                        d0,
                        r_end,
                        "actual_dependence_sweep",
                        method=method,
                        target_rho=float(rho),
                        replicate=j,
                    )
                )

    main_df = pd.DataFrame(main_rows)
    main_df.to_csv(outdir / "meboot_replicate_metrics.csv", index=False)
    main_summary = summarize(main_df, ["method", "target_rho"])
    main_summary.to_csv(outdir / "meboot_dependence_summary.csv", index=False)

    serial_rows: list[dict[str, float | int | str]] = []
    for pi, phi in enumerate(PHIS):
        for template_id in range(args.serial_templates):
            rng = np.random.default_rng(910000 + pi * 100 + template_id)
            seed_series = rank_reorder(z, ar1(len(z), phi, rng))
            boot = nns_meboot(
                seed_series,
                reps=args.serial_reps,
                rho=0.95,
                type="spearman",
                drift=False,
                expand_sd=True,
                force_clt=True,
                random_seed=920000 + pi * 100 + template_id,
            )
            mat = np.asarray(boot["replicates"], dtype=np.float64)
            for j in range(mat.shape[1]):
                row = path_metrics(
                    mat[:, j],
                    z,
                    variance,
                    d0,
                    r_end,
                    "serial_persistence_stress",
                    phi=float(phi),
                    template=template_id,
                    replicate=j,
                    seed_lag1=corr(seed_series[:-1], seed_series[1:]),
                )
                row["realized_spearman_to_template"] = float(spearmanr(mat[:, j], seed_series).statistic)
                serial_rows.append(row)

    serial_df = pd.DataFrame(serial_rows)
    serial_df.to_csv(outdir / "meboot_serial_stress_metrics.csv", index=False)
    serial_summary = summarize(serial_df, ["phi"])
    serial_summary.to_csv(outdir / "meboot_serial_stress_summary.csv", index=False)

    all_df = pd.concat(
        [main_df.assign(source="main"), serial_df.assign(source="serial")],
        ignore_index=True,
        sort=False,
    )
    all_df["lag1_bin"] = pd.cut(all_df.lag1, bins=np.linspace(-1, 1, 21), include_lowest=True)
    bin_summary = (
        all_df.groupby("lag1_bin", observed=True)
        .agg(
            n=("lag1", "size"),
            lag1_mean=("lag1", "mean"),
            rh1000_median=("max_rh_ratio_R_ge_1000", "median"),
            rh1000_q95=("max_rh_ratio_R_ge_1000", lambda x: np.quantile(x, 0.95)),
            rh1000_max=("max_rh_ratio_R_ge_1000", "max"),
            K_median=("max_K_log3B", "median"),
            K_q95=("max_K_log3B", lambda x: np.quantile(x, 0.95)),
            K_max=("max_K_log3B", "max"),
        )
        .reset_index()
    )
    bin_summary.to_csv(outdir / "meboot_realized_lag1_bins.csv", index=False)

    fig, ax = plt.subplots(figsize=(9, 6))
    for method, group in main_summary.groupby("method"):
        group = group.sort_values("target_rho")
        x = group.target_rho.to_numpy(dtype=np.float64)
        med = group.max_rh_ratio_R_ge_1000_median.to_numpy(dtype=np.float64)
        lo = group.max_rh_ratio_R_ge_1000_q05.to_numpy(dtype=np.float64)
        hi = group.max_rh_ratio_R_ge_1000_q95.to_numpy(dtype=np.float64)
        ax.plot(x, med, marker="o", label=f"{method} median")
        ax.fill_between(x, lo, hi, alpha=0.18)
    ax.axhline(actual_metrics["max_rh_ratio_R_ge_1000"], linestyle="--", label="actual primes")
    ax.set_xlabel("NNS.meboot target correlation to actual standardized VF error")
    ax.set_ylabel("max |D_R|/(R log R), R >= 1000")
    ax.set_title("NNS.meboot dependence frontier")
    ax.legend()
    fig.tight_layout()
    fig.savefig(outdir / "meboot_dependence_frontier.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(9, 6))
    sample = all_df.sample(min(4000, len(all_df)), random_state=17)
    ax.scatter(sample.lag1, sample.max_rh_ratio_R_ge_1000, s=10, alpha=0.25)
    ax.scatter(
        [actual_metrics["lag1"]],
        [actual_metrics["max_rh_ratio_R_ge_1000"]],
        s=100,
        marker="x",
        label="actual primes",
    )
    ax.set_xlabel("realized lag-1 correlation")
    ax.set_ylabel("max |D_R|/(R log R), R >= 1000")
    ax.set_title("Serial persistence vs RH-normalized VF excursion")
    ax.legend()
    fig.tight_layout()
    fig.savefig(outdir / "meboot_lag1_vs_rh_ratio.png", dpi=180)
    plt.close(fig)

    serial_summary = serial_summary.sort_values("phi")
    fig, ax = plt.subplots(figsize=(9, 6))
    x = serial_summary.phi.to_numpy(dtype=np.float64)
    med = serial_summary.max_rh_ratio_R_ge_1000_median.to_numpy(dtype=np.float64)
    lo = serial_summary.max_rh_ratio_R_ge_1000_q05.to_numpy(dtype=np.float64)
    hi = serial_summary.max_rh_ratio_R_ge_1000_q95.to_numpy(dtype=np.float64)
    ax.plot(x, med, marker="o", label="stress median")
    ax.fill_between(x, lo, hi, alpha=0.18)
    ax.axhline(actual_metrics["max_rh_ratio_R_ge_1000"], linestyle="--", label="actual primes")
    ax.set_xlabel("latent AR(1) rank-template persistence phi")
    ax.set_ylabel("max |D_R|/(R log R), R >= 1000")
    ax.set_title("NNS.meboot serial-persistence stress test")
    ax.legend()
    fig.tight_layout()
    fig.savefig(outdir / "meboot_serial_persistence_stress.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(9, 6))
    ax.plot(serial_summary.phi, serial_summary.max_K_log3B_median, marker="o", label="median K required")
    ax.plot(serial_summary.phi, serial_summary.max_K_log3B_q95, marker="o", label="95th percentile K required")
    ax.axhline(actual_metrics["max_K_log3B"], linestyle="--", label="actual primes")
    ax.set_yscale("log")
    ax.set_xlabel("latent AR(1) rank-template persistence phi")
    ax.set_ylabel("max C_R^2 / ((log R)^3 B_R)")
    ax.set_title("Empirical constant required by proposed polylog variance bound")
    ax.legend()
    fig.tight_layout()
    fig.savefig(outdir / "meboot_polylog_K_stress.png", dpi=180)
    plt.close(fig)

    report = {
        "main_paths": int(len(main_df)),
        "serial_paths": int(len(serial_df)),
        "total_paths": int(len(main_df) + len(serial_df)),
        "main_pooled_max_RH1000": float(main_df.max_rh_ratio_R_ge_1000.max()),
        "main_pooled_q99_RH1000": float(np.quantile(main_df.max_rh_ratio_R_ge_1000, 0.99)),
        "serial_pooled_max_RH1000": float(serial_df.max_rh_ratio_R_ge_1000.max()),
        "serial_pooled_q99_RH1000": float(np.quantile(serial_df.max_rh_ratio_R_ge_1000, 0.99)),
        "serial_pooled_max_K": float(serial_df.max_K_log3B.max()),
        "serial_pooled_q99_K": float(np.quantile(serial_df.max_K_log3B, 0.99)),
        "serial_fraction_K_le_1": float(np.mean(serial_df.max_K_log3B <= 1.0)),
        "all_paths_RH1000_lt_1": bool(
            (main_df.max_rh_ratio_R_ge_1000 < 1.0).all()
            and (serial_df.max_rh_ratio_R_ge_1000 < 1.0).all()
        ),
    }
    (outdir / "suite_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"actual": actual_metrics, "suite": report}, indent=2))


if __name__ == "__main__":
    main()
