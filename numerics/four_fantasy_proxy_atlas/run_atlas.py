#!/usr/bin/env python3
"""Reproduce the four fantasy prime-count proxy atlas used by RH_Lean.

The four proxy definitions mirror research/FOUR_FANTASY_PROXY_RH_CLOSURES.lean:
  1. continuous Li from 2;
  2. exact discrete VF-mid fractional cluster at square endpoints;
  3. literal midpoint-to-midpoint VF linear interpolant;
  4. integer-cutoff floor(Li) staircase.

All comparisons with actual pi are finite diagnostics. They do not prove the
actual-to-proxy asymptotic bounds consumed by the Lean RH closures.
"""
from __future__ import annotations
import argparse, csv, json, math
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import expi


def li2(x):
    x = np.asarray(x, dtype=float)
    return expi(np.log(x)) - expi(math.log(2.0))


def prime_sieve_bytes(nmax: int) -> bytearray:
    sieve = bytearray(b"\x01") * (nmax + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(nmax) + 1):
        if sieve[p]:
            start = p * p
            count = (nmax - start) // p + 1
            sieve[start:nmax + 1:p] = b"\x00" * count
    return sieve


def prime_counts_at_squares(rmax: int, sieve: bytearray) -> np.ndarray:
    out = np.zeros(rmax + 2, dtype=np.int64)
    running = 0
    prev = 0
    view = memoryview(sieve)
    for r in range(rmax + 2):
        sq = r * r
        if sq >= prev + 1:
            running += sum(view[prev + 1:sq + 1])
        out[r] = running
        prev = sq
    return out


def local_prime_counts(xmax: int, sieve: bytearray) -> np.ndarray:
    a = np.frombuffer(sieve, dtype=np.uint8, count=xmax + 1)
    return np.cumsum(a, dtype=np.int64)


def band_mass(r):
    r = np.asarray(r, dtype=float)
    return (2.0 * r + 1.0) / np.log(r * r + r + 0.5)


def finished_mass_table(rmax: int) -> np.ndarray:
    f = np.zeros(rmax + 4, dtype=float)
    for r in range(2, rmax + 3):
        f[r + 1] = f[r] + float(band_mass(r))
    return f


def vf_mid_scalar(x: float, finished: np.ndarray) -> float:
    if x < 4.0:
        return 0.0
    R = math.floor(math.sqrt(x))
    return finished[R] + (x - R * R) / math.log((R * R + x) / 2.0)


def vf_linear_scalar(x: float, finished: np.ndarray) -> float:
    m2 = 6.5
    if x < m2:
        return vf_mid_scalar(x, finished)
    R = math.floor(math.sqrt(x))
    mR = R * R + R + 0.5
    r = R - 1 if x < mR else R
    a = r * r + r + 0.5
    b = (r + 1) * (r + 1) + (r + 1) + 0.5
    va = vf_mid_scalar(a, finished)
    vb = vf_mid_scalar(b, finished)
    lam = (x - a) / (2.0 * r + 2.0)
    return va + lam * (vb - va)


def vf_linear_vector(xs, finished):
    return np.array([vf_linear_scalar(float(x), finished) for x in xs], dtype=float)


def floor_li_integer_cutoff(xs):
    n = np.floor(np.asarray(xs, dtype=float)).astype(np.int64)
    return np.floor(li2(n.astype(float)))


def crossing_scan(rmax: int, pi_sq: np.ndarray, finished: np.ndarray, c: float):
    k = np.floor(finished[:rmax + 2] + c).astype(np.int64)
    rows = []
    for r in range(2, rmax + 1):
        horizontal = int(pi_sq[r]) <= int(k[r]) <= int(pi_sq[r + 1])
        left = int(k[r - 1]) <= int(pi_sq[r]) <= int(k[r])
        right = int(k[r]) <= int(pi_sq[r + 1]) <= int(k[r + 1])
        rows.append((r, horizontal, left, right, horizontal or left or right))
    return rows


def save_fig(fig, path: Path):
    fig.tight_layout()
    fig.savefig(path, dpi=180, bbox_inches="tight")
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-max", type=int, default=10_000)
    ap.add_argument("--local-x-max", type=int, default=2500)
    ap.add_argument("--rh-start", type=int, default=56)
    ap.add_argument("--out", type=Path, default=Path("numerics/four_fantasy_proxy_atlas/results"))
    args = ap.parse_args()

    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    nmax = (args.r_max + 1) ** 2
    sieve = prime_sieve_bytes(nmax)
    pi_sq = prime_counts_at_squares(args.r_max, sieve)
    finished = finished_mass_table(args.r_max + 3)

    R = np.arange(2, args.r_max + 1, dtype=np.int64)
    x = R * R
    actual = pi_sq[R].astype(float)
    series = {
        "continuous_li": li2(x.astype(float)),
        "fractional_cluster": finished[R],
        "linear_midpoint_vf": vf_linear_vector(x.astype(float), finished),
        "floor_li": floor_li_integer_cutoff(x.astype(float)),
    }
    rhscale = R.astype(float) * np.log(R.astype(float))
    blockscale = R.astype(float) / np.log(R.astype(float))

    with (out / "square_endpoint_proxy_comparison.csv").open("w", newline="") as fh:
        w = csv.writer(fh)
        header = ["R", "x", "pi"]
        for name in series:
            header += [name, f"pi_minus_{name}", f"abs_pi_minus_{name}_over_RlogR", f"abs_pi_minus_{name}_over_blockscale"]
        w.writerow(header)
        for i, r in enumerate(R):
            row = [int(r), int(x[i]), int(actual[i])]
            for name, y in series.items():
                e = actual[i] - y[i]
                row += [f"{y[i]:.15g}", f"{e:.15g}", f"{abs(e)/rhscale[i]:.15g}", f"{abs(e)/blockscale[i]:.15g}"]
            w.writerow(row)

    summary = {"r_min": 2, "r_max": int(args.r_max), "x_max": int(args.r_max ** 2), "rh_start": int(args.rh_start), "proxies": {}}
    tail = R >= args.rh_start
    for name, y in series.items():
        e = actual - y
        q = np.abs(e) / rhscale
        qt = q[tail]
        Rt = R[tail]
        j = int(np.argmax(qt))
        summary["proxies"][name] = {
            "max_abs_error": float(np.max(np.abs(e))),
            "max_abs_error_over_RlogR_R_ge_rh_start": float(qt[j]),
            "argmax_R_for_RlogR_ratio_R_ge_rh_start": int(Rt[j]),
            "final_abs_error_over_RlogR": float(q[-1]),
            "max_abs_error_over_blockscale": float(np.max(np.abs(e) / blockscale)),
        }

    f3 = finished[3]
    c0 = float(pi_sq[3]) - f3
    scan0 = crossing_scan(args.r_max, pi_sq, finished, 0.0)
    scanc = crossing_scan(args.r_max, pi_sq, finished, c0)
    summary["crossing"] = {
        "tested_R_max": int(args.r_max),
        "unaligned_full_graph_failures": [r for r,h,l,rr,ok in scan0 if not ok],
        "anchored_c0": c0,
        "anchored_full_graph_failures": [r for r,h,l,rr,ok in scanc if not ok],
        "anchored_horizontal_failures": [r for r,h,l,rr,ok in scanc if not h],
        "anchored_vertical_rescues": [[r, "L" if l else "R"] for r,h,l,rr,ok in scanc if ok and not h],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    fig, ax = plt.subplots(figsize=(11, 6.5))
    ax.plot(R, actual, label="actual pi(R^2)", linewidth=2.2)
    ax.plot(R, series["continuous_li"], label="continuous Li", linewidth=1.0)
    ax.plot(R, series["fractional_cluster"], label="fractional VF cluster", linewidth=1.0)
    ax.plot(R, series["linear_midpoint_vf"], label="midpoint-linear VF", linewidth=1.0)
    ax.plot(R, series["floor_li"], label="floor Li", linewidth=1.0)
    ax.set_title("Actual prime count and the four RH-closing fantasy proxies")
    ax.set_xlabel("square-root index R (x = R^2)")
    ax.set_ylabel("count")
    ax.legend(ncol=2)
    ax.grid(True, alpha=.2)
    save_fig(fig, out / "four_proxy_pi_overlay_global.png")

    Rt = R[tail]
    fig, ax = plt.subplots(figsize=(11, 6.5))
    for name, y in series.items():
        ax.plot(Rt, ((actual - y) / rhscale)[tail], label=name, linewidth=1.0)
    ax.set_title(f"Actual minus proxy, normalized by R log R (R >= {args.rh_start})")
    ax.set_xlabel("square-root index R")
    ax.set_ylabel("(pi(R^2) - proxy(R^2)) / (R log R)")
    ax.legend(ncol=2)
    ax.grid(True, alpha=.2)
    save_fig(fig, out / "four_proxy_rh_normalized_residuals.png")

    fig, ax = plt.subplots(figsize=(11, 6.5))
    for name, y in series.items():
        ax.plot(Rt, (np.abs(actual - y) / blockscale)[tail], label=name, linewidth=1.0)
    ax.set_title(f"Absolute actual-to-proxy discrepancy in one-block units (R >= {args.rh_start})")
    ax.set_xlabel("square-root index R")
    ax.set_ylabel("|pi(R^2) - proxy(R^2)| / (R/log R)")
    ax.legend(ncol=2)
    ax.grid(True, alpha=.2)
    save_fig(fig, out / "four_proxy_block_scale_residuals.png")

    local_pi = local_prime_counts(args.local_x_max, sieve)
    xs = np.arange(4, args.local_x_max + 1, dtype=np.int64)
    p = local_pi[xs].astype(float)
    local = {
        "continuous_li": ("Continuous Li", li2(xs.astype(float)), "line"),
        "linear_midpoint_vf": ("Literal midpoint-linear VF", vf_linear_vector(xs.astype(float), finished), "line"),
        "floor_li": ("Integer-cutoff floor(Li)", floor_li_integer_cutoff(xs.astype(float)), "step"),
    }
    for key, (label, y, kind) in local.items():
        fig, ax = plt.subplots(figsize=(11, 6.5))
        ax.step(xs, p, where="post", label="actual pi(x)", linewidth=1.8)
        if kind == "step":
            ax.step(xs, y, where="post", label=label, linewidth=1.2)
        else:
            ax.plot(xs, y, label=label, linewidth=1.3)
        ax.set_title(f"Actual pi(x) vs {label}, 4 <= x <= {args.local_x_max}")
        ax.set_xlabel("x")
        ax.set_ylabel("count / proxy value")
        ax.legend()
        ax.grid(True, alpha=.2)
        save_fig(fig, out / f"overlay_{key}.png")

    Rs = np.arange(2, math.isqrt(args.local_x_max) + 1, dtype=np.int64)
    sqx = Rs * Rs
    fig, ax = plt.subplots(figsize=(11, 6.5))
    ax.step(xs, p, where="post", label="actual pi(x)", linewidth=1.8)
    ax.scatter(sqx, finished[Rs], label="fractional VF cluster (square endpoints)", s=18)
    ax.set_title(f"Actual pi(x) vs exact fractional VF cluster, 4 <= x <= {args.local_x_max}")
    ax.set_xlabel("x")
    ax.set_ylabel("count / proxy value")
    ax.legend()
    ax.grid(True, alpha=.2)
    save_fig(fig, out / "overlay_fractional_cluster.png")

    rscan = np.array([row[0] for row in scanc], dtype=int)
    status = np.array([0 if row[1] else (1 if row[4] else 2) for row in scanc], dtype=float)
    fig, ax = plt.subplots(figsize=(11, 3.8))
    ax.scatter(rscan, status, s=7)
    ax.set_yticks([0, 1, 2], labels=["horizontal", "vertical rescue", "miss"])
    ax.set_ylim(-.5, 2.5)
    ax.set_title("Anchored VF step-graph intersection diagnostic by square block")
    ax.set_xlabel("R")
    ax.set_ylabel("intersection mode")
    ax.grid(True, axis="x", alpha=.15)
    save_fig(fig, out / "vf_step_graph_crossing_diagnostic.png")

    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
