from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from scipy.special import expi

R0 = 56
RMAX = 10_000
N0 = R0 * R0
N = RMAX * RMAX
LI2_CONST = float(expi(math.log(2.0)))


def robust_floor_li2(values: np.ndarray, near_tol: float = 2e-7) -> tuple[np.ndarray, int]:
    values = np.asarray(values, dtype=np.int64)
    vals = expi(np.log(values.astype(np.float64))) - LI2_CONST
    floors = np.floor(vals).astype(np.int64)
    near = np.flatnonzero(np.abs(vals - np.rint(vals)) < near_tol)
    if near.size:
        import mpmath as mp

        mp.mp.dps = 60
        c = mp.ei(mp.log(2))
        for j in near:
            x = int(values[j])
            floors[j] = int(mp.floor(mp.ei(mp.log(x)) - c))
    return floors, int(near.size)


def prime_sieve(limit: int) -> np.ndarray:
    is_prime = np.ones(limit + 1, dtype=np.bool_)
    is_prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            is_prime[p * p : limit + 1 : p] = False
    return is_prime


def quantiles(values: np.ndarray) -> dict[str, float]:
    qs = [0, 0.01, 0.05, 0.25, 0.5, 0.75, 0.95, 0.99, 1]
    return {str(q): float(np.quantile(values, q)) for q in qs}


def corr(a: np.ndarray, b: np.ndarray) -> float:
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    if len(a) < 2 or np.std(a) == 0 or np.std(b) == 0:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def mine_transport(is_prime: np.ndarray) -> dict:
    pi0 = int(np.count_nonzero(is_prime[: N0 + 1]))
    q0 = int(robust_floor_li2(np.array([N0], dtype=np.int64))[0][0])
    d0 = pi0 - q0

    prev_q = q0
    backlog = d0
    min_backlog = d0
    max_backlog = d0
    near_total = 0
    minus_parts: list[np.ndarray] = []
    plus_parts: list[np.ndarray] = []
    overlap_parts: list[np.ndarray] = []

    chunk = 2_000_000
    for lo in range(N0 + 1, N + 1, chunk):
        hi = min(N + 1, lo + chunk)
        arr = np.arange(lo, hi, dtype=np.int64)
        floor_li, near = robust_floor_li2(arr)
        near_total += near

        dq = np.empty(len(arr), dtype=np.int8)
        dq[0] = floor_li[0] - prev_q
        dq[1:] = np.diff(floor_li).astype(np.int8)

        prime = is_prime[lo:hi]
        minus_idx = np.flatnonzero((~prime) & (dq == 1))
        plus_idx = np.flatnonzero(prime & (dq == 0))
        overlap_idx = np.flatnonzero(prime & (dq == 1))

        minus_parts.append((minus_idx + lo).astype(np.int32))
        plus_parts.append((plus_idx + lo).astype(np.int32))
        overlap_parts.append((overlap_idx + lo).astype(np.int32))

        xi = prime.astype(np.int8) - dq
        cs = np.cumsum(xi, dtype=np.int32)
        min_backlog = min(min_backlog, backlog + int(cs.min(initial=0)))
        max_backlog = max(max_backlog, backlog + int(cs.max(initial=0)))
        backlog += int(cs[-1])
        prev_q = int(floor_li[-1])

    minus = np.concatenate(minus_parts).astype(np.int64)
    plus = np.concatenate(plus_parts).astype(np.int64)
    overlap = np.concatenate(overlap_parts).astype(np.int64)

    if max_backlog >= 0:
        raise RuntimeError(
            f"backlog reached {max_backlog}; rank-pairing shortcut is invalid"
        )

    # The observed backlog starts negative and never reaches zero.  The first
    # -d0 prime-only events repay deficit inherited from before N0.  Thereafter
    # monotone/FIFO matching is rank matching.
    skip = -d0
    pairs = min(len(minus), len(plus) - skip)
    birth = minus[:pairs]
    death = plus[skip : skip + pairs]

    if np.any(death < birth):
        raise RuntimeError("rank pairing produced a negative relocation delay")

    delay = death - birth
    # This is deliberately labeled a square-root-bin statistic.  Exact
    # half-open square blocks differ at perfect-square event locations.
    birth_bin = np.floor(np.sqrt(birth)).astype(np.int64)
    death_bin = np.floor(np.sqrt(death)).astype(np.int64)
    bin_gap = death_bin - birth_bin

    event_pos = np.concatenate([minus, plus])
    event_sign = np.concatenate(
        [-np.ones(len(minus), dtype=np.int8), np.ones(len(plus), dtype=np.int8)]
    )
    order = np.argsort(event_pos, kind="mergesort")
    event_sign = event_sign[order]
    bounds = np.r_[0, np.flatnonzero(event_sign[1:] != event_sign[:-1]) + 1, len(event_sign)]
    run_lengths = np.diff(bounds)
    run_signs = event_sign[bounds[:-1]]

    return {
        "range": {"n0": N0, "N": N},
        "start_backlog": int(d0),
        "final_backlog": int(backlog),
        "min_backlog": int(min_backlog),
        "max_backlog": int(max_backlog),
        "near_integer_rechecks": int(near_total),
        "counts": {
            "minus_floor_only": int(len(minus)),
            "plus_prime_only": int(len(plus)),
            "overlap": int(len(overlap)),
        },
        "overlap_frac_prime": float(len(overlap) / (len(overlap) + len(plus))),
        "mismatch_frac_union": float(
            (len(minus) + len(plus)) / (len(minus) + len(plus) + len(overlap))
        ),
        "pairing": {
            "pairs": int(pairs),
            "unmatched_minus_end": int(len(minus) - pairs),
            "delay_quantiles": quantiles(delay),
            "mean_delay": float(delay.mean()),
            "max_delay": int(delay.max()),
            "same_bin_frac": float(np.mean(bin_gap == 0)),
            "within1_bin_frac": float(np.mean(bin_gap <= 1)),
            "within2_bin_frac": float(np.mean(bin_gap <= 2)),
            "max_bin_gap": int(bin_gap.max()),
            "bin_gap_counts": {
                str(int(k)): int(v)
                for k, v in zip(*np.unique(bin_gap, return_counts=True))
            },
        },
        "event_runs": {
            "minus_max": int(run_lengths[run_signs == -1].max()),
            "plus_max": int(run_lengths[run_signs == 1].max()),
            "minus_p99": float(np.quantile(run_lengths[run_signs == -1], 0.99)),
            "plus_p99": float(np.quantile(run_lengths[run_signs == 1], 0.99)),
        },
    }


def mine_square_blocks(is_prime: np.ndarray) -> dict:
    square = np.arange(R0, RMAX + 1, dtype=np.int64) ** 2
    floor_li, _ = robust_floor_li2(square)

    pi_square = np.zeros(len(square), dtype=np.int64)
    running = 0
    previous = 0
    for i, endpoint in enumerate(square):
        running += int(np.count_nonzero(is_prime[previous + 1 : endpoint + 1]))
        pi_square[i] = running
        previous = int(endpoint)

    R = np.arange(R0, RMAX, dtype=np.int64)
    prime_supply = np.diff(pi_square)
    floor_supply = np.diff(floor_li)
    delta = prime_supply - floor_supply
    E = pi_square[:-1] - floor_li[:-1]
    E_next = pi_square[1:] - floor_li[1:]

    if not np.array_equal(E_next, E + delta):
        raise RuntimeError("square-block backlog recurrence failed")

    diag = delta.astype(float) ** 2
    cross = 2 * E.astype(float) * delta
    step = diag + cross

    ranges = [(56, 100), (100, 200), (200, 500), (500, 1000),
              (1000, 2000), (2000, 5000), (5000, 10000)]
    range_rows = []
    for lo, hi in ranges:
        mask = (R >= lo) & (R < hi)
        range_rows.append(
            {
                "Rlo": lo,
                "Rhi": hi,
                "n": int(mask.sum()),
                "E_min": int(E[mask].min()),
                "E_max": int(E[mask].max()),
                "mean_delta": float(delta[mask].mean()),
                "lag1_delta": corr(delta[mask][:-1], delta[mask][1:]),
                "corr_E_delta": corr(E[mask], delta[mask]),
                "sum_diag": float(diag[mask].sum()),
                "sum_cross": float(cross[mask].sum()),
                "sum_step": float(step[mask].sum()),
                "cross_cancel_diag": float(-cross[mask].sum() / diag[mask].sum()),
                "net_over_gross_step": float(
                    abs(step[mask].sum()) / np.abs(step[mask]).sum()
                ),
            }
        )

    tail = R >= 1000
    Rt = R[tail].astype(float)
    Et = E[tail].astype(float)
    dt = delta[tail].astype(float)

    X = np.column_stack([np.ones(len(Et)), Et, Rt])
    beta = np.linalg.lstsq(X, dt, rcond=None)[0]
    pred = X @ beta
    r2 = float(
        1 - np.sum((dt - pred) ** 2) / np.sum((dt - dt.mean()) ** 2)
    )

    feedback_rows = []
    for lo in range(1000, 10000, 1000):
        hi = lo + 1000
        mask = (R >= lo) & (R < hi)
        ee = E[mask]
        dd = delta[mask]
        q1, q3 = np.quantile(ee, [0.25, 0.75])
        deep = dd[ee <= q1]
        shallow = dd[ee >= q3]
        feedback_rows.append(
            {
                "Rlo": lo,
                "Rhi": hi,
                "deep_mean_delta": float(deep.mean()),
                "shallow_mean_delta": float(shallow.mean()),
                "difference": float(deep.mean() - shallow.mean()),
            }
        )

    return {
        "global": {
            "E0": int(E[0]),
            "E_final": int(E_next[-1]),
            "E_min": int(E.min()),
            "E_max": int(E.max()),
            "delta_min": int(delta.min()),
            "delta_max": int(delta.max()),
            "corr_E_delta": corr(E, delta),
            "lag1_delta": corr(delta[:-1], delta[1:]),
            "sum_diag": float(diag.sum()),
            "sum_cross": float(cross.sum()),
            "sum_step": float(step.sum()),
            "cross_cancel_diag": float(-cross.sum() / diag.sum()),
            "net_over_gross_step": float(abs(step.sum()) / np.abs(step).sum()),
            "max_RH_ratio": float(
                np.max(np.abs(E_next) / ((R + 1) * np.log(R + 1)))
            ),
            "final_RH_ratio": float(
                abs(E_next[-1]) / (RMAX * np.log(RMAX))
            ),
        },
        "ranges": range_rows,
        "feedback_regression_E_R": {
            "intercept": float(beta[0]),
            "beta_E": float(beta[1]),
            "beta_R": float(beta[2]),
            "r2": r2,
        },
        "fixed_scale_quartile_feedback": feedback_rows,
    }


def main() -> None:
    out_dir = Path(__file__).resolve().parent
    is_prime = prime_sieve(N)

    result = {
        "transport": mine_transport(is_prime),
        "square_blocks": mine_square_blocks(is_prime),
        "scope_warning": (
            "All relocation lifetimes and feedback statistics are finite diagnostics. "
            "The square-root-bin gap uses floor(sqrt(n)); exact half-open square blocks "
            "differ at perfect-square event sites."
        ),
    }

    out = out_dir / "results_1e8.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
