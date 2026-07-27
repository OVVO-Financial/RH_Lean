#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.special import expi


def mobius_linear(n: int) -> np.ndarray:
    mu = np.zeros(n + 1, dtype=np.int8)
    if n >= 1:
        mu[1] = 1
    primes = []
    composite = np.zeros(n + 1, dtype=np.bool_)
    for i in range(2, n + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            x = i * p
            if x > n:
                break
            composite[x] = True
            if i % p == 0:
                mu[x] = 0
                break
            mu[x] = -mu[i]
    return mu


def prime_pi_table(n: int) -> np.ndarray:
    is_prime = np.ones(n + 1, dtype=np.bool_)
    is_prime[:2] = False
    for p in range(2, math.isqrt(n) + 1):
        if is_prime[p]:
            is_prime[p * p : n + 1 : p] = False
    return np.cumsum(is_prime, dtype=np.int32)


def li_table(n: int) -> np.ndarray:
    out = np.zeros(n + 1, dtype=np.float64)
    x = np.arange(2, n + 1, dtype=np.float64)
    out[2:] = expi(np.log(x))
    return out


def exact_pair_matrix(
    N: int,
    H: int,
    c_lo: int,
    c_hi: int,
    pi: np.ndarray,
    li: np.ndarray,
    mu: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    # Fixed odd squarefree parent support; rows automatically zero when c > t/2.
    c = np.arange(max(1, c_lo), c_hi, dtype=np.int64)
    c = c[(c & 1) == 1]
    c = c[mu[c] != 0]
    A = np.zeros((H, c.size), dtype=np.float64)
    K = np.zeros_like(A)
    J = np.zeros_like(A)

    for r, t in enumerate(range(N, N + H)):
        active = c <= t // 2
        if not np.any(active):
            continue
        ca = c[active]
        S = (t + 1) ** 2
        X = S - 1

        L1 = np.maximum(t + 2, (S + 2 * ca - 1) // (2 * ca))
        U1 = X // ca
        L2 = np.maximum(t + 2, (S + 4 * ca - 1) // (4 * ca))
        U2 = X // (2 * ca)

        d1 = (pi[U1] - pi[L1 - 1]).astype(np.float64) - (li[U1] - li[L1 - 1])
        d2 = (pi[U2] - pi[L2 - 1]).astype(np.float64) - (li[U2] - li[L2 - 1])
        pair = d1 - d2

        l1 = (U1 - L1 + 1).astype(np.float64)
        l2 = (U2 - L2 + 1).astype(np.float64)
        # Exact K/J split from the previous experiment.
        A1 = d1 / l1
        A2 = d2 / l2
        k = (l1 - l2) * A2
        j = l1 * (A1 - A2)

        A[r, active] = pair
        K[r, active] = k
        J[r, active] = j
    return c, A, np.stack([K, J], axis=0)


def energy_metrics(A: np.ndarray, signs: np.ndarray, rng: np.random.Generator, reps: int) -> dict[str, float]:
    actual_profile = A @ signs.astype(np.float64)
    actual = float(actual_profile @ actual_profile)
    diagonal = float(np.sum(A * A))
    allplus_profile = A.sum(axis=1)
    allplus = float(allplus_profile @ allplus_profile)
    l1_upper = float(np.sum(np.sum(np.abs(A), axis=1) ** 2))

    if A.shape[1] == 0 or diagonal == 0:
        return {
            'actual_energy': actual,
            'diagonal_energy': diagonal,
            'actual_over_random_expectation': float('nan'),
            'allplus_over_random_expectation': float('nan'),
            'l1_upper_over_random_expectation': float('nan'),
            'random_mean_ratio': float('nan'),
            'random_sd_ratio': float('nan'),
            'actual_random_z': float('nan'),
            'actual_random_percentile': float('nan'),
            'offdiag_fraction': float('nan'),
            'profile_mean_fraction': float('nan'),
        }

    rand_signs = rng.choice(np.array([-1.0, 1.0]), size=(A.shape[1], reps))
    rand_profiles = A @ rand_signs
    rand_energy = np.sum(rand_profiles * rand_profiles, axis=0)
    rand_ratio = rand_energy / diagonal
    sd = float(np.std(rand_ratio, ddof=1)) if reps > 1 else float('nan')
    actual_ratio = actual / diagonal
    percentile = float((np.sum(rand_ratio <= actual_ratio) + 0.5) / (reps + 1.0))

    centered = actual_profile - actual_profile.mean()
    centered_energy = float(centered @ centered)
    mean_energy = float(A.shape[0] * actual_profile.mean() ** 2)

    return {
        'actual_energy': actual,
        'diagonal_energy': diagonal,
        'actual_over_random_expectation': actual_ratio,
        'allplus_over_random_expectation': allplus / diagonal,
        'l1_upper_over_random_expectation': l1_upper / diagonal,
        'random_mean_ratio': float(np.mean(rand_ratio)),
        'random_sd_ratio': sd,
        'actual_random_z': (actual_ratio - float(np.mean(rand_ratio))) / sd if sd > 0 else float('nan'),
        'actual_random_percentile': percentile,
        'offdiag_fraction': (actual - diagonal) / diagonal,
        'profile_mean_fraction': mean_energy / actual if actual > 0 else float('nan'),
        'centered_energy_fraction': centered_energy / actual if actual > 0 else float('nan'),
        'actual_profile_max_abs': float(np.max(np.abs(actual_profile))),
        'actual_profile_rms': math.sqrt(actual / A.shape[0]),
    }


def analyze_one(
    scale_N: int,
    start: int,
    H: int,
    label: str,
    c_lo: int,
    c_hi: int,
    pi: np.ndarray,
    li: np.ndarray,
    mu: np.ndarray,
    rng: np.random.Generator,
    reps: int,
) -> dict[str, float | int | str]:
    c, A, KJ = exact_pair_matrix(start, H, c_lo, c_hi, pi, li, mu)
    m = energy_metrics(A, mu[c], rng, reps)

    # Internal K+J cancellation after the true Mobius recombination.
    Kprof = KJ[0] @ mu[c].astype(np.float64)
    Jprof = KJ[1] @ mu[c].astype(np.float64)
    Pprof = Kprof + Jprof
    EK = float(Kprof @ Kprof)
    EJ = float(Jprof @ Jprof)
    EP = float(Pprof @ Pprof)
    corr = float(np.corrcoef(Kprof, Jprof)[0, 1]) if H > 1 and np.std(Kprof) and np.std(Jprof) else float('nan')

    # Column coherence diagnostics. A high effective rank is preferable to a hidden rank-one artifact.
    frob2 = float(np.sum(A * A))
    # Compute only singular values of HxM; H is deliberately modest.
    svals = np.linalg.svd(A, compute_uv=False)
    spec2 = float(svals[0] ** 2) if svals.size else 0.0
    effective_rank = (float(np.sum(svals * svals)) ** 2 / float(np.sum(svals ** 4))) if np.any(svals) else float('nan')

    return {
        'scale_N': scale_N,
        'window_start': start,
        'H': H,
        'band': label,
        'c_lo': c_lo,
        'c_hi': c_hi,
        'column_count': int(c.size),
        **m,
        'KJ_survival_ratio': EP / (EK + EJ) if EK + EJ > 0 else float('nan'),
        'KJ_corr': corr,
        'top_singular_energy_share': spec2 / frob2 if frob2 > 0 else float('nan'),
        'effective_rank': effective_rank,
        'pair_split_max_error': float(np.max(np.abs(A - (KJ[0] + KJ[1])))) if A.size else 0.0,
    }


def fit_trends(df: pd.DataFrame) -> pd.DataFrame:
    rows = []
    for (band, window_id), g in df.groupby(['band', 'window_id']):
        g = g.replace([np.inf, -np.inf], np.nan).dropna(subset=['actual_over_random_expectation'])
        if len(g) < 3:
            continue
        x = np.log(g['scale_N'].to_numpy(float))
        y = np.log(g['actual_over_random_expectation'].to_numpy(float))
        slope, intercept = np.polyfit(x, y, 1)
        # Also test a log-power trend ratio ~ (log N)^b.
        xl = np.log(np.log(g['scale_N'].to_numpy(float)))
        bslope, bintercept = np.polyfit(xl, y, 1)
        rows.append({
            'band': band,
            'window_id': int(window_id),
            'power_slope': float(slope),
            'power_intercept': float(intercept),
            'log_power_slope': float(bslope),
            'n_points': int(len(g)),
            'ratio_first': float(g.sort_values('scale_N').iloc[0]['actual_over_random_expectation']),
            'ratio_last': float(g.sort_values('scale_N').iloc[-1]['actual_over_random_expectation']),
        })
    return pd.DataFrame(rows)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', type=Path, default=Path(__file__).resolve().parent / 'results')
    ap.add_argument('--random-reps', type=int, default=48)
    ap.add_argument('--seed', type=int, default=20260726)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    scales = [4000, 8000, 16000, 32000, 64000, 128000, 200000]
    # Consecutive windows: enough to test stability while keeping exact matrix calculations tractable.
    H_by_N = {N: min(384, max(160, int(round(0.04 * N)))) for N in scales}
    window_ids = [0, 1]
    band_defs = [
        ('deep_1_64', 1/64, 1/32),
        ('deep_1_32', 1/32, 1/16),
        ('deep_1_16', 1/16, 1/8),
        ('deep_1_8', 1/8, 1/4),
        ('transition_1_4', 1/4, 1/2),
    ]

    max_start = max(N + max(window_ids) * H_by_N[N] for N in scales)
    max_t = max_start + max(H_by_N.values()) - 1
    # Smallest c occurs at N=4000, but the largest U occurs at largest t / smallest relative c for its scale.
    max_u = 0
    max_c_needed = 0
    for N in scales:
        H = H_by_N[N]
        for wid in window_ids:
            start = N + wid * H
            t = start + H - 1
            cmin = max(1, int(math.floor(N / 64)))
            u = ((t + 1) ** 2 - 1) // cmin
            max_u = max(max_u, u)
            max_c_needed = max(max_c_needed, int(math.ceil(N / 2)) + 2)

    print(json.dumps({'max_t': max_t, 'max_u': max_u, 'max_c_needed': max_c_needed}))
    pi = prime_pi_table(max_u)
    li = li_table(max_u)
    mu = mobius_linear(max_c_needed * 2 + 10)
    rng = np.random.default_rng(args.seed)

    rows = []
    for N in scales:
        H = H_by_N[N]
        for wid in window_ids:
            start = N + wid * H
            for label, lo_frac, hi_frac in band_defs:
                c_lo = max(1, int(math.floor(N * lo_frac)))
                c_hi = max(c_lo + 1, int(math.ceil(N * hi_frac)))
                row = analyze_one(N, start, H, label, c_lo, c_hi, pi, li, mu, rng, args.random_reps)
                row['window_id'] = wid
                rows.append(row)
                print(f"done N={N} wid={wid} band={label} ratio={row['actual_over_random_expectation']:.4g} z={row['actual_random_z']:.2f}")

            # Aggregate all tested paired bands. This keeps one copy of every parent in [N/64,N/2).
            c_lo = max(1, int(math.floor(N / 64)))
            c_hi = max(c_lo + 1, int(math.ceil(N / 2)))
            row = analyze_one(N, start, H, 'aggregate_1_64_to_1_2', c_lo, c_hi, pi, li, mu, rng, args.random_reps)
            row['window_id'] = wid
            rows.append(row)
            print(f"done N={N} wid={wid} band=aggregate ratio={row['actual_over_random_expectation']:.4g} z={row['actual_random_z']:.2f}")

    df = pd.DataFrame(rows)
    df.to_csv(args.outdir / 'kj_falsification_grid.csv', index=False)
    trends = fit_trends(df)
    trends.to_csv(args.outdir / 'kj_scale_trends.csv', index=False)

    summary = df.groupby('band').agg(
        n=('actual_over_random_expectation', 'size'),
        median_actual_random_ratio=('actual_over_random_expectation', 'median'),
        max_actual_random_ratio=('actual_over_random_expectation', 'max'),
        min_actual_random_ratio=('actual_over_random_expectation', 'min'),
        median_random_percentile=('actual_random_percentile', 'median'),
        fraction_below_random_expectation=('actual_over_random_expectation', lambda x: float(np.mean(x < 1))),
        fraction_below_random_10pct=('actual_random_percentile', lambda x: float(np.mean(x <= 0.10))),
        median_KJ_survival=('KJ_survival_ratio', 'median'),
        median_KJ_corr=('KJ_corr', 'median'),
        median_top_singular_share=('top_singular_energy_share', 'median'),
        median_effective_rank=('effective_rank', 'median'),
    ).reset_index()
    summary.to_csv(args.outdir / 'kj_falsification_summary.csv', index=False)

    # Objective verdict rules, stated before reading the output.
    agg = df[df.band == 'aggregate_1_64_to_1_2']
    agg_trends = trends[trends.band == 'aggregate_1_64_to_1_2']
    evidence = {
        'aggregate_all_ratios_below_one': bool(np.all(agg.actual_over_random_expectation < 1)),
        'aggregate_median_ratio': float(agg.actual_over_random_expectation.median()),
        'aggregate_worst_ratio': float(agg.actual_over_random_expectation.max()),
        'aggregate_median_percentile': float(agg.actual_random_percentile.median()),
        'aggregate_power_slopes': agg_trends[['window_id','power_slope']].to_dict(orient='records'),
        'all_pair_identities_exact_to_1e_9': bool(df.pair_split_max_error.max() < 1e-9),
    }
    # Continue only if the true signs consistently beat random and do not worsen with scale in both moving windows.
    slopes_ok = len(agg_trends) == len(window_ids) and bool(np.all(agg_trends.power_slope <= 0.05))
    evidence['predeclared_continue_gate'] = bool(
        evidence['aggregate_all_ratios_below_one']
        and evidence['aggregate_median_ratio'] <= 0.75
        and evidence['aggregate_median_percentile'] <= 0.15
        and slopes_ok
    )
    evidence['interpretation'] = (
        'PASS: exact Mobius/dyadic structure shows stable better-than-random cancellation; proceed to derive Type-I/II bounds.'
        if evidence['predeclared_continue_gate'] else
        'FAIL: no stable scale-uniform better-than-random cancellation under the predeclared gate; the current analytic route should be killed or materially redesigned.'
    )
    (args.outdir / 'verdict.json').write_text(json.dumps(evidence, indent=2))

    print('\nSUMMARY')
    print(summary.to_string(index=False))
    print('\nTRENDS')
    print(trends.to_string(index=False))
    print('\nVERDICT')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
