#!/usr/bin/env python3
"""Prime-density packet-operator reproducibility test.

This script verifies three claims for the exact odd-annulus/dyadic-packet model:

1. packet starts admit an exact cofactor/short-prime-interval identity;
2. a no-fit local prime-density weight predicts the drifting signed packet bias;
3. preserving the cofactor-dependent packet lifetime yields an exact decomposition

       S = (L + H_hat) + (H - H_hat)

   whose two modeled pieces are tested on the H*N^2 local-energy scale.

The output is finite numerical evidence only. It does not assert either required
uniform analytic estimate.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
from numba import njit


@njit(cache=True)
def linear_sieve_mu_lpf(n: int):
    spf = np.zeros(n + 1, dtype=np.int32)
    lpf = np.ones(n + 1, dtype=np.int32)
    mu = np.zeros(n + 1, dtype=np.int8)
    primes = np.empty(max(16, n // 8), dtype=np.int32)
    pc = 0
    mu[1] = 1
    lpf[1] = 1
    for i in range(2, n + 1):
        if spf[i] == 0:
            spf[i] = i
            lpf[i] = i
            primes[pc] = i
            pc += 1
            mu[i] = -1
        j = 0
        while j < pc:
            p = primes[j]
            v = p * i
            if v > n:
                break
            spf[v] = p
            lpf[v] = lpf[i] if lpf[i] > p else p
            if p == spf[i]:
                mu[v] = 0
                break
            mu[v] = -mu[i]
            j += 1
    return mu, lpf


@njit(cache=True)
def build_annulus_and_high(mu, lpf, nmax: int):
    limit = (nmax + 1) * (nmax + 1) - 1
    diff_d = np.zeros(nmax + 2, dtype=np.int64)
    diff_h = np.zeros(nmax + 2, dtype=np.int64)
    starts = np.zeros(nmax + 1, dtype=np.int64)
    counts = np.zeros(nmax + 1, dtype=np.int64)
    for m in range(1, limit + 1, 2):
        w = int(mu[m])
        if w == 0:
            continue
        birth = int(math.sqrt(m))
        while (birth + 1) * (birth + 1) <= m:
            birth += 1
        while birth * birth > m:
            birth -= 1
        if birth > nmax:
            continue
        end_ann = int(math.sqrt(2 * m))
        while (end_ann + 1) * (end_ann + 1) <= 2 * m:
            end_ann += 1
        while end_ann * end_ann > 2 * m:
            end_ann -= 1
        if end_ann > nmax + 1:
            end_ann = nmax + 1
        if birth < end_ann:
            diff_d[birth] += w
            diff_d[end_ann] -= w
        q = int(lpf[m])
        end_high = end_ann if end_ann < q - 1 else q - 1
        if birth < end_high:
            diff_h[birth] += w
            diff_h[end_high] -= w
            starts[birth] += w
            counts[birth] += 1
    d = np.cumsum(diff_d)[: nmax + 1]
    h = np.cumsum(diff_h)[: nmax + 1]
    return d, d - h, h, starts, counts


@njit(cache=True)
def prime_prefix(lpf):
    pi = np.zeros(len(lpf), dtype=np.int32)
    acc = 0
    for x in range(2, len(lpf)):
        if lpf[x] == x:
            acc += 1
        pi[x] = acc
    return pi


@njit(cache=True)
def exact_cofactor_starts(mu_small, pi, nmax: int):
    signed = np.zeros(nmax + 1, dtype=np.int64)
    count = np.zeros(nmax + 1, dtype=np.int64)
    for n in range(2, nmax + 1):
        n2 = n * n
        top = (n + 1) * (n + 1) - 1
        for c in range(1, n + 1, 2):
            muc = int(mu_small[c])
            if muc == 0:
                continue
            upper = top // c
            lower_prime = (n2 + c - 1) // c
            if lower_prime < n + 2:
                lower_prime = n + 2
            lower = lower_prime - 1
            if upper <= lower:
                continue
            weight = int(pi[upper] - pi[lower])
            signed[n] += -muc * weight
            count[n] += weight
    return signed, count


@njit(cache=True)
def pnt_start_arrays(mu_small, nmax: int):
    signed = np.zeros(nmax + 1, dtype=np.float64)
    count = np.zeros(nmax + 1, dtype=np.float64)
    for n in range(2, nmax + 1):
        n2 = float(n * n)
        top = float((n + 1) * (n + 1) - 1)
        for c in range(1, n + 1, 2):
            muc = int(mu_small[c])
            if muc == 0:
                continue
            lo = n2 / c
            if lo < n + 1.0:
                lo = n + 1.0
            hi = top / c
            if hi <= lo:
                continue
            midpoint = math.sqrt(lo * hi)
            if midpoint <= 2.0:
                continue
            weight = (hi - lo) / math.log(midpoint)
            signed[n] += -muc * weight
            count[n] += weight
    return signed, count


@njit(cache=True)
def pnt_high_process(mu_small, nmax: int):
    diff_signed = np.zeros(nmax + 2, dtype=np.float64)
    diff_count = np.zeros(nmax + 2, dtype=np.float64)
    for n in range(2, nmax + 1):
        n2 = float(n * n)
        top = float((n + 1) * (n + 1) - 1)
        for c in range(1, n + 1, 2):
            muc = int(mu_small[c])
            if muc == 0:
                continue
            lo = n2 / c
            if lo < n + 2.0:
                lo = n + 2.0
            hi = top / c
            if hi < lo:
                continue
            width = hi - lo + 1.0
            qmid = 0.5 * (lo + hi)
            if qmid <= 2.0:
                continue
            weight = width / math.log(qmid)
            mmid = c * qmid
            end = math.floor(math.sqrt(2.0 * mmid))
            transition = math.floor(qmid - 1.0)
            if transition < end:
                end = transition
            if end > nmax + 1:
                end = nmax + 1
            if end > n:
                diff_signed[n] += -muc * weight
                diff_signed[end] -= -muc * weight
                diff_count[n] += weight
                diff_count[end] -= weight
    return np.cumsum(diff_signed)[: nmax + 1], np.cumsum(diff_count)[: nmax + 1]


def energy(x: np.ndarray, lo: int, hi: int) -> float:
    v = x[lo:hi].astype(np.float64)
    return float(np.dot(v, v) / ((hi - lo) * lo * lo))


def slope(rows, key: str) -> float:
    x = np.log(np.asarray([r["window"][0] for r in rows], dtype=np.float64))
    y = np.log(np.asarray([r[key] for r in rows], dtype=np.float64))
    return float(np.polyfit(x, y, 1)[0])


def run(nmax: int, identity_nmax: int):
    started = time.time()
    limit = (nmax + 1) ** 2 - 1
    mu, lpf = linear_sieve_mu_lpf(limit)
    d, low, high, starts, counts = build_annulus_and_high(mu, lpf, nmax)

    prefix = np.cumsum(mu.astype(np.int64))
    endpoints = (np.arange(nmax + 1, dtype=np.int64) + 1) ** 2 - 1
    square_prefix = prefix[endpoints]

    identity_nmax = min(identity_nmax, nmax)
    pi = prime_prefix(lpf)
    exact_signed, exact_count = exact_cofactor_starts(mu[: identity_nmax + 1], pi, identity_nmax)

    pnt_starts, pnt_counts = pnt_start_arrays(mu[: nmax + 1], nmax)
    pnt_high, _ = pnt_high_process(mu[: nmax + 1], nmax)
    residual = high.astype(np.float64) - pnt_high
    complementary_main = low.astype(np.float64) + pnt_high

    windows = []
    for lo in [500, 750, 1000, 1250, 1500, 2000, 2500, 3000, 4000, 4500, 5000]:
        hi = 2 * lo
        if hi > nmax:
            continue
        exact_beta = float(np.sum(starts[lo:hi]) / np.sum(counts[lo:hi]))
        predicted_beta = float(np.sum(pnt_starts[lo:hi]) / np.sum(pnt_counts[lo:hi]))
        windows.append(
            {
                "window": [lo, hi],
                "exact_packet_bias": exact_beta,
                "predicted_packet_bias": predicted_beta,
                "packet_bias_relative_error": (predicted_beta - exact_beta) / exact_beta,
                "raw_high_energy_over_HN2": energy(high, lo, hi),
                "residual_energy_over_HN2": energy(residual, lo, hi),
                "complementary_main_energy_over_HN2": energy(complementary_main, lo, hi),
                "complete_annulus_energy_over_HN2": energy(d, lo, hi),
                "corr_high_predicted": float(np.corrcoef(high[lo:hi], pnt_high[lo:hi])[0, 1]),
                "recombination_max_error": float(
                    np.max(np.abs((complementary_main + residual - d)[lo:hi]))
                ),
            }
        )

    large = [r for r in windows if r["window"][0] >= 1000] or windows
    return {
        "classification": {
            "exact": [
                "complete odd-annulus reconstruction",
                "cofactor short-prime-interval packet-start identity",
                "modeled decomposition S=(L+H_hat)+(H-H_hat)",
            ],
            "finite_numerical_evidence_only": [
                "prime-density bias accuracy",
                "scale stability of the two modeled local energies",
            ],
            "not_claimed": [
                "uniform analytic local-energy bound",
                "Riemann Hypothesis proof",
            ],
        },
        "nmax": nmax,
        "integer_cutoff": limit,
        "runtime_seconds": time.time() - started,
        "exact_checks": {
            "annulus_vs_square_prefix_mertens_max_error": int(np.max(np.abs(d - square_prefix))),
            "identity_nmax": identity_nmax,
            "cofactor_signed_start_max_error": int(
                np.max(np.abs(exact_signed[2:] - starts[2 : identity_nmax + 1]))
            ),
            "cofactor_count_start_max_error": int(
                np.max(np.abs(exact_count[2:] - counts[2 : identity_nmax + 1]))
            ),
            "modeled_recombination_max_error": float(
                np.max(np.abs(complementary_main + residual - d))
            ),
        },
        "windows": windows,
        "summary_large_windows": {
            "median_abs_packet_bias_relative_error": float(
                np.median(np.abs([r["packet_bias_relative_error"] for r in large]))
            ),
            "max_abs_packet_bias_relative_error": float(
                np.max(np.abs([r["packet_bias_relative_error"] for r in large]))
            ),
            "min_corr_high_predicted": float(min(r["corr_high_predicted"] for r in large)),
            "residual_energy_range": [
                float(min(r["residual_energy_over_HN2"] for r in large)),
                float(max(r["residual_energy_over_HN2"] for r in large)),
            ],
            "complementary_main_energy_range": [
                float(min(r["complementary_main_energy_over_HN2"] for r in large)),
                float(max(r["complementary_main_energy_over_HN2"] for r in large)),
            ],
            "normalized_energy_loglog_slopes": {
                "raw_high": slope(large, "raw_high_energy_over_HN2"),
                "residual": slope(large, "residual_energy_over_HN2"),
                "complementary_main": slope(large, "complementary_main_energy_over_HN2"),
                "complete_annulus": slope(large, "complete_annulus_energy_over_HN2"),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=10_000)
    parser.add_argument("--identity-nmax", type=int, default=4_000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run(args.nmax, args.identity_nmax)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result["exact_checks"], indent=2))
    print(json.dumps(result["summary_large_windows"], indent=2))


if __name__ == "__main__":
    main()
