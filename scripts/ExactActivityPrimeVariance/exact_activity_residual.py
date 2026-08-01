#!/usr/bin/env python3
"""Corrected exact-activity prime-variance diagnostics.

This script replaces the historical midpoint-lifetime interpretation added in
PR #99. It keeps the exact packet-start identity intact but evaluates the prime
model on the exact active interval at each time t and odd cofactor c:

    L(t,c) = max(t+2, ceil((t+1)^2/(2c)))
    U(t,c) = floor(((t+1)^2-1)/c).

The script provides two diagnostics:

1. `split`: decompose the historical midpoint residual into the pure prime-count
   discrepancy plus the deterministic lifetime mismatch;
2. `scaling`: measure dyadic-band sign-blind and signed energies of the pure
   prime discrepancy across scales.

All reported asymptotic behavior is finite numerical evidence only.
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
def mobius_sieve(n: int) -> np.ndarray:
    mu = np.zeros(n + 1, np.int8)
    lp = np.zeros(n + 1, np.int32)
    primes = np.empty(n // 2 + 10, np.int32)
    pc = 0
    mu[1] = 1
    for i in range(2, n + 1):
        if lp[i] == 0:
            lp[i] = i
            primes[pc] = i
            pc += 1
            mu[i] = -1
        for j in range(pc):
            p = primes[j]
            v = i * p
            if v > n:
                break
            lp[v] = p
            if p == lp[i]:
                mu[v] = 0
                break
            mu[v] = -mu[i]
    return mu


def prime_pi(n: int) -> np.ndarray:
    is_prime = np.ones(n + 1, dtype=np.bool_)
    is_prime[:2] = False
    for p in range(2, math.isqrt(n) + 1):
        if is_prime[p]:
            is_prime[p * p : n + 1 : p] = False
    return np.cumsum(is_prime, dtype=np.int32)


@njit(cache=True)
def li_interval(a: float, b: float) -> float:
    """Five-point Gauss-Legendre approximation of integral_a^b dq/log(q)."""
    mid = 0.5 * (a + b)
    half = 0.5 * (b - a)
    x1 = 0.5384693101056831
    x2 = 0.9061798459386640
    total = 0.5688888888888889 / math.log(mid)
    total += 0.4786286704993665 * (
        1.0 / math.log(mid - half * x1) + 1.0 / math.log(mid + half * x1)
    )
    total += 0.2369268850561891 * (
        1.0 / math.log(mid - half * x2) + 1.0 / math.log(mid + half * x2)
    )
    return half * total


@njit(cache=True)
def build_cofactors(mu: np.ndarray, lo: int, hi: int):
    count = 0
    for c in range(lo | 1, hi, 2):
        if mu[c] != 0:
            count += 1
    cs = np.empty(count, np.int32)
    signs = np.empty(count, np.int8)
    k = 0
    for c in range(lo | 1, hi, 2):
        if mu[c] != 0:
            cs[k] = c
            signs[k] = -mu[c]
            k += 1
    return cs, signs


@njit(cache=True)
def exact_and_li_activity(pi: np.ndarray, cs: np.ndarray, signs: np.ndarray, n: int):
    exact = np.zeros((n, len(cs)), np.float64)
    model = np.zeros_like(exact)
    for it in range(n):
        t = n + it
        tp = t + 1
        tp2 = tp * tp
        for j in range(len(cs)):
            c = int(cs[j])
            lo = (tp2 + 2 * c - 1) // (2 * c)
            if lo < t + 2:
                lo = t + 2
            hi = (tp2 - 1) // c
            if hi < lo:
                continue
            count = int(pi[hi]) - int(pi[lo - 1])
            weight = li_interval(lo - 0.5, hi + 0.5)
            exact[it, j] = signs[j] * count
            model[it, j] = signs[j] * weight
    return exact, model


@njit(cache=True)
def midpoint_model(cs: np.ndarray, signs: np.ndarray, n: int):
    nmax = 2 * n
    diff = np.zeros((len(cs), nmax + 2), np.float64)
    for j in range(len(cs)):
        c = int(cs[j])
        sign = int(signs[j])
        n0 = c if c > 2 else 2
        for birth in range(n0, nmax + 1):
            lower = float(birth * birth) / c
            if lower < birth + 2.0:
                lower = birth + 2.0
            upper = float((birth + 1) * (birth + 1) - 1) / c
            if upper < lower:
                continue
            weight = li_interval(lower - 0.5, upper + 0.5)
            qmid = 0.5 * (lower + upper)
            mmid = c * qmid
            end = math.floor(math.sqrt(2.0 * mmid))
            transition = math.floor(qmid - 1.0)
            if transition < end:
                end = transition
            if end > nmax + 1:
                end = nmax + 1
            if end <= birth:
                continue
            diff[j, birth] += sign * weight
            diff[j, end] -= sign * weight
    out = np.zeros((n, len(cs)), np.float64)
    for j in range(len(cs)):
        acc = 0.0
        for t in range(nmax + 1):
            acc += diff[j, t]
            if n <= t < 2 * n:
                out[t - n, j] = acc
    return out


def component_stats(matrix: np.ndarray, n: int) -> dict:
    total = matrix.sum(axis=1)
    diagonal = float(np.sum(matrix * matrix) / n**3)
    energy = float(np.dot(total, total) / n**3)
    return {
        "diagonal_over_HN2": diagonal,
        "signed_energy_over_HN2": energy,
        "energy_over_diagonal": energy / diagonal if diagonal else None,
    }


def run_split(n: int, lo: int, hi: int) -> dict:
    start = time.time()
    mu = mobius_sieve(2 * n + 2)
    cs, signs = build_cofactors(mu, lo, hi)
    qmax = ((2 * n) * (2 * n) - 1) // lo + 10
    pi = prime_pi(qmax)
    exact, active_model = exact_and_li_activity(pi, cs, signs, n)
    midpoint = midpoint_model(cs, signs, n)
    pure_prime = exact - active_model
    lifetime_mismatch = active_model - midpoint
    historical_residual = exact - midpoint
    identity = historical_residual - (pure_prime + lifetime_mismatch)
    return {
        "N": n,
        "band": [lo, hi],
        "active_cofactors": int(len(cs)),
        "qmax": int(qmax),
        "identity_error": float(np.max(np.abs(identity))),
        "summed_identity_error": float(
            np.max(
                np.abs(
                    historical_residual.sum(axis=1)
                    - pure_prime.sum(axis=1)
                    - lifetime_mismatch.sum(axis=1)
                )
            )
        ),
        "historical_midpoint_residual": component_stats(historical_residual, n),
        "pure_prime_discrepancy": component_stats(pure_prime, n),
        "deterministic_lifetime_mismatch": component_stats(lifetime_mismatch, n),
        "runtime_seconds": time.time() - start,
    }


@njit(cache=True)
def sampled_band_stats(
    pi: np.ndarray,
    cs: np.ndarray,
    signs: np.ndarray,
    times: np.ndarray,
    n: int,
):
    diagonal = np.zeros(len(times), np.float64)
    signed = np.zeros(len(times), np.float64)
    for it in range(len(times)):
        t = int(times[it])
        tp = t + 1
        tp2 = tp * tp
        d = 0.0
        s = 0.0
        for j in range(len(cs)):
            c = int(cs[j])
            lo = (tp2 + 2 * c - 1) // (2 * c)
            if lo < t + 2:
                lo = t + 2
            hi = (tp2 - 1) // c
            if hi < lo:
                continue
            count = int(pi[hi]) - int(pi[lo - 1])
            weight = li_interval(lo - 0.5, hi + 0.5)
            discrepancy = count - weight
            d += discrepancy * discrepancy
            s += signs[j] * discrepancy
        diagonal[it] = d / (n * n)
        signed[it] = s * s / (n * n)
    return diagonal, signed


def dyadic_bands(n: int):
    cmin = max(1, n // 64)
    cmax = 2 * n + 1
    p = 1
    while 2 * p <= cmin:
        p *= 2
    out = []
    while p < cmax:
        lo = max(p, cmin)
        hi = min(2 * p, cmax)
        if lo < hi:
            out.append((lo, hi))
        p *= 2
    return out


def sample_times(n: int, count: int) -> np.ndarray:
    if n <= count:
        return np.arange(n, 2 * n, dtype=np.int32)
    return np.unique(np.linspace(n, 2 * n - 1, count, dtype=np.int32))


def run_scaling(scales: list[int], samples: int) -> dict:
    start = time.time()
    max_n = max(scales)
    mu = mobius_sieve(2 * max_n + 2)
    qmax = max(((2 * n) * (2 * n) - 1) // max(1, n // 64) for n in scales) + 10
    pi = prime_pi(qmax)
    results = []
    for n in scales:
        times = sample_times(n, samples)
        bands = []
        for lo, hi in dyadic_bands(n):
            cs, signs = build_cofactors(mu, lo, hi)
            diagonal, signed = sampled_band_stats(pi, cs, signs, times, n)
            bands.append(
                {
                    "band": [lo, hi],
                    "active_cofactors": int(len(cs)),
                    "samples": int(len(times)),
                    "diagonal_over_HN2": float(np.mean(diagonal)),
                    "signed_energy_over_HN2": float(np.mean(signed)),
                }
            )
        top = max(bands, key=lambda row: row["diagonal_over_HN2"])
        results.append({"N": n, "top_band": top, "bands": bands})
    ns = np.array([row["N"] for row in results], dtype=float)
    ds = np.array(
        [row["top_band"]["diagonal_over_HN2"] for row in results], dtype=float
    )
    power = np.polyfit(np.log(ns), np.log(ds), 1)
    polylog = np.polyfit(np.log(np.log(ns)), np.log(ds), 1)
    return {
        "qmax": int(qmax),
        "scales": results,
        "power_slope": float(power[0]),
        "polylog_exponent": float(polylog[0]),
        "power_log_rss": float(
            np.sum((np.log(ds) - np.polyval(power, np.log(ns))) ** 2)
        ),
        "polylog_log_rss": float(
            np.sum((np.log(ds) - np.polyval(polylog, np.log(np.log(ns)))) ** 2)
        ),
        "runtime_seconds": time.time() - start,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["split", "scaling", "all"], default="all")
    parser.add_argument("--split-n", type=int, default=5000)
    parser.add_argument("--split-lo", type=int, default=2048)
    parser.add_argument("--split-hi", type=int, default=4096)
    parser.add_argument(
        "--scales",
        type=str,
        default="1000,2000,5000,10000,20000,50000,100000,200000",
    )
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output: dict = {
        "classification": {
            "exact": "finite activity intervals and decomposition identities",
            "finite_evidence": "scaling fits over the requested finite range",
            "not_claimed": "uniform asymptotic estimate or RH implication",
        }
    }
    if args.mode in ("split", "all"):
        output["split"] = run_split(args.split_n, args.split_lo, args.split_hi)
    if args.mode in ("scaling", "all"):
        scales = [int(item) for item in args.scales.split(",") if item.strip()]
        output["scaling"] = run_scaling(scales, args.samples)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
