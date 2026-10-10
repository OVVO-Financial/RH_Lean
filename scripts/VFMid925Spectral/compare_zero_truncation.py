#!/usr/bin/env python3
"""EXPLORATORY genuine-factor vs finite zeta-zero square-band comparison.

A numeric experiment only; mpmath.zetazero enumerates zeros on the
critical line and is NOT a certified complete set of ALL zeta zeros.
No RH or owner-return inequality is inferred from output.
Requires: pip install mpmath

Example:
  python3 scripts/VFMid925Spectral/compare_zero_truncation.py \
    --roots 7,17,56,119 --height-factor 1 --dps 50
"""
from __future__ import annotations

import argparse
import json

try:
    import mpmath as mp
except ImportError as exc:
    raise SystemExit(
        "This optional exploration requires mpmath; it is NOT part of CI"
    ) from exc

from verify_factor_theta import least_prime_factors


def lambda_at(n: int, spf: list[int]):
    if n < 2:
        return mp.mpf(0)
    p = spf[n]
    residue = n
    while residue % p == 0:
        residue //= p
    return mp.log(p) if residue == 1 else mp.mpf(0)


def gather_critical_line_zeros(height: float, limit: int):
    zeros = []
    k = 1
    overflow = False
    while k <= limit:
        rho = mp.zetazero(k)
        if mp.im(rho) > height:
            break
        zeros.append(rho)
        k += 1
    if k > limit:
        overflow = True
    return zeros, overflow


def physical(root: int, spf: list[int]):
    a, b = root * root, (root + 1) ** 2
    q_terms = [
        mp.log(n) for n in range(a + 1, b)
        if n == spf[n]  # genuine primes; verified by the separate FTA audit
    ]
    Q = mp.fsum(q_terms)
    H = mp.fsum(
        lambda_at(n, spf) for n in range(a + 1, b)
        if n != spf[n]
    )
    P = len(q_terms)
    La, Lb = lambda_at(a, spf), lambda_at(b, spf)
    midpoint = mp.mpf(a + root) + mp.mpf("0.5")
    logmid = mp.log(midpoint)
    V = mp.mpf(2 * root + 1) / logmid
    F = mp.fsum(
        mp.mpf(2 * r + 1) /
        mp.log(mp.mpf(r * r + r) + mp.mpf("0.5"))
        for r in range(2, root)
    )
    pi = sum(1 for n in range(2, a + 1) if spf[n] == n)
    D = mp.mpf(pi) - F
    return {
        "a": a, "b": b, "Q": Q,
        "U": mp.mpf(2 * root + 1) - Q,
        "H": H, "La": La, "Lb": Lb,
        "P": P, "V": V, "position": mp.mpf(P) - Q / logmid,
        "D": D, "midlog": logmid,
    }


def evaluate(root: int, spf: list[int], zeros, height: float, k: float):
    d = physical(root, spf)
    a, b = d["a"], d["b"]
    T = height * root
    terms = [
        (mp.power(b, rho) - mp.power(a, rho)) / rho
        for rho in zeros if mp.im(rho) <= T
    ]
    z = 2 * mp.re(mp.fsum(terms))
    g = mp.log(
        (1 - mp.mpf(b) ** -2) / (1 - mp.mpf(a) ** -2)
    ) / 2
    endpoint = (d["La"] + d["Lb"]) / 2
    estimate = z + g + d["H"] + endpoint
    slack = d["D"] + k * root * mp.log(root)
    wall_step = k * (
        (root + 1) * mp.log(root + 1) - root * mp.log(root)
    )
    breach_margin = d["P"] + slack + wall_step - d["V"]
    return {
        "root": root,
        "T": T,
        "positive_height_zeros_used": len(terms),
        "actual_factor_theta_shortage_U": mp.nstr(d["U"], 24),
        "truncated_zero_sum": mp.nstr(z, 24),
        "trivial_zero_term": mp.nstr(g, 24),
        "strict_interior_prime_powers": mp.nstr(d["H"], 24),
        "both_endpoint_half_jumps": mp.nstr(endpoint, 24),
        "finite_height_reconstruction": mp.nstr(estimate, 24),
        "arithmetic_minus_finite_zero_reconstruction": mp.nstr(d["U"] - estimate, 24),
        "original_log_position_term": mp.nstr(d["position"], 24),
        "K": k,
        "historical_lower_slack": mp.nstr(slack, 24),
        "one_block_first_breach_margin": mp.nstr(breach_margin, 24),
        "interpretation": "diagnostic only; neither zero-list completeness nor signed owner return proved",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--roots", default="7,17,56,119")
    p.add_argument("--height-factor", type=float, default=1.0)
    p.add_argument("--dps", type=int, default=50)
    p.add_argument("--max-zero-count", type=int, default=500)
    p.add_argument("--wall-k", type=float, default=2.0)
    args = p.parse_args()
    roots = sorted({int(s) for s in args.roots.split(",")})
    if not roots or min(roots) < 5:
        raise ValueError("roots must all be >= 5")
    if args.height_factor <= 0 or args.dps < 20 or args.max_zero_count <= 0:
        raise ValueError("positive height, 20+ digits, positive max zero count required")
    mp.mp.dps = args.dps
    zeros, incomplete = gather_critical_line_zeros(
        args.height_factor * max(roots), args.max_zero_count
    )
    spf = least_prime_factors((max(roots) + 1) ** 2)
    out = {
        "status": "exploratory_finite_zero_comparison_NOT_a_proof",
        "critical_line_zeros_found": len(zeros),
        "zero_list_hit_max_count": incomplete,
        "warning": (
            "mpmath zetazero is NOT a proof that all nontrivial zeros "
            "were enumerated; no rigorous T-truncation constant is applied"
        ),
        "samples": [
            evaluate(r, spf, zeros, args.height_factor, args.wall_k)
            for r in roots
        ],
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
