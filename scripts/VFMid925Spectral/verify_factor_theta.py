#!/usr/bin/env python3
"""Actual square-factor theta / psi_0 / half-jump verification for PR #925.

Entirely finite genuine integer arithmetic. Does NOT import or approximate
zeta zeros, prove a spectral cancellation bound, or claim RH.
"""
from __future__ import annotations

import argparse
import json
import math
from collections import Counter


def least_prime_factors(nmax: int) -> list[int]:
    spf = list(range(nmax + 1))
    for p in range(2, math.isqrt(nmax) + 1):
        if spf[p] == p:
            for n in range(p * p, nmax + 1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def log_mangoldt(n: int, spf: list[int]) -> float:
    if n < 2:
        return 0.0
    p = spf[n]
    t = n
    while t % p == 0:
        t //= p
    return math.log(p) if t == 1 else 0.0


def close(label: str, lhs: float, rhs: float, root: int, eps: float = 2e-9) -> None:
    if not math.isclose(lhs, rhs, abs_tol=eps, rel_tol=1e-12):
        raise AssertionError(
            f"{label}, R={root}: lhs={lhs!r}, rhs={rhs!r}, diff={lhs-rhs}"
        )


def run(max_root: int) -> dict:
    if max_root < 8:
        raise ValueError("max_root must be >= 8")
    spf = least_prime_factors((max_root + 1) ** 2)
    stats = Counter()
    witnesses = {}
    first_seen = None

    for root in range(5, max_root + 1):
        a, b = root * root, (root + 1) ** 2
        candidate = [
            n for n in range(a + 1, b)
            if math.gcd(n, 30) == 1
        ]
        covered = [n for n in candidate if spf[n] <= root]
        survived = [n for n in candidate if spf[n] > root]
        genuine = [n for n in range(a + 1, b) if spf[n] == n]
        if set(survived) != set(genuine):
            raise AssertionError(f"FTA survivor mismatch at root {root}")
        if len(candidate) != len(covered) + len(survived):
            raise AssertionError("candidate partition violated")
        if any(spf[n] < 7 for n in candidate):
            raise AssertionError("fixed wheel did not delete 2,3,5 factors")
        if any(spf[n] != n for n in survived):
            raise AssertionError("composite escaped full factor sieve")

        Q = math.fsum(math.log(n) for n in survived)
        theta_band = math.fsum(math.log(n) for n in genuine)
        H = math.fsum(
            log_mangoldt(n, spf)
            for n in range(a + 1, b)
            if spf[n] != n
        )
        psi_interior = math.fsum(
            log_mangoldt(n, spf) for n in range(a + 1, b)
        )
        La = log_mangoldt(a, spf)
        Lb = log_mangoldt(b, spf)

        # Exact finite psi0 formula, using genuine prime powers at both
        # square endpoints and the native (a,b] Chebyshev convention.
        psi_right_closed = psi_interior + Lb
        psi0_diff = psi_right_closed - Lb / 2 + La / 2
        psi0_expected = Q + H + (La + Lb) / 2

        close("factor Q = theta increment", Q, theta_band, root)
        close("strict psi interior = theta + higher powers", psi_interior, Q + H, root)
        close("psi0 both half jumps", psi0_diff, psi0_expected, root)

        width = 2 * root + 1
        midlog = math.log(root * root + root + 0.5)
        V = width / midlog
        P = len(survived)
        U = width - Q
        position = P - Q / midlog
        E = len(covered) - (len(candidate) - V)
        close("true factor coverage excess = VF - P", E, V - P, root)
        close("signed theta U and VF count excess", E, U / midlog - position, root)
        close("signed theta U as negative band error", U, -(Q - width), root)

        stats["roots"] += 1
        stats["wheel30_candidates"] += len(candidate)
        stats["distinct_divisor_covered"] += len(covered)
        stats["uncovered_genuine_primes"] += len(survived)
        stats["strict_interior_higher_prime_power_sites"] += sum(
            1
            for n in range(a + 1, b)
            if spf[n] != n and log_mangoldt(n, spf) > 0
        )
        stats["left_square_with_nonzero_lambda"] += (La > 0)
        stats["right_square_with_nonzero_lambda"] += (Lb > 0)

        if root in (5, 7, 8, 17, 56, 119, 317, 1027, max_root):
            witnesses[str(root)] = {
                "a": a,
                "b": b,
                "candidates": len(candidate),
                "covered": len(covered),
                "prime_survivors": P,
                "Q_log_survivors": Q,
                "H_strict_higher_powers": H,
                "Lambda_a": La,
                "Lambda_b": Lb,
                "psi0_step": psi0_diff,
                "theta_forcing": U,
                "VF_coverage_excess": E,
                "within_band_position": position,
            }
        if La > 0 and Lb > 0 and first_seen is None:
            first_seen = root

    if first_seen != 7:
        raise AssertionError(f"expected first double endpoint power at R=7; got {first_seen}")
    if stats["left_square_with_nonzero_lambda"] <= 0 or \
       stats["right_square_with_nonzero_lambda"] <= 0:
        raise AssertionError("no nonzero prime-power endpoint corrections tested")
    if max_root >= 7:
        r7 = witnesses["7"]
        close("R7 left endpoint", r7["Lambda_a"], math.log(7), 7)
        close("R7 right endpoint", r7["Lambda_b"], math.log(2), 7)
        close("R7 strict prime power interior", r7["H_strict_higher_powers"], 0, 7)
        close("R7 theta prime sites", r7["Q_log_survivors"],
              math.log(53) + math.log(59) + math.log(61), 7)

    return {
        "status": "finite_arithmetic_factor_theta_psi0_audit_not_RH",
        "max_root": max_root,
        "tested_complete_blocks": stats["roots"],
        "wheel30_candidates": stats["wheel30_candidates"],
        "distinct_divisor_covered": stats["distinct_divisor_covered"],
        "uncovered_genuine_primes": stats["uncovered_genuine_primes"],
        "strict_interior_higher_prime_power_sites":
            stats["strict_interior_higher_prime_power_sites"],
        "nonzero_left_square_half_jumps": stats["left_square_with_nonzero_lambda"],
        "nonzero_right_square_half_jumps": stats["right_square_with_nonzero_lambda"],
        "first_both_square_half_jumps": first_seen,
        "maximum_identity_residual_tolerance": 2e-9,
        "witnesses": witnesses,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-root", type=int, default=1027)
    args = parser.parse_args()
    print(json.dumps(run(args.max_root), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
