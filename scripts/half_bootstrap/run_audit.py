#!/usr/bin/env python3
"""Exact algebra and finite original-source checks; not a zero-bound proof.

Run from any directory. Only the Python standard library is required.
The analytic inputs and all-scale estimates in the accompanying notes remain
separate proof obligations. This program neither invokes Lean nor certifies
the paper asymptotics.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from euler_exact_check import Polynomial, run_checks as run_euler_checks
from native_identity_check import run_native_identity_checks


def require_equal(actual, expected, label):
    if actual != expected:
        raise AssertionError(f"{label}: {actual!r} != {expected!r}")


def geometry_and_recurrences():
    """Coefficient identities and exact rational barriers, without sampling."""
    # Coefficients of x,y,1 in (5x+y)/12 - (x/3-29/36).
    low_coefficients = (F(5, 12) - F(1, 3), F(1, 12), F(29, 36))
    require_equal(low_coefficients, (F(1, 12), F(1, 12), F(29, 36)), "LOW normalization")
    # (3/2)(5/3-2s) <= 1/6 gives s >= 7/9.
    minimum_sum = (F(5, 2) - F(1, 6)) / 3
    require_equal(minimum_sum, F(7, 9), "LOW admissibility")
    low_floor = F(29, 36) + minimum_sum / 12
    require_equal(low_floor, F(47, 54), "LOW floor")
    cumulative_tilt = (F(5, 6) - minimum_sum) / 12
    require_equal(cumulative_tilt, F(1, 216), "cumulative Y-tilt budget")
    require_equal(F(7, 8) - cumulative_tilt, low_floor, "Y-tilt endpoint")

    # Native update in t and eta. The two entries are their coefficients.
    # b_next=(2b+1)/4+eta/2, b=1/2+t.
    next_constant = (2 * F(1, 2) + 1) / 4
    next_coefficients = (F(2, 4), F(1, 2))
    require_equal(next_constant, F(1, 2), "native critical center")
    require_equal(next_coefficients, (F(1, 2), F(1, 2)), "native gap map")
    require_equal(sum(next_coefficients), 1, "eta=t has no gain")
    require_equal((1 + F(1, 2)) / 2, F(3, 4), "eta=t/2 contraction")

    # Verify the fixed-cost solution as a polynomial induction schema:
    # u represents 2^(-n); the update must replace u by u/2 for all t0,eta,u.
    t0, eta, u = (Polynomial.variable(name) for name in ("t0", "eta", "u"))
    current = eta + u * (t0 - eta)
    advanced = F(1, 2) * (current + eta)
    expected = eta + F(1, 2) * u * (t0 - eta)
    require_equal((advanced - expected).is_zero, True, "fixed-cost induction schema")
    require_equal((current.substitute({"u": 1}) - t0).is_zero, True, "fixed-cost initial value")

    return {
        "status": "PASS_EXACT_RATIONAL_IDENTITIES",
        "low_floor": str(low_floor),
        "cumulative_y_tilt_budget": str(cumulative_tilt),
        "native_gap_update": "(t+eta)/2",
        "fixed_eta_solution": "eta + 2^(-n)*(t_0-eta)",
        "eta_equal_t_over_two_contraction": "3/4",
        "scope": "Coefficient algebra only; no native norm supplier is proved.",
    }


def run_audit():
    return {
        "status": "PASS_EXACT_ALGEBRA_AND_FINITE_IDENTITIES_ONLY",
        "source_main": "076195b75278869d4f18fd924b9ebdaedf723108",
        "source_reports": "bfed46eb81d3e7e782ea4e921008afb3959df54d",
        "geometry_and_recurrences": geometry_and_recurrences(),
        "euler_and_response": run_euler_checks(),
        "native_source": run_native_identity_checks(r_min=2, r_max=64),
        "lean_executed": False,
        "new_zero_bound": False,
        "verified_eta": None,
        "unproved_inputs": [
            "Native arithmetic supplier with eta(t)<t",
            "Expanded angular-family prime cancellation and uniform exponent gain",
            "Complete physical return below the current LOW floor",
            "Global multiplier identification and numerator-zero control",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print the scoped JSON result")
    parser.add_argument("--output", type=Path, help="also write that result to this path")
    args = parser.parse_args()
    result = run_audit()
    serialized = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(serialized, encoding="utf-8")
    if args.json:
        print(serialized, end="")
    else:
        print(result["status"])
        print("LOW floor 47/54; native source R=2..64; exact Euler/response algebra.")
        print("No all-scale supplier, new zero bound, or Lean certification.")


if __name__ == "__main__":
    main()
