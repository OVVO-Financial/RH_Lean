#!/usr/bin/env python3
"""Machine-replayable finite c0 discrete VF step-graph alignment contract.

Uses the existing original-mass and prime-sieve definitions from verify.py.
This independently tests actual pi(R^2), not floor Li or fantasy primes.
No result is extrapolated to all square roots. It records the exact
canonical phase, each graph orientation, the finite successful-phase grid,
and genuine-prime checkpoints.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from verify import prime_counts_at_squares, vf_finished_masses, scan, phase_window


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-max", type=int, default=10000)
    parser.add_argument("--grid-step", type=float, default=0.001)
    parser.add_argument("--assert-10000", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if args.r_max < 1027:
        raise SystemExit("r-max must be >= 1027 for the four checkpoints")

    pi_sq = prime_counts_at_squares(args.r_max)
    f = vf_finished_masses(args.r_max)
    c0 = 4.0 - 5.0 / math.log(6.5)
    assert abs(c0 - (4.0 - f[3])) < 1e-14
    unaligned_h, unaligned_fail, unaligned_vertical, _ = scan(
        args.r_max, pi_sq, f, 0.0
    )
    aligned_h, aligned_fail, aligned_vertical, k = scan(
        args.r_max, pi_sq, f, c0
    )
    sqrt2 = math.sqrt(2.0)
    sqrt2_h, sqrt2_fail, sqrt2_vertical, sqrt2_k = scan(
        args.r_max, pi_sq, f, sqrt2
    )
    differing_levels = [
        r for r in range(2, args.r_max + 2) if sqrt2_k[r] != k[r]
    ]
    window = phase_window(
        args.r_max, pi_sq, f, start=0.0, stop=3.0, step=args.grid_step
    )
    nblocks = args.r_max - 1
    record = {
        "status": "finite_integer_sieve_diagnostic_not_universal_proof",
        "roots": [2, args.r_max],
        "blocks_tested": nblocks,
        "c0_formula": "4 - 5/log(13/2)",
        "F3": f[3],
        "c0": c0,
        "sqrt2_diagnostic": {
            "phase": sqrt2,
            "phase_difference_from_c0": sqrt2 - c0,
            "horizontal_crossings": (args.r_max - 1) - len(sqrt2_h),
            "left_vertical_only": sum(m == "L" for _, m in sqrt2_vertical),
            "right_vertical_only": sum(m == "R" for _, m in sqrt2_vertical),
            "full_graph_failures": sqrt2_fail,
            "integer_levels_differing_from_c0": len(differing_levels),
            "first_differing_root": differing_levels[0] if differing_levels else None,
            "root_6_levels": {
                "pi_36": pi_sq[6],
                "F_6": f[6],
                "canonical_K_6": k[6],
                "sqrt2_K_6": sqrt2_k[6],
            },
        },
        "canonical": {
            "horizontal_crossings": nblocks - len(aligned_h),
            "left_vertical_only": sum(m == "L" for _, m in aligned_vertical),
            "right_vertical_only": sum(m == "R" for _, m in aligned_vertical),
            "full_graph_failures": aligned_fail,
            "vertical_rescues": aligned_vertical,
        },
        "unaligned": {
            "horizontal_failures": unaligned_h,
            "full_graph_failures": unaligned_fail,
            "vertical_rescues": unaligned_vertical,
        },
        "phase_grid": {
            "step": args.grid_step,
            "start": 0.0,
            "stop": 3.0,
            "first_good": window[0] if window else None,
            "last_good": window[1] if window else None,
        },
        "anchors": {
            str(r): {
                "actual_pi_at_r_squared": pi_sq[r],
                "real_finished_vf_mass": f[r],
                "aligned_integer_level": k[r],
                "integer_backlog": k[r] - pi_sq[r],
                "rounding_phase": (f[r] + c0) - k[r],
            }
            for r in (3, 17, 317, 1027)
        },
    }
    # Algebraic acceptance for all four independent checked roots;
    # no extra prime-distribution bound is assumed.
    assert record["anchors"]["3"]["aligned_integer_level"] == 4
    assert all(0 <= p["rounding_phase"] < 1 for p in record["anchors"].values())
    assert (
        record["canonical"]["horizontal_crossings"]
        + record["canonical"]["left_vertical_only"]
        + record["canonical"]["right_vertical_only"]
        + len(aligned_fail)
        == nblocks
    )

    if args.assert_10000:
        assert args.r_max == 10000 and args.grid_step == 0.001
        assert not aligned_fail
        assert record["canonical"]["horizontal_crossings"] == 9994
        assert record["canonical"]["left_vertical_only"] == 4
        assert record["canonical"]["right_vertical_only"] == 1
        assert unaligned_fail == [2, 3, 4]
        assert window == (1.329, 1.865)
        assert pi_sq[17] == 61
        assert pi_sq[317] == 9631
        assert pi_sq[1027] == 82462
        assert sqrt2_fail == []
        assert (nblocks - len(sqrt2_h)) == 9994
        assert sqrt2_vertical == aligned_vertical
        assert len(differing_levels) == 863
        assert differing_levels[0] == 6
        assert k[6] == 12 and sqrt2_k[6] == 13

    result = json.dumps(record, indent=2, sort_keys=True) + "\n"
    if args.json_out:
        args.json_out.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
