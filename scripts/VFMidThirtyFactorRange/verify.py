#!/usr/bin/env python3
"""Finite factor-range witness. It is NOT an induction or a proof of RH.

Each site is tested by its smallest proper divisor (a completely exact
integer sieve). The gcd-30 mask is applied BEFORE the d>=7 factor range,
and the 2/3/5 carriers and accumulated VF mass remain exactly unchanged.
Original pi is used ONLY as an independent FTA verification, never as
an assumption giving a density or lower bound.
"""
from __future__ import annotations

from array import array
import argparse
import json
import math


def least_factors(limit: int) -> array:
    """spf[n]=0 for prime n >=2; otherwise its smallest prime divisor."""
    spf = array("H", [0]) * (limit + 1)
    for p in range(2, math.isqrt(limit) + 1):
        if not spf[p]:
            for n in range(p * p, limit + 1, p):
                if not spf[n]:
                    spf[n] = p
    return spf


def audit(max_r: int, lag_constant: float) -> dict:
    if not 1027 <= max_r <= 10000:
        raise ValueError("Require 1027<=r-max<=10000 (16-bit least factor)")
    spf = least_factors((max_r + 1) ** 2)
    F = [0.] * (max_r + 2)
    for r in range(2, max_r + 1):
        F[r + 1] = F[r] + (2*r+1)/math.log(r*r+r+0.5)
    pi25 = sum(spf[n] == 0 for n in range(2, 26))
    assert pi25 == 9
    pi_at_sq, excess_acc = pi25, 0.
    all_candidates = all_covered = all_primes = all_end5 = 0
    first_failure = None
    min_margin, min_margin_r = math.inf, None
    max_telescope_error = 0.
    max_normalized_abs_defect = 0.
    owner_signs = [0, 0]
    anchors = {}
    for r in range(5, max_r+1):
        defect = pi_at_sq - F[r]
        expected_defect = pi25 - F[5] - excess_acc
        max_telescope_error = max(
            max_telescope_error, abs(defect-expected_defect))
        max_normalized_abs_defect = max(
            max_normalized_abs_defect, abs(defect)/(r*math.log(r)))
        h = min(r//2, math.floor(lag_constant*math.log(r)**2))
        shifted = r-h
        level = math.floor(F[shifted]+math.sqrt(2))
        margin = pi_at_sq-level
        if margin < min_margin: min_margin,min_margin_r = margin,r
        if margin < 0 and first_failure is None: first_failure = r
        N = C = P = last5 = 0
        for n in range(r*r+1, (r+1)**2):
            if n % 10 == 5:
                last5 += 1
            if math.gcd(n, 30) == 1:
                N += 1
                d = spf[n]
                if d:
                    assert 7 <= d <= r, (r, n, d)
                    C += 1
                else:
                    P += 1
            else:
                assert spf[n] != 0, (r, n, "small excluded prime")
        assert N-C == P
        assert N <= r and last5 <= r-N
        V = F[r+1]-F[r]
        excess = C-(N-V)
        assert abs(excess-(V-P)) < 3e-9
        owner_signs[excess<0] += 1
        if r in (5, 6, 17, 317, 1027, max_r):
            anchors[str(r)] = {
              "pi_r_squared":pi_at_sq, "vf_mass":F[r],
              "thirty_candidates":N, "factors_7_to_r_covered":C,
              "genuine_survivors":P,
              "ending_in_5_removed":last5,
              "sqrt2_lag":h, "sqrt2_horizontal_margin":margin,
              "lower_channel_K2_slack":defect+2*r*math.log(r),
              "physical_factor_excess":excess}
        excess_acc += excess
        pi_at_sq += P
        all_candidates += N
        all_covered += C
        all_primes += P
        all_end5 += last5
    def prefix30(n):
        return 8*(n//30)+sum(math.gcd(j,30)==1 for j in range(1,n%30+1))
    A,B = 5,max_r+1
    literal = (prefix30(B*B)-prefix30(A*A)
               -prefix30(B)+prefix30(A))
    assert literal == all_candidates
    expected = (4/15)*((B*B-A*A)-(B-A))
    phase = literal-expected
    assert abs(phase) <= 32+1e-7
    return {
      "status":"finite_integer_factor_sieve_not_a_universal_RH_proof",
      "block_range":[5,max_r],
      "blocks_checked":max_r-4,
      "gcd30_candidate_total":all_candidates,
      "factors_7_to_R_unique_covered_total":all_covered,
      "FTA_genuine_survivor_total":all_primes,
      "odd_last_digit_five_removed_total":all_end5,
      "factor_defect_identity_max_rounding_error":max_telescope_error,
      "positive_or_zero_factor_excess_blocks":owner_signs[0],
      "negative_factor_excess_blocks":owner_signs[1],
      "max_normalized_abs_defect_RlogR":max_normalized_abs_defect,
      "horizontal": {
        "phase":"sqrt(2) additive",
        "lag_constant":lag_constant,
        "lag":"min(floor(R/2),floor(A*log(R)^2))",
        "first_failure":first_failure,
        "minimum_margin":min_margin,
        "minimum_margin_at_R":min_margin_r,
      },
      "thirty_wheel_four_endpoint": {
        "candidate_total":literal,
        "density_4over15_expected":expected,
        "signed_error":phase,
        "proved_uniform_upper_bound":32,
      },
      "checkpoints":anchors,
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--r-max",type=int,default=2500)
    ap.add_argument("--lag",type=float,default=0.4)
    ap.add_argument("--assert-exact",action="store_true")
    args=ap.parse_args()
    report=audit(args.r_max,args.lag)
    if args.assert_exact:
        assert report["horizontal"]["first_failure"] is None
        assert report["factor_defect_identity_max_rounding_error"] < 1e-6
        assert report["thirty_wheel_four_endpoint"]["proved_uniform_upper_bound"] == 32
        assert report["checkpoints"]["17"]["genuine_survivors"] == 5
        assert report["checkpoints"]["317"]["pi_r_squared"] == 9631
        assert report["checkpoints"]["1027"]["pi_r_squared"] == 82462
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
