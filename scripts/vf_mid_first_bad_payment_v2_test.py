#!/usr/bin/env python3
"""Fast, stdlib-only, independently sieved ACTUAL-prime verification of the
exact original parity-compressed first-bad budget.

No approximation to pi, no fantasy proxy, no fabricated even charges.
A negative actual hbalance is REPORTED, never silently treated as a failed
theorem: the intended payment is only under a hypothetical first-bad.

Examples:
  python3 scripts/vf_mid_first_bad_payment_v2_test.py
  python3 scripts/vf_mid_first_bad_payment_v2_test.py --extended
"""
import argparse
import math
import time


def prime_flags(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            start = p * p
            flags[start::p] = b"\x00" * ((limit - start) // p + 1)
    return flags


def count_at_queries(flags, queries):
    """All exact prime counts, using a single scan of the sieve."""
    out = {}
    prior = 0
    count = 0
    for n in sorted(set(queries)):
        if not (0 <= n < len(flags)):
            raise ValueError(f"prime query outside sieve: {n}")
        count += sum(flags[prior + 1:n + 1])
        out[n] = count
        prior = n
    return out


def midpoint_prefix(max_r):
    """At squares VF_mid(R^2) = sum_{r=2}^{R-1} V_r, no Li approximation."""
    vf = [0.0] * (max_r + 2)
    for r in range(2, max_r + 1):
        mass = (2 * r + 1) / math.log(r * r + r + 0.5)
        vf[r + 1] = vf[r] + mass
    return vf


def close(a, b, scale=1.0):
    return math.isclose(a, b, rel_tol=3e-12, abs_tol=3e-9 * scale)


def verify(r, pi, vf, flags=None):
    """Verify exact formulas numerically, never assert the open sign gate."""
    x, y = r * r, (r + 1) * (r + 1)
    pr = pi[y] - pi[x]
    composites = r - pr
    assert 0 <= pr <= r, ("odd physical seats", r, pr)
    w = (2 * r + 1) / (r * math.log(r * r + r + 0.5))
    v = w * r
    d0 = pi[x] - vf[r]
    d1 = pi[y] - vf[r + 1]

    # The complete full-lattice VF mass is carried by EXACTLY r odd sites.
    # Prime charge -1 is placed ONLY on actual odd prime candidates.
    upper = max(-d0, 0.0) + w * composites
    lower = max(d0, 0.0) + (1.0 - w) * pr
    signed = upper - lower
    abs_mass = upper + lower
    original_mass_sq = (abs(d0) + w * composites + (1.0 - w) * pr) ** 2
    balance = original_mass_sq - 2.0 * d1 ** 2

    assert close(v, vf[r + 1] - vf[r]), ("reference all seats", r)
    assert close(d1, d0 + pr - v), ("exact block recurrence", r)
    assert close(signed, -d1), ("full signed parity reconstruction", r)
    assert close(abs_mass ** 2, original_mass_sq), ("original NNS mass", r)
    assert close(abs_mass ** 2 - 2.0 * signed ** 2, balance), ("cone algebra", r)
    assert close(original_mass_sq, (upper + lower) ** 2), ("L1 norm", r)

    if flags is not None:
        # Independent physical seat audit; no even candidate may enter.
        odds = list(range(x + 1, y, 2))
        if (x + 1) % 2 == 0:
            odds = list(range(x + 2, y, 2))
        assert len(odds) == r, ("R odd sites", r)
        actual_primes = sum(flags[n] for n in odds)
        assert actual_primes == pr, ("actual prime seats", r)
        charges = [w - int(flags[n]) for n in odds]
        assert close(sum(charges), v - pr), ("literal odd signed source", r)
        assert close(sum(abs(z) for z in charges),
                     w * composites + (1.0 - w) * pr), ("literal odd L1", r)
        # pi(even n) == pi(n-1), even though VF reference still advances.
        even_candidates = [x + 2, x + 4, y - 1]
        for n in even_candidates:
            if n % 2 == 0 and 4 <= n <= y:
                assert flags[n] == 0, ("even composites already absent", r, n)
    return {
        "R": r, "P": pr, "C": composites, "w": w,
        "D0": d0, "D1": d1, "U": upper, "L": lower,
        "M2": original_mass_sq, "slack": balance,
        "norm": (d1 * d1 / original_mass_sq if original_mass_sq > 0 else 0.0),
        "firstbad_breach": abs(d1) > 2 * (r + 1) * math.log(r + 1),
    }


def check_synthetic_counterexample():
    # w=1/4, P=0, C=8, D=0: U=2, L=0, slack=-4.
    # This rules out mistaking the symbolic algebra for an unconditional
    # arithmetic prime distribution/contraction proof.
    w, p, c, d = 0.25, 0, 8, 0
    u = max(-d, 0) + w * c
    l = max(d, 0) + (1 - w) * p
    assert u == 2 and l == 0
    assert (u + l) ** 2 - 2 * (u - l) ** 2 == -4


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extended", action="store_true",
                        help="every R=8..6000, including 317/1027/1760/5267")
    args = parser.parse_args()

    start = time.monotonic()
    samples = (8, 18, 29, 57, 119, 317, 1027)
    if args.extended:
        indices = range(8, 6001)
    else:
        indices = samples
    largest = max(indices)
    flags = prime_flags((largest + 1) ** 2)
    endpoints = {r * r for r in indices} | {(r + 1) ** 2 for r in indices}
    pi = count_at_queries(flags, endpoints)
    vf = midpoint_prefix(largest + 1)

    check_synthetic_counterexample()
    min_balance = (float("inf"), None)
    negatives = 0
    breaches = 0
    for r in indices:
        record = verify(r, pi, vf, flags if r in samples or r in (1760, 5267, 6000)
                        else None)
        if record["slack"] < min_balance[0]:
            min_balance = record["slack"], r
        negatives += record["slack"] < 0
        breaches += record["firstbad_breach"]
        if r in samples or r in (1760, 5267, 6000):
            print(f"R={r:<5d} P={record['P']:<5d} "
                  f"U={record['U']:.6f} L={record['L']:.6f} "
                  f"Dnext={record['D1']:+.6f} "
                  f"slack={record['slack']:+.4f} "
                  f"NNS={record['norm']:.6f} PASS")
    print(f"PASS {len(indices)} true-prime blocks: exactly 2R full integers, "
          f"R odd candidates, w=V/R, unchanged original anchored mass; "
          f"negative balances={negatives} (diagnostic, not failures); "
          f"firstbad breaches={breaches}; "
          f"minimum slack={min_balance}; elapsed={time.monotonic()-start:.2f}s")
    print("OPEN: hfirst-specific signed balance, NOT proved by the regression.")


if __name__ == "__main__":
    main()
