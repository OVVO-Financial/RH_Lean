#!/usr/bin/env python3
"""Exact Euler x VF historical Sector-Six occurrence incidence, not OAI Hecke phases.

Rows: AA HH PP AH AP HP (physical prime/smooth/high-composite source pairs).
Cols: first-left, first-right, next-left, next-right, returned-left, returned-right.
The shared historical active carrier is the ODD SQUAREFREE VF square block.
Both mu(n)*mu(m) and original VF charge(n)*charge(m) are retained separately.
No global signed bound, full-wheel bijection, or Hecke-character map is assumed.

Run: python3 scripts/vf919_euler_historical_six_by_six.py --roots 317 1027
"""
import argparse
import csv
import json
import math
from collections import defaultdict
from pathlib import Path

ROWS = ("AA", "HH", "PP", "AH", "AP", "HP")
COLS = ("first-left", "first-right", "next-left", "next-right",
        "returned-left", "returned-right")
REF = {
    317: [[193, 0, 0, -128, 0, 0],
          [5268, 0, 0, -3184, 498, 0],
          [0, 0, 0, 0, 1431, 0],
          [-110, 0, 0, -839, 0, 0],
          [0, 0, 0, 702, 0, 0],
          [0, 0, 0, -3942, 0, 0]],
    1027: [[1771, 0, 0, -1296, 0, 0],
           [41406, 0, 0, -29239, 2872, 0],
           [0, 0, 0, 0, 10296, 0],
           [565, 0, 0, -6340, 0, 0],
           [0, 0, 0, 4752, 0, 0],
           [0, 0, 0, -25200, 0, 0]],
}

def linear_sieve(nmax):
    smallest = [0] * (nmax + 1)
    mobius = [0] * (nmax + 1)
    mobius[1] = 1
    primes = []
    for n in range(2, nmax + 1):
        if not smallest[n]:
            smallest[n] = n
            mobius[n] = -1
            primes.append(n)
        for p in primes:
            child = n * p
            if child > nmax or p > smallest[n]:
                break
            smallest[child] = p
            if n % p == 0:
                mobius[child] = 0
                break
            mobius[child] = -mobius[n]
    return smallest, mobius

def factors(n, smallest):
    out = set()
    while n > 1:
        p = smallest[n]
        out.add(p)
        while n % p == 0:
            n //= p
    return out

def run(R, smallest, mu, outdir):
    assert R >= 2
    X = (R + 1) ** 2 - 1
    shell = [n for n in range(R * R + 1, X + 1) if mu[n]]
    active = [n for n in shell if n & 1]
    factor = {n: factors(n, smallest) for n in active}
    kind = {n: ("P" if smallest[n] == n else
                "A" if max(factor[n]) <= R else "H")
            for n in active}
    vfr = (2 * R + 1) / (R * math.log(R * R + R + 0.5))
    counts = [[0] * 6 for _ in range(6)]
    signed = [[0] * 6 for _ in range(6)]
    vf = [[0.] * 6 for _ in range(6)]
    examples = {}
    seen = 0
    for i, n in enumerate(active):
        fn = factor[n]
        for m in active[i + 1:]:
            # Least differing prime: the repo's ascending first-owner p.
            p = min(fn ^ factor[m])
            a, child = (n, m) if p not in fn else (m, n)
            assert p not in factor[a] and p in factor[child]
            b = child // p
            assert b and p * b == child and p * a > X >= p * b
            assert {q for q in factor[a] if q < p} == {
                q for q in factor[child] if q < p}
            # Greatest NEW owner of the p-free parent pair (a,b).
            fb = factor[child] - {p}
            diff = factor[a] ^ fb
            assert diff and min(diff) > p
            r = max(diff)
            u = a // r if r in factor[a] else a
            v = b // r if r in fb else b
            assert r not in factors(u, smallest)
            assert r not in factors(v, smallest)
            # Literal historical raw-parent first/next/returned filters.
            # Left priority matches RAW_PARENT_BOUNDARY_ORIENTED_FUBINI.lean.
            if p * u > X or p * v > X:
                j = 0 if p * u > X else 1
            elif r * u > X or r * v > X:
                j = 2 if r * u > X else 3
            elif p * r * u > X or p * r * v > X:
                j = 4 if p * r * u > X else 5
            else:
                raise AssertionError(("unclassified completed physical pair", R, n, m))
            types = "".join(sorted((kind[n], kind[m]),
                                   key={"A": 0, "H": 1, "P": 2}.__getitem__))
            k = ROWS.index(types)
            counts[k][j] += 1
            signed[k][j] += mu[n] * mu[m]
            vf[k][j] += ((vfr - (kind[n] == "P")) *
                         (vfr - (kind[m] == "P")))
            examples.setdefault((k, j), [n, m, p, r, u, v])
            seen += 1
    assert seen == len(active) * (len(active) - 1) // 2
    # Three columns vanish on the actual clipped x admitted carrier, not
    # on the whole historical polarization carrier.
    assert all(counts[i][j] == 0 for i in range(6) for j in (1, 2, 5))
    if R in REF:
        assert signed == REF[R], (R, signed, REF[R])
        minor = ((signed[0][0] * signed[1][3] -
                  signed[0][3] * signed[1][0]) * signed[2][4])
        assert minor != 0, ("rank less than three", R)
    masses = defaultdict(int)
    diagonals = defaultdict(int)
    for n in active:
        masses[kind[n]] += mu[n]
        diagonals[kind[n]] += 1
    A, H, P = (masses[t] for t in ("A", "H", "P"))
    KA, KH, KP = (diagonals[t] for t in ("A", "H", "P"))
    expected = [(A * A - KA) // 2, (H * H - KH) // 2,
                (P * P - KP) // 2, A * H, A * P, H * P]
    assert [sum(row) for row in signed] == expected
    s = sum(mu[n] for n in active)
    assert sum(map(sum, signed)) == (s * s - len(active)) // 2
    # Exact globally valid odd-carrier reduction, at this square cutoff.
    full_mertens = sum(mu[1:X + 1])
    odd_prefix = sum(mu[1:X + 1:2])
    odd_half_prefix = sum(mu[1:X // 2 + 1:2])
    assert full_mertens == odd_prefix - odd_half_prefix, (
        R, full_mertens, odd_prefix, odd_half_prefix)
    # PP + AP + HP are one signed algebraic bill; do not bound PP alone.
    assert P == -KP
    prime_rows = sum(sum(signed[i]) for i in (2, 4, 5))
    composite_rows = sum(sum(signed[i]) for i in (0, 1, 3))
    assert prime_rows == -(KP * (KP + 1)) // 2 - KP * s, (
        R, prime_rows, KP, s)
    assert composite_rows + prime_rows == sum(map(sum, signed))
    # Unique greatest-prime-factor decomposition n=m*q, with q>P+(m).
    # This is a distinct counting coordinate from the six historical sectors.
    prime_fibers = defaultdict(list)
    for n in active:
        q = max(factor[n])
        m = n // q
        assert q > 1 and smallest[q] == q
        assert m > 0 and (m & 1) and n == m * q and mu[n] == -mu[m]
        if m > 1:
            assert max(factors(m, smallest)) < q
        assert R * R < m * q < (R + 1) ** 2
        prime_fibers[m].append(q)
    assert all(len(qs) == len(set(qs)) for qs in prime_fibers.values())
    assert len(prime_fibers.get(1, [])) == KP
    odd_fiber_sum = -sum(mu[m] * len(qs) for m, qs in prime_fibers.items())
    assert odd_fiber_sum == s
    composite_fiber_sum = -sum(
        mu[m] * len(qs) for m, qs in prime_fibers.items() if m > 1)
    assert composite_fiber_sum == A + H
    assert sum(signed[4]) == -A * KP
    assert sum(signed[5]) == -H * KP
    assert sum(signed[4]) + sum(signed[5]) == KP * sum(
        mu[m] * len(qs) for m, qs in prime_fibers.items() if m > 1)
    # Exact rank-one double-difference, including BOTH defect cross bills.
    # alpha(m)=1/m is a deterministic reference, not a PNT approximation.
    carrier = set(prime_fibers) | {1, 3}
    rel = {m: 1.0 / m for m in carrier}
    defect = sum(mu[m] * rel[m] for m in carrier)
    raw = sum(mu[m] * len(prime_fibers.get(m, [])) for m in carrier)
    centered = sum(mu[m] * (
        len(prime_fibers.get(m, [])) - rel[m] * KP) for m in carrier)
    assert raw == -s
    assert abs(raw - (centered + defect * KP)) < 1.e-8
    assert abs(raw ** 2 -
               (centered ** 2 + 2 * defect * KP * centered +
                defect ** 2 * KP ** 2)) < 1.e-7
    # An exact zero-defect choice exists even if it gives NO variance gain:
    # alpha(1)=alpha(3)=1, and alpha(m)=0 elsewhere, so 1-mu(3)=0.
    alpha_zero = {m: 1.0 if m in (1, 3) else 0.0 for m in carrier}
    assert sum(mu[m] * alpha_zero[m] for m in carrier) == 0.0
    centered_zero = sum(mu[m] * (
        len(prime_fibers.get(m, [])) - alpha_zero[m] * KP)
        for m in carrier)
    assert centered_zero == raw
    # True p=3 sign/threshold invariance, NOT membership closure in this shell.
    parents_3 = [m for m in prime_fibers if m >= 5 and m % 3 != 0]
    parent_without_child = 0
    for d in parents_3:
        child = 3 * d
        if child > X:
            parent_without_child += 1
            continue
        assert max(factors(d, smallest)) == max(factors(child, smallest))
        assert mu[d] and mu[child] == -mu[d]
        if child not in prime_fibers:
            parent_without_child += 1
    # Even when gpf is invariant, q-shell supports of d and 3d differ.
    # In particular Q_R(d) and Q_R(3d) need not be simultaneously nonzero.
    # Non-circular rank-one drift removal; it changes no square energy.
    baseline = R / math.log(R)
    centered_composite = A + H - baseline
    centered_primes = KP - baseline
    assert abs((centered_composite - centered_primes) - s) < 1e-9
    assert abs((centered_composite - centered_primes) ** 2 - s ** 2) < 1e-8
    # These exact cancellations do not supply an asymptotic bound.
    vf_site = [vfr - (kind[n] == "P") for n in active]
    vf_total = ((sum(vf_site) ** 2) -
                sum(v * v for v in vf_site)) / 2
    assert abs(sum(map(sum, vf)) - vf_total) < 1.e-6
    sfull = sum(mu[n] for n in shell)
    fullcov = (sfull * sfull - len(shell)) // 2
    subsetcov = sum(map(sum, signed))
    missing = len(shell) * (len(shell) - 1) // 2 - seen
    summary = {
        "R": R, "X": X, "squarefree_sites": len(shell),
        "odd_active_sites": len(active),
        "even_squarefree_excluded_sites": len(shell) - len(active),
        "shared_occurrences": seen, "unmatched_even_occurrences": missing,
        "full_euler_pair_covariance": fullcov,
        "active_euler_pair_covariance": subsetcov,
        "composite_row_covariance": composite_rows,
        "prime_row_covariance": prime_rows,
        "prime_row_reduced_formula": -(KP * (KP + 1)) // 2 - KP * s,
        "odd_gpf_fiber_count": len(prime_fibers),
        "odd_gpf_signed_sum": odd_fiber_sum,
        "odd_gpf_composite_sum": composite_fiber_sum,
        "odd_gpf_prime_fiber": len(prime_fibers.get(1, [])),
        "gpf_double_diff_defect_one_over_m": defect,
        "gpf_double_diff_centered_one_over_m": centered,
        "gpf_double_diff_zero_defect_energy": centered_zero ** 2,
        "gpf_three_dipole_parents": len(parents_3),
        "gpf_three_dipole_parent_without_child": parent_without_child,
        "centered_drift": baseline,
        "centered_composite": centered_composite,
        "centered_prime": centered_primes,
        "full_mertens_at_X": full_mertens,
        "odd_mertens_at_X": odd_prefix,
        "odd_mertens_at_half_X": odd_half_prefix,
        "unmatched_signed_euler_covariance": fullcov - subsetcov,
        "original_VF_active_pair_covariance": vf_total,
        "nonzero_columns": [COLS[j] for j in (0, 3, 4)],
        "signed_6x6": signed, "count_6x6": counts,
        "vf_charge_6x6": vf,
        "examples": {ROWS[i] + "/" + COLS[j]: x
                     for (i, j), x in examples.items()},
    }
    for label, mat in (("signed", signed), ("count", counts),
                       ("vf_charge", vf)):
        with (outdir / f"vf919_sector_six_R{R}_{label}.csv").open("w") as fp:
            writer = csv.writer(fp)
            writer.writerow(["Euler/source"] + list(COLS) + ["row_total"])
            for rowname, row in zip(ROWS, mat):
                writer.writerow([rowname] + row + [sum(row)])
    print(f"PASS R={R}: {seen:,} exact pairs, "
          f"3/6 nonempty columns, full C={fullcov}, "
          f"active C={subsetcov}, missing-even C={fullcov-subsetcov}, "
          f"VF active C={vf_total:.9f}")
    return summary

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--roots", type=int, nargs="+", default=[317, 1027])
    parser.add_argument("--out", type=Path, default=Path("."))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    spf, mu = linear_sieve((max(args.roots) + 1) ** 2)
    result = [run(R, spf, mu, args.out) for R in args.roots]
    (args.out / "vf919_sector_six_summary.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("PASS: exact owner incidence, 6x6 row/column marginals, VF "
          "charges and excluded even-site budget")

if __name__ == "__main__":
    main()
