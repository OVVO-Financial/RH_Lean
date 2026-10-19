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
