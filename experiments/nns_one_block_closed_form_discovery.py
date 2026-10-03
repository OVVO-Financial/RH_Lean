#!/usr/bin/env python3
"""Exact formula-discovery probe for the #877/#878 one-block NNS recurrence.

The purpose of this script is NOT to gather generic evidence for RH.  It treats
Lean/the integer arithmetic as an exact oracle and searches for the global
closed form of the one-square-block update.

For every root R it computes the exact integer data

    C_R = M(R-1) - M(R^2-1)
    Delta_R = M((R+1)^2-1) - M(R^2-1)
    U_R = mu(R) - Delta_R

and the target-zero NNS squarefree masses

    Qold_R = sum_{R <= n < R^2} mu(n)^2
    Qnew_R = mu(R)^2 + sum_{R^2 <= n < (R+1)^2} mu(n)^2.

Hence the literal rectangular target-zero NNS coefficient has the exact
factorized closed form

    rho_R = (C_R / Qold_R) * (U_R / Qnew_R).

The current square block is then grouped by canonical cofactor

    c(m) = m / P+(m),

where P+(m) is the largest prime factor.  On squarefree block sites Lean proves

    mu(m) = -mu(c(m)),

so, with N_R(c) the canonical-parent-fibre cardinality,

    Delta_R = - sum_c mu(c) N_R(c),
    U_R = mu(R) + sum_c mu(c) N_R(c),
    Qnew_R = mu(R)^2 + sum_c mu(c)^2 N_R(c).

Those identities are checked exactly.  The experiment then truncates the
canonical parent population at user-selected fractions of

    oldParentCutoff(R) = (R^2 - 1) // 2

and reports exactly how the normalized new-block bias changes.  This is meant
to mimic a chamber-discovery workflow: a failed candidate is localized to the
parent range whose activation was omitted.

Examples
--------
python experiments/nns_one_block_closed_form_discovery.py --r-min 56 --r-max 640
python experiments/nns_one_block_closed_form_discovery.py --r-min 56 --r-max 6400 --step 8 \
    --truncations 1/16,1/8,1/4,1/2,3/4,1
python experiments/nns_one_block_closed_form_discovery.py --r-min 3 --r-max 1000 \
    --csv /tmp/nns_one_block.csv

The sieve is deliberately simple and exact.  Large scans should be split into
several R windows rather than changing the arithmetic.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from fractions import Fraction
from pathlib import Path


def mobius_spf_sieve(limit: int) -> tuple[list[int], list[int]]:
    """Return mu(n) and smallest-prime-factor arrays for n <= limit."""

    if limit < 1:
        return [0] * (limit + 1), [0] * (limit + 1)

    spf = list(range(limit + 1))
    if limit >= 0:
        spf[0] = 0
    if limit >= 1:
        spf[1] = 1

    p = 2
    while p * p <= limit:
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
        p += 1

    mu = [0] * (limit + 1)
    mu[1] = 1
    for n in range(2, limit + 1):
        p = spf[n]
        m = n // p
        if m % p == 0:
            mu[n] = 0
        else:
            mu[n] = -mu[m]
    return mu, spf


def largest_prime_factor(n: int, spf: list[int]) -> int:
    """Largest prime factor, with the Lean-compatible convention P+(0)=P+(1)=1."""

    if n <= 1:
        return 1
    largest = 1
    while n > 1:
        p = spf[n]
        largest = p
        while n % p == 0:
            n //= p
    return largest


def prefix_sum(values: list[int]) -> list[int]:
    out = [0] * len(values)
    running = 0
    for i, value in enumerate(values):
        running += value
        out[i] = running
    return out


def interval_prefix_sum(prefix: list[int], lo: int, hi: int) -> int:
    """Inclusive sum on [lo,hi]."""

    if hi < lo:
        return 0
    return prefix[hi] - (prefix[lo - 1] if lo > 0 else 0)


def parse_fractions(spec: str) -> list[Fraction]:
    ans = sorted(set(Fraction(item.strip()) for item in spec.split(",") if item.strip()))
    if not ans:
        raise ValueError("at least one truncation is required")
    if ans[0] < 0 or ans[-1] > 1:
        raise ValueError("truncations must lie in [0,1]")
    return ans


def frac_parts(x: Fraction | None) -> tuple[int | str, int | str]:
    if x is None:
        return "", ""
    return x.numerator, x.denominator


def measure_root(
    R: int,
    mu: list[int],
    spf: list[int],
    M: list[int],
    Q: list[int],
    truncations: list[Fraction],
) -> dict:
    lo = R * R
    hi = (R + 1) * (R + 1) - 1
    endpoint = lo - 1

    corr = M[R - 1] - M[endpoint]
    delta = M[hi] - M[endpoint]
    update = mu[R] - delta

    qold = interval_prefix_sum(Q, R, endpoint)
    qblock = interval_prefix_sum(Q, lo, hi)
    qnew = mu[R] * mu[R] + qblock

    alpha = Fraction(corr, qold) if qold else None
    beta = Fraction(update, qnew) if qnew else None
    rho = Fraction(corr * update, qold * qnew) if qold and qnew else None
    if alpha is not None and beta is not None:
        assert rho == alpha * beta

    fibres: Counter[int] = Counter()
    owner_low = owner_high = 0
    position_quarters = [0, 0, 0, 0]

    block_len = hi - lo + 1
    for m in range(lo, hi + 1):
        if mu[m] == 0:
            continue
        pmax = largest_prime_factor(m, spf)
        c = m // pmax
        fibres[c] += 1
        if pmax <= R:
            owner_low += 1
        else:
            owner_high += 1
        q = min(3, (4 * (m - lo)) // max(1, block_len))
        position_quarters[q] += 1

    cutoff = endpoint // 2
    assert all(c <= cutoff for c in fibres)

    parent_signed = sum(mu[c] * mult for c, mult in fibres.items())
    parent_squarefree = sum((mu[c] * mu[c]) * mult for c, mult in fibres.items())

    # Exact Lean identities mirrored by ExactPrefixPopulationIdentity.
    assert delta == -parent_signed
    assert update == mu[R] + parent_signed
    assert qblock == parent_squarefree
    assert qnew == mu[R] * mu[R] + parent_squarefree

    matched_signed = sum(
        mu[c] * mult for c, mult in fibres.items() if R <= c <= cutoff
    )
    lower_signed = sum(mu[c] * mult for c, mult in fibres.items() if c < R)
    matched_energy = sum(
        mu[c] * mu[c] * mult for c, mult in fibres.items() if R <= c <= cutoff
    )
    lower_energy = sum(
        mu[c] * mu[c] * mult for c, mult in fibres.items() if c < R
    )
    assert parent_signed == matched_signed + lower_signed
    assert parent_squarefree == matched_energy + lower_energy

    trunc_rows = []
    for frac in truncations:
        cmax = (cutoff * frac.numerator) // frac.denominator
        signed = sum(mu[c] * mult for c, mult in fibres.items() if c <= cmax)
        energy = sum(
            mu[c] * mu[c] * mult for c, mult in fibres.items() if c <= cmax
        )
        u_trunc = mu[R] + signed
        q_trunc = mu[R] * mu[R] + energy
        beta_trunc = Fraction(u_trunc, q_trunc) if q_trunc else None
        trunc_rows.append(
            {
                "frac": frac,
                "cmax": cmax,
                "signed": signed,
                "energy": energy,
                "u_trunc": u_trunc,
                "q_trunc": q_trunc,
                "beta_trunc": beta_trunc,
                "u_residual": update - u_trunc,
                "q_residual": qnew - q_trunc,
            }
        )

    lambda_empirical = Fraction(-update, corr) if corr else None

    return {
        "R": R,
        "corr": corr,
        "delta": delta,
        "update": update,
        "qold": qold,
        "qblock": qblock,
        "qnew": qnew,
        "alpha": alpha,
        "beta": beta,
        "rho": rho,
        "lambda_empirical": lambda_empirical,
        "cutoff": cutoff,
        "fibres": fibres,
        "parent_signed": parent_signed,
        "parent_squarefree": parent_squarefree,
        "lower_signed": lower_signed,
        "matched_signed": matched_signed,
        "lower_energy": lower_energy,
        "matched_energy": matched_energy,
        "owner_low": owner_low,
        "owner_high": owner_high,
        "position_quarters": position_quarters,
        "truncations": trunc_rows,
    }


def print_root(row: dict) -> None:
    def fs(x: Fraction | None) -> str:
        return "NA" if x is None else f"{x.numerator}/{x.denominator}"

    print(
        f"R={row['R']:5d} "
        f"C={row['corr']:6d} U={row['update']:5d} "
        f"Q-= {row['qold']:7d} Q+= {row['qnew']:5d} "
        f"alpha={fs(row['alpha']):>12} beta={fs(row['beta']):>12} "
        f"rho={fs(row['rho']):>14}"
    )
    print(
        "  parents:"
        f" lower signed={row['lower_signed']:5d}, matched signed={row['matched_signed']:5d};"
        f" lower sf={row['lower_energy']:5d}, matched sf={row['matched_energy']:5d};"
        f" owner<=R={row['owner_low']:5d}, owner>R={row['owner_high']:5d}"
    )
    for tr in row["truncations"]:
        print(
            f"    c<={str(tr['frac']):>5} cutoff:"
            f" U={tr['u_trunc']:5d}, Q={tr['q_trunc']:5d},"
            f" beta={fs(tr['beta_trunc']):>12},"
            f" residual(U,Q)=({tr['u_residual']:5d},{tr['q_residual']:5d})"
        )


def write_csv(path: Path, rows: list[dict]) -> None:
    fields = [
        "R", "corr", "delta", "update", "qold", "qblock", "qnew",
        "alpha_num", "alpha_den", "beta_num", "beta_den", "rho_num", "rho_den",
        "lambda_num", "lambda_den", "cutoff", "parent_signed",
        "parent_squarefree", "lower_signed", "matched_signed", "lower_energy",
        "matched_energy", "owner_low", "owner_high", "quarter0", "quarter1",
        "quarter2", "quarter3",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            an, ad = frac_parts(row["alpha"])
            bn, bd = frac_parts(row["beta"])
            rn, rd = frac_parts(row["rho"])
            ln, ld = frac_parts(row["lambda_empirical"])
            quarters = row["position_quarters"]
            writer.writerow(
                {
                    "R": row["R"],
                    "corr": row["corr"],
                    "delta": row["delta"],
                    "update": row["update"],
                    "qold": row["qold"],
                    "qblock": row["qblock"],
                    "qnew": row["qnew"],
                    "alpha_num": an, "alpha_den": ad,
                    "beta_num": bn, "beta_den": bd,
                    "rho_num": rn, "rho_den": rd,
                    "lambda_num": ln, "lambda_den": ld,
                    "cutoff": row["cutoff"],
                    "parent_signed": row["parent_signed"],
                    "parent_squarefree": row["parent_squarefree"],
                    "lower_signed": row["lower_signed"],
                    "matched_signed": row["matched_signed"],
                    "lower_energy": row["lower_energy"],
                    "matched_energy": row["matched_energy"],
                    "owner_low": row["owner_low"],
                    "owner_high": row["owner_high"],
                    "quarter0": quarters[0],
                    "quarter1": quarters[1],
                    "quarter2": quarters[2],
                    "quarter3": quarters[3],
                }
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-min", type=int, default=56)
    parser.add_argument("--r-max", type=int, default=256)
    parser.add_argument("--step", type=int, default=1)
    parser.add_argument(
        "--truncations",
        default="1/16,1/8,1/4,1/2,3/4,1",
        help="comma-separated parent-cutoff fractions",
    )
    parser.add_argument("--csv", type=Path)
    parser.add_argument(
        "--quiet", action="store_true", help="suppress per-root human-readable output"
    )
    args = parser.parse_args()

    if args.r_min < 3 or args.r_max < args.r_min or args.step < 1:
        raise SystemExit("require 3 <= r-min <= r-max and step >= 1")

    truncations = parse_fractions(args.truncations)
    maximum = (args.r_max + 1) ** 2 - 1
    print(f"building exact Mobius/SPF sieve through {maximum:,} ...")
    mu, spf = mobius_spf_sieve(maximum)
    M = prefix_sum(mu)
    Q = prefix_sum([x * x for x in mu])

    rows = []
    for R in range(args.r_min, args.r_max + 1, args.step):
        row = measure_root(R, mu, spf, M, Q, truncations)
        rows.append(row)
        if not args.quiet:
            print_root(row)

    if args.csv:
        write_csv(args.csv, rows)
        print(f"wrote {args.csv}")

    # Discovery summary: exact ranges of normalized block/history biases.
    alphas = [row["alpha"] for row in rows if row["alpha"] is not None]
    betas = [row["beta"] for row in rows if row["beta"] is not None]
    rhos = [row["rho"] for row in rows if row["rho"] is not None]
    if alphas and betas and rhos:
        print(
            "summary:"
            f" alpha in [{min(alphas)}, {max(alphas)}],"
            f" beta in [{min(betas)}, {max(betas)}],"
            f" rho in [{min(rhos)}, {max(rhos)}]"
        )

    print("all exact parent-fibre and NNS factorization checks passed")


if __name__ == "__main__":
    main()
