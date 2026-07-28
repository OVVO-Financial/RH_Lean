#!/usr/bin/env python3
"""Omega-parity vs orientation diagnostic for the squarefree Mobius sum.

This experiment tests the "prime-factor-count parity" attack vector directly and
is dependency-free (no numpy/pandas), so it runs in the same environment as
``lake build``.

Setup.  For squarefree ``m`` in ``(1, X]`` write ``q = P+(m)`` (largest prime
factor) and ``c = m / q`` (the canonical cofactor).  Then

    omega(c) = omega(m) - 1,      mu(m) = -mu(c) = (-1)^omega(m).

Hence the squarefree Mertens sum is the finite alternating omega-stratified sum

    M(X) = sum_{m<=X} mu(m) = 1 + sum_{k>=1} (-1)^k Q_k(X),
    Q_k(X) = #{ squarefree m <= X : omega(m) = k }.

This is exactly the ``death_shell_factor_omega`` coordinate already compiled in
``RHLean.Proof.DeathShellCofactorParity`` (there ``N_k`` counts shell sources by
cofactor omega), lifted to the global square prefix.

Two questions:

(1) THE LITERAL LEVER.  Is the 2-prime-factor class balanced against the
    3-prime-factor class, ``Q_2 ~ Q_3`` (and, pair by pair, ``Q_{2j} ~ Q_{2j+1}``)?
    If so, cancellation of consecutive pairs would give ``M`` small.

(2) THE ORIENTATION SPLIT.  Partition squarefree ``m`` by the largest prime
    factor relative to the square-root boundary:

        high (transport) :  P+(m) >  sqrt(m)
        low  (smooth)    :  P+(m) <= sqrt(m)

    and form the two orientation-restricted Mertens sums

        A_high = sum_{m<=X, P+(m)>sqrt m} mu(m) = sum_k (-1)^k Q_k^high,
        A_low  = sum_{m<=X, P+(m)<=sqrt m} mu(m) = sum_k (-1)^k Q_k^low,
        A_high + A_low = M(X).

    Is the operative cancellation the (2 vs 3) one, or the (high vs low) one?

Predeclared continue/stop criterion (per RESEARCH_ROUTE_REGISTRY acceptance rule):
  - The literal lever survives only if |Q_2 - Q_3| stays o(|Q_2|) AND does not
    change sign as X grows.  A growing, sign-changing gap falsifies it.
  - The orientation route is interesting only if |M(X)| / |A_high(X)| decreases
    with X (each orientation large, their signed sum a shrinking relative
    residual).  A flat or growing ratio kills it.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

KMAX = 16


def sieve(X: int):
    """Linear sieve of mu, omega, and largest prime factor through X."""
    spf = [0] * (X + 1)   # smallest prime factor
    lpf = [0] * (X + 1)   # largest prime factor
    omega = [0] * (X + 1)  # number of distinct prime factors
    mu = [0] * (X + 1)
    mu[1] = 1
    primes: list[int] = []
    for n in range(2, X + 1):
        if spf[n] == 0:
            spf[n] = n
            lpf[n] = n
            omega[n] = 1
            mu[n] = -1
            primes.append(n)
        sn = spf[n]
        for p in primes:
            m = n * p
            if p > sn or m > X:
                break
            spf[m] = p
            lpf[m] = lpf[n] if lpf[n] > p else p
            if p == sn:  # p | n already -> m not squarefree
                omega[m] = omega[n]
                mu[m] = 0
            else:
                omega[m] = omega[n] + 1
                mu[m] = -mu[n]
    return spf, lpf, omega, mu


def probe(X: int):
    _, lpf, omega, mu = sieve(X)
    Q = [0] * (KMAX + 1)
    Qhigh = [0] * (KMAX + 1)
    Qlow = [0] * (KMAX + 1)
    M = 1  # mu(1) = 1
    for m in range(2, X + 1):
        if mu[m] == 0:
            continue
        k = omega[m]
        Q[k] += 1
        M += mu[m]
        if lpf[m] * lpf[m] > m:   # P+(m) > sqrt(m)
            Qhigh[k] += 1
        else:
            Qlow[k] += 1
    return Q, Qhigh, Qlow, M


def alt(Q: list[int]) -> int:
    return sum(((-1) ** k) * Q[k] for k in range(len(Q)))


def report(X: int) -> dict:
    Q, Qh, Ql, M = probe(X)
    A_all = alt(Q)          # = M - 1  (since mu(1) sits at k=0 with Q_0 = 0 here)
    A_high = alt(Qh)
    A_low = alt(Ql)
    q23 = Q[2] - Q[3]
    q45 = Q[4] - Q[5]
    print(f"\n=== X = {X:>10}   (sqrt X = {int(math.isqrt(X))}) ===")
    print(f"  M(X) = {M}")
    print(f"  {'k':>3} {'Q_k':>10} {'Q_k high(q>rt)':>16} {'Q_k low(q<=rt)':>16}")
    for k in range(1, 9):
        if Q[k] == 0 and k > 4:
            continue
        print(f"  {k:>3} {Q[k]:>10} {Qh[k]:>16} {Ql[k]:>16}")
    print(f"  LITERAL LEVER : Q_2 - Q_3 = {q23:>8}   Q_4 - Q_5 = {q45:>8}")
    print(f"  ORIENTATION   : A_high = {A_high:>8}   A_low = {A_low:>8}"
          f"   (A_high + A_low = {A_high + A_low} = M-1+mu(1)? M={M})")
    ratio = abs(M) / abs(A_high) if A_high != 0 else float("nan")
    print(f"  |M| / |A_high| = {ratio:.4f}")
    return {
        "X": X,
        "M": M,
        "Q2": Q[2], "Q3": Q[3], "Q2_minus_Q3": q23,
        "Q4": Q[4], "Q5": Q[5], "Q4_minus_Q5": q45,
        "A_high": A_high, "A_low": A_low,
        "abs_M_over_abs_Ahigh": ratio,
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--scales", type=int, nargs="+",
                   default=[10**4, 10**5, 10**6, 4 * 10**6])
    p.add_argument("--output-dir", type=Path, default=Path("."))
    return p.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = [report(X) for X in args.scales]
    out = args.output_dir / "omega_parity_orientation.csv"
    with out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
