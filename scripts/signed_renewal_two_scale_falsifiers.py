#!/usr/bin/env python3
"""Exact-integer falsification checks for SIGNED_RENEWAL_TWO_SCALE_ATTACK_PLAN_20261018.

Uses genuine Mobius signs, primes and square shells. No PNT approximation, fitted
power law, probabilistic assumption, Lean import or RH claim is made.

Run:
  python3 scripts/signed_renewal_two_scale_falsifiers.py --max-root 317
"""
from __future__ import annotations

import argparse
from math import isqrt


def make_tables(limit: int):
    spf = [0] * (limit + 1)
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes = []
    for i in range(2, limit + 1):
        if spf[i] == 0:
            spf[i] = i
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if p > spf[i] or i * p > limit:
                break
            spf[i * p] = p
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    is_prime = [False] * (limit + 1)
    for p in primes:
        is_prime[p] = True
    pi = [0] * (limit + 1)
    mertens = [0] * (limit + 1)
    largest = [0] * (limit + 1)
    largest[1] = 1
    for n in range(1, limit + 1):
        pi[n] = pi[n - 1] + int(is_prime[n])
        mertens[n] = mertens[n - 1] + mu[n]
        if n >= 2:
            largest[n] = max(spf[n], largest[n // spf[n]])
    return mu, pi, mertens, largest, is_prime


def incidence(r: int, c: int, pi):
    assert 1 <= c <= r
    return pi[((r + 1) ** 2 - 1) // c] - pi[(r * r) // c]


def shell(r: int, mu, pi, mertens, largest):
    lo = r * r
    hi = (r + 1) ** 2 - 1
    smooth = sum(mu[n] for n in range(lo + 1, hi + 1) if largest[n] <= r)
    transported = sum(mu[c] * incidence(r, c, pi) for c in range(1, r + 1))
    q_count = incidence(r, 1, pi)
    composite = smooth - sum(mu[c] * incidence(r, c, pi) for c in range(2, r + 1))
    delta = mertens[hi] - mertens[lo]
    assert smooth - transported == delta, ("S=A-T shell", r)
    assert composite - q_count == delta, ("C-Q shell", r)
    return delta, q_count, composite, smooth, transported


def check_compensator(r: int, mu, pi, mertens, largest):
    lo = r * r
    hi = (r + 1) ** 2 - 1
    bsmooth = [0] * (r + 1)
    smooth_sites = [n for n in range(lo + 1, hi + 1) if largest[n] <= r]
    for n in smooth_sites:
        for d in range(1, r + 1):
            if n % d == 0:
                bsmooth[d] += mu[n]
    a = [0] * (r + 1)
    z = [0] * (r + 1)
    e = [0] * (r + 1)
    for c in range(1, r + 1):
        a[c] = sum(mu[k] * bsmooth[k * c] for k in range(1, r // c + 1))
        z[c] = mu[c] * incidence(r, c, pi)
        e[c] = z[c] - a[c]
    delta = mertens[hi] - mertens[lo]
    assert sum(e) == -delta, ("compensator zero mode", r)
    for d in range(1, r + 1):
        cofactor_a = sum(a[c] for c in range(d, r + 1, d))
        assert cofactor_a == bsmooth[d], ("inverted smooth profile", r, d)
        divisor_shell = sum(mu[n] for n in range(lo + 1, hi + 1) if n % d == 0)
        assert divisor_shell == -sum(e[c] for c in range(d, r + 1, d)), (
            "centered divisor profile", r, d
        )
    return e[1], delta


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-root", type=int, default=317,
                        help="largest root in the exact tables (default 317)")
    args = parser.parse_args()
    max_root = args.max_root
    if max_root < 13 or max_root > 2000:
        parser.error("choose 13 <= max-root <= 2000 for this finite census")
    mu, pi, mertens, largest, is_prime = make_tables((max_root + 1) ** 2)
    data = {}
    for r in range(2, max_root + 1):
        data[r] = shell(r, mu, pi, mertens, largest)
    spot_roots = [r for r in (2, 7, 13, 18, 56, 317) if r <= max_root]
    for r in spot_roots:
        delta, q_count, composite, smooth, transported = data[r]
        e1, delta_check = check_compensator(r, mu, pi, mertens, largest)
        assert delta == delta_check
        if is_prime[r]:
            correct = incidence(r, r, pi)
            wrong_lower = pi[((r + 1) ** 2 - 1) // r] - pi[(r * r - 1) // r]
            assert wrong_lower == correct + 1, ("strict lower endpoint", r)
        print(f"r={r:4d} delta={delta:5d} Q={q_count:4d} C={composite:5d} "
              f"smooth={smooth:5d} transport={transported:5d} e(1)={e1:5d}")
    for h in (8, 16, 32, 64, 128, 256, 512):
        if 2 * h - 1 > max_root:
            continue
        left = sum(data[r][1] * data[r][2] for r in range(h, 2 * h))
        right = sum(data[isqrt(q)][2]
                    for q in range(h * h + 1, (2 * h) ** 2)
                    if is_prime[q])
        assert left == right, ("outer prime cross-term", h)
        energy = sum(data[r][0] ** 2 for r in range(h, 2 * h))
        print(f"H={h:4d} cross_QC={left:10d} shell_energy={energy:10d} "
              "outer-prime reindex EXACT")
    for r in (6, 12, 16, 30):
        if r + 1 > max_root or not is_prime[r + 1]:
            continue
        p = r + 1
        high_prime_handoff = sum(mu[p * c] for c in range(1, r))
        assert high_prime_handoff == -mertens[r - 1], ("threshold handoff", r)
    assert mu[2] * mu[3] == 1
    assert mu[5] * mu[6] == -1
    assert mu[3] * mu[4] == 0
    assert abs(83 - 101) < 2 * 101 ** 0.5 and isqrt(83) != isqrt(101)
    print("PASS: genuine-mu shell, strict cutoffs, compensator, outer q reindex, "
          "threshold handoff, sign and approximate-window counterexamples")
    print("STATUS: FINITE INTEGER TEST ONLY. No signed moment or RH estimate.")


if __name__ == "__main__":
    main()
