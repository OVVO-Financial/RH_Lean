#!/usr/bin/env python3
"""Exact integer regression: frozen Mobius cofactors vs moving real primes.

No independence model, approximate prime density, or assumed OAI moment.
The OAI-facing arithmetic lift uses a_F = mu * (chi_-3 pointwise mu),
the prime-to-six norm mask, and FULL 3/4/12 restoring terms.
The cutoff p>R matches the repository's non-strict root wheel y=R.
The p=R prime branch is checked separately.
"""
from __future__ import annotations

import argparse
import math


def arithmetic_tables(limit: int):
    least = [0] * (limit + 1)
    largest = [1] * (limit + 1)
    mob = [0] * (limit + 1)
    mob[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if not least[n]:
            least[n] = n
            primes.append(n)
            mob[n] = -1
        for p in primes:
            k = n * p
            if k > limit or p > least[n]:
                break
            least[k] = p
            if n % p == 0:
                mob[k] = 0
                break
            mob[k] = -mob[n]
    pi = [0] * (limit + 1)
    mertens = [0] * (limit + 1)
    for n in range(1, limit + 1):
        pi[n] = pi[n - 1] + (least[n] == n and n >= 2)
        mertens[n] = mertens[n - 1] + mob[n]
        if n >= 2:
            largest[n] = max(least[n], largest[n // least[n]])
    return least, largest, mob, pi, mertens, primes


def chi3(n: int) -> int:
    return 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)


def eisenstein_norm_coefficients(mob: list[int], max_c: int):
    a_f = [0] * (max_c + 1)
    for u in range(1, max_c + 1):
        if not mob[u]:
            continue
        for v in range(1, max_c // u + 1):
            a_f[u * v] += mob[u] * chi3(v) * mob[v]
    return a_f


def verify_root(R, least, largest, mob, pi, mertens, primes, a_f):
    X = R * R - 1

    # The genuine post-root prime response, a weight on FIXED c < R.
    def weight(c):
        return pi[X // c] - pi[R] if 0 < c < R else 0

    response = sum(mob[c] * weight(c) for c in range(1, R))
    pi_tail = sum(mertens[X // p] for p in primes if R < p <= X)
    assert response == pi_tail, (R, response, pi_tail)

    # Full quadratic character/ideal-norm convolution (NO rational-norm dedup).
    chi_lift = 0
    for c in range(1, R):
        at_c = sum(chi3(d) * a_f[c // d] for d in range(1, c + 1) if c % d == 0)
        assert at_c == mob[c], (R, c, at_c, mob[c])
        chi_lift += at_c * weight(c)
    assert chi_lift == response, (R, chi_lift, response)

    # Exact excluded-norm transport with complete 3,4,12 restoration.
    hecke_source = 0
    for m in range(1, R):
        if math.gcd(m, 6) != 1:
            continue
        inner = 0
        for d in range(1, (R - 1) // m + 1):
            md = m * d
            inner += chi3(d) * (
                weight(md) - weight(3 * md) - weight(4 * md) + weight(12 * md)
            )
        hecke_source += a_f[m] * inner
    assert hecke_source == response, (R, hecke_source, response)

    # Direct smooth mass independently enumerated at every physical integer.
    smooth_positive = smooth_negative = 0
    for n in range(1, X + 1):
        if largest[n] <= R:
            smooth_positive += mob[n] == 1
            smooth_negative += mob[n] == -1
    smooth = smooth_positive - smooth_negative
    assert smooth - pi_tail == mertens[X], (R, smooth, pi_tail, mertens[X])

    # Complete NNS Co/Div, retaining every smooth x high cross pair.
    high_positive = sum(weight(c) for c in range(1, R) if mob[c] == -1)
    high_negative = sum(weight(c) for c in range(1, R) if mob[c] == 1)
    assert high_positive - high_negative == -response
    assert (smooth_positive + high_positive) - (
        smooth_negative + high_negative
    ) == mertens[X]
    cross_codiv = (
        smooth_positive * high_positive
        + smooth_negative * high_negative
        - smooth_positive * high_negative
        - smooth_negative * high_positive
    )
    assert cross_codiv == -smooth * response
    assert smooth * smooth + response * response - 2 * smooth * response == mertens[X] ** 2

    # At a PRIME root the strict historical split p>=R transfers exactly
    # M(R-1) from the smooth side to the high-prime response. Neither is
    # the much larger low-prime animation population.
    singleton = mertens[R - 1] if least[R] == R else 0
    strict_smooth = sum(mob[n] for n in range(1, X + 1) if largest[n] < R)
    strict_response = sum(mertens[X // p] for p in primes if R <= p <= X)
    assert strict_smooth == smooth + singleton
    assert strict_response == response + singleton
    assert strict_smooth - strict_response == mertens[X]
    if R in (317, 1027):
        print(
            f"R={R} X={X} smooth<=R={smooth} p>R response={response} "
            f"smooth<R={strict_smooth} p>=R response={strict_response} "
            f"M={mertens[X]} crossCoDiv={cross_codiv} "
            f"heckeLift={hecke_source}"
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-root", type=int, default=1027)
    args = parser.parse_args()
    root = args.max_root
    if root < 4:
        parser.error("max-root must be >= 4")
    least, largest, mob, pi, mertens, primes = arithmetic_tables(root * root - 1)
    a_f = eisenstein_norm_coefficients(mob, root)
    candidates = sorted(set(range(4, min(root, 70) + 1)) | {n for n in (97, 101, 317, 1027) if n <= root})
    for R in candidates:
        verify_root(R, least, largest, mob, pi, mertens, primes, a_f)
    print(
        f"PASS: {len(candidates)} true integer square roots; frozen-cofactor "
        f"prime response, 3/4/12 restored Hecke lift, full NNS cross CoDiv, "
        f"strict-root prime singleton transfer; no stochastic inputs"
    )


if __name__ == "__main__":
    main()
