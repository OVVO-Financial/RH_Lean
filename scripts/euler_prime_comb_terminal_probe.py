#!/usr/bin/env python3
"""Independent finite prime-comb feedback audit; no RH assertion.

Usage: python3 scripts/euler_prime_comb_terminal_probe.py \
           --roots 56 317 1000 --limit 1000000
Standard library only.
"""
import argparse
from array import array
from fractions import Fraction


def sieve(N):
    spf = array("I", [0]) * (N + 1)
    mu = array("b", [0]) * (N + 1)
    mu[1] = 1
    primes = []
    for n in range(2, N + 1):
        if spf[n] == 0:
            spf[n] = n
            mu[n] = -1
            primes.append(n)
        for p in primes:
            v = n * p
            if v > N or p > spf[n]:
                break
            spf[v] = p
            if p == spf[n]:
                mu[v] = 0
                break
            mu[v] = -mu[n]
    M = array("i", [0]) * (N + 1)
    largest_prime = array("I", [0]) * (N + 1)
    for n in range(1, N + 1):
        M[n] = M[n - 1] + mu[n]
        if n > 1:
            largest_prime[n] = max(spf[n], largest_prime[n // spf[n]])
    return spf, mu, M, largest_prime


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roots", type=int, nargs="+", default=[56, 317, 1000])
    parser.add_argument("--limit", type=int, default=1000000)
    args = parser.parse_args()
    if args.limit < 95 or not args.roots or min(args.roots) < 2:
        parser.error("limit must be >=95 and each root must be >=2")
    N = max(1000, args.limit, max(r * r - 1 for r in args.roots))
    spf, mu, M, largest_prime = sieve(N)
    assert M[100] == 1 and M[1000] == 2
    if N >= 1000000:
        assert M[1000000] == 212
    assert max(M[1:95]) == 1 and M[95] == 2

    for r in args.roots:
        X = r * r - 1
        # Independent construction of the prime-candidate field after
        # primes below r have acted (do not derive J from the updates).
        J = sum(
            0 if mu[n] == 0 else
            -mu[n] if largest_prime[n] >= r and largest_prime[n] != n else mu[n]
            for n in range(1, X + 1)
        )
        pos = neg = zero = active = total = 0
        for p in range(r, X // 2 + 1):
            if spf[p] != p:
                continue
            delta = 2 * (1 - M[X // p])
            total += delta
            active += 1
            if delta > 0:
                pos += 1
            elif delta < 0:
                neg += 1
            else:
                zero += 1
            # p > X/95 implies X/p <95 and M(floor(X/p)) <= 1.
            if 95 * p > X:
                assert delta >= 0
        assert J + total == M[X], (r, J, total, M[X])
        print("ROOT", r, "X", X, "J", J, "active", active,
              "positive", pos, "negative", neg, "zero", zero,
              "sum_updates", total, "M_X", M[X],
              "J_plus_4N", J + 4 * active,
              "updates_minus_4N", total - 4 * active)

    N = args.limit
    weights = {"positive": 0.0, "negative": 0.0, "zero": 0.0}
    mean = 0.0
    for k in range(2, N + 1):
        weight = 2.0 / (k * (k + 1))
        b = 1 - M[k]
        cls = "positive" if b > 0 else "negative" if b < 0 else "zero"
        weights[cls] += weight
        mean += 2 * b * weight
    print("LIMITING_SIGN_WEIGHTS_PREFIX", N,
          *(f"{cls}={weight:.10f}" for cls, weight in weights.items()),
          "per_class_tail_bound", 2.0 / (N + 1),
          "truncated_mean_step", round(mean, 10),
          "proven_mean_step_limit", 4)
    for cutoff in (2, 5, 20):
        left = sum(
            (Fraction(1 - M[k], k * (k + 1)) for k in range(2, cutoff + 1)),
            Fraction(),
        )
        right = (
            1 - sum((Fraction(mu[n], n) for n in range(1, cutoff + 1)), Fraction())
            + Fraction(M[cutoff] - 1, cutoff + 1)
        )
        assert left == right
    print("Finite harmonic identity verified exactly for N=2,5,20")


if __name__ == "__main__":
    main()
