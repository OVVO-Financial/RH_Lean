#!/usr/bin/env python3
"""Exact-weight, genuine-prime owner/analytic Abel synthesis at A=2634.

No extrapolation to RH: finite actual p<q semiprimes for A<p<B<=2A,
with original w_floor(sqrt(p*q)) weight. Quantitative integral Li
increments use composite Simpson per integer segment. The Abel
identity itself is exact for ANY cumulative discrete reference.

What gets tested: whether individual genuine owner-column pi-Li
errors cancel after ORIGINAL physical weighting and reassembly.
They DO NOT in this test: nearly all p-column errors have one sign.
Do not invent a restoring signed payment from spectral input.
"""
import math

A, B = 2634, 5267
MAX = 4 * A


def sieve(n):
    flags = bytearray(b"\x01") * (n + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p :: p] = b"\x00" * ((n - p * p) // p + 1)
    return flags


def original_weight(p, q):
    r = math.isqrt(p * q)
    return (2 * r + 1) / (r * math.log(r * r + r + 0.5))


def main():
    primes = sieve(MAX)
    owners = [p for p in range(A + 1, B) if primes[p]]
    pi = [0] * (MAX + 1)
    li = [0.0] * (MAX + 1)
    for t in range(2, MAX + 1):
        pi[t] = pi[t - 1] + primes[t]
        if t > 2:
            k = t - 1
            li[t] = li[t - 1] + (
                1 / math.log(k) + 4 / math.log(k + 0.5) +
                1 / math.log(t)) / 6
    E = [pi[t] - li[t] for t in range(MAX + 1)]

    prime_charge = []
    analytic_charge = []
    abel_phases = []
    absolute_column_errors = []
    column_bounds = []
    degree = []
    for p in owners:
        upper = min(MAX, (B * B - 1) // p)
        assert p < upper < MAX
        degrees = sum(primes[p + 1 : upper + 1])
        degree.append(degrees)
        direct_prime, model_li, residual = [], [], []
        for q in range(p + 1, upper + 1):
            w = original_weight(p, q)
            dl = li[q] - li[q - 1]
            direct_prime.append(w * primes[q])
            model_li.append(w * dl)
            residual.append(w * (primes[q] - dl))
        actual = math.fsum(direct_prime)
        smooth = math.fsum(model_li)
        error = math.fsum(residual)
        assert abs((actual - smooth) - error) < 1e-9

        abel = (original_weight(p, upper) * E[upper] -
                original_weight(p, p) * E[p])
        abel += math.fsum(
            (original_weight(p, q) - original_weight(p, q + 1)) * E[q]
            for q in range(p, upper))
        assert abs(abel - error) < 1e-8, (p, abel, error)

        weights = (original_weight(p, q) for q in range(p, upper + 1))
        assert all(w > 0 for w in weights)
        max_error = max(abs(E[q]) for q in range(p, upper + 1))
        bound = 2 * original_weight(p, p) * max_error
        assert abs(error) <= bound + 1e-9

        prime_charge.append(actual)
        analytic_charge.append(smooth)
        abel_phases.append(abel)
        absolute_column_errors.append(abs(abel))
        column_bounds.append(bound)

    total_prime = math.fsum(prime_charge)
    total_model = math.fsum(analytic_charge)
    total_error = math.fsum(abel_phases)
    total_unsigned = math.fsum(absolute_column_errors)
    total_bound = math.fsum(column_bounds)
    negatives = sum(x < 0 for x in abel_phases)
    positives = sum(x > 0 for x in abel_phases)

    assert len(owners) == 316
    assert sum(degree) == 125272
    assert abs(total_prime - 14955.134569296933) < 1e-6
    assert abs(total_model - 15091.428261549745) < 1e-6
    assert abs(total_error + 136.2936922528104) < 1e-6
    assert negatives == 293 and positives == 23
    assert abs(total_unsigned - 140.78373545794858) < 1e-6
    assert abs(total_bound - 1588.123003336842) < 1e-4

    print("ACTUAL_7_8_OWNER_ABEL A=%d B=%d owners=%d "
          "semiprime_edges=%d true_weighted_charge=%.9f "
          "Li_weighted_reference=%.9f "
          "total_signed_prime_Li_error=%+.9f "
          "sum_abs_owner_errors=%.9f "
          "inter_owner_saving=%.6fx "
          "negative_owner_columns=%d positive_owner_columns=%d "
          "naive_local_Abel_bound=%.9f" % (
              A, B, len(owners), sum(degree),
              total_prime, total_model, total_error, total_unsigned,
              total_unsigned / abs(total_error),
              negatives, positives, total_bound))
    print("PASS: genuine prime-factor graph + original VF weight "
          "+ exact discrete signed Abel; no RH, no global sector-six claim.")


if __name__ == "__main__":
    main()
