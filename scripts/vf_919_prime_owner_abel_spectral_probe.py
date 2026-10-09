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


def test_unrestricted_dirichlet_vs_physical_cutoff():
    """Check the exact prime-zeta-square identity without conflating
    its INFINITE/UNRESTRICTED source with the physical pq < B^2 packet.
    This is a *finite identity test*, not Perron inversion.
    """
    a, b, maxp = 8, 17, 53
    flags = sieve(maxp)
    selected = [p for p in range(a + 1, maxp + 1) if flags[p]]
    s = complex(1.35, 0.41)

    def drich(n):
        return __import__("cmath").exp(-s * math.log(n))

    # Finite product identity: 1/2(P^2 - P(2s)) exactly
    # counts unordered p<q without a PHYSICAL CUTOFF.
    P = sum(drich(p) for p in selected)
    P2 = sum(drich(p * p) for p in selected)
    uncut = (P * P - P2) / 2
    uncut_pairs = sum(drich(p * q) for i, p in enumerate(selected)
                      for q in selected[i + 1:])
    assert abs(uncut - uncut_pairs) < 1e-12

    cut_pairs = [(p, q) for i, p in enumerate(selected)
                 for q in selected[i + 1:] if p * q < b * b]
    assert 0 < len(cut_pairs) < len(selected) * (len(selected) - 1) // 2
    Hcut = sum(drich(p * q) for p, q in cut_pairs)
    assert abs(Hcut - uncut) > 1e-7

    # The original strict OPEN square R bands form an EXACT, DISJOINT
    # partition on distinct-prime products; no half-weight square sites.
    cut_routed = 0.0
    cut_direct = 0.0
    for p, q in cut_pairs:
        n = p * q
        r = math.isqrt(n)
        assert a * a < n < b * b
        assert a <= r < b and r * r < n < (r + 1) ** 2
        cut_direct += original_weight(p, q)
        cut_routed += sum(original_weight(p, q) for R in range(a, b)
                          if R * R < n < (R + 1) * (R + 1))
    assert abs(cut_direct - cut_routed) < 1e-12
    print("PASS_FINITE_PRIME_ZETA_SQUARE_SOURCE "
          "A=%d B=%d primes_in_finite_dirichlet=%d "
          "uncut_pair_count=%d physical_cut_pair_count=%d "
          "exact_finite_dirichlet_error=%.3e "
          "original_weight_open_square_route_error=%.3e" %
          (a, b, len(selected), len(selected)*(len(selected)-1)//2,
           len(cut_pairs), abs(uncut-uncut_pairs),
           abs(cut_direct-cut_routed)))


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
    test_unrestricted_dirichlet_vs_physical_cutoff()
    main()
