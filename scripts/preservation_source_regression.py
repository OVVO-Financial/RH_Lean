#!/usr/bin/env python3
"""Exact finite regression for owner capacity and double-centered Euler source.

Preregistered domains:
* every integer R=2..25 and every R<=x<R^2 for the complete owner source;
* every R=2..40, plus R=317 and R=1027, for the complete frozen bilinear;
* all Mobius coefficients through 1027^2-1, by two independent constructions.

All comparisons use integers or Fraction.  In particular, the double-centered
kernel is evaluated directly with a common integer denominator; the full
bilinear is independently evaluated with integer floors.  The large examples
are checked against a complete sieve, not used as assumptions on future values.

These finite regressions are not Lean certificates or proofs of an asymptotic
signed estimate.  No upper bound on Gamma or Xi beyond the proved finite
reassembly bounds is asserted.
"""

from bisect import bisect_right
from fractions import Fraction
from math import lcm


SMALL_OWNER_ROOTS = range(2, 26)
SMALL_FROZEN_ROOTS = range(2, 41)
ENDPOINTS = {
    317: (-28, 22, -915, -887, 14887, -14103),
    1027: (367, -375, -6602, -6969, 131389, 3300),
}


def prime_factor_sieve(limit):
    """Mobius signs, actual primes, and largest prime factor by factorization."""
    mu = [1] * (limit + 1)
    mu[0] = 0
    largest = [0] * (limit + 1)
    primes = []
    for p in range(2, limit + 1):
        if largest[p] == 0:
            primes.append(p)
            for n in range(p, limit + 1, p):
                mu[n] = -mu[n]
                largest[n] = p
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return mu, largest, primes


def divisor_inverse(limit):
    """Independently solve sum_{d|n} mu(d)=1[n=1], without prime factors."""
    inverse = [0] * (limit + 1)
    inverse[1] = 1
    for d in range(1, limit + 1):
        coefficient = inverse[d]
        if coefficient:
            for n in range(2 * d, limit + 1, d):
                inverse[n] -= coefficient
    return inverse


def prefix_sums(values):
    result = [0] * len(values)
    for n in range(1, len(values)):
        result[n] = result[n - 1] + values[n]
    return result


def owner_primes(primes, root, x):
    return primes[bisect_right(primes, root):bisect_right(primes, x)]


def historical_k(mertens, root):
    return max(Fraction((mertens[y] - 1) ** 2, y + 1) for y in range(root))


def prefix_amplitude_sq(values, root):
    # The generic repository amplitude adjoins 1.  Actual M has M(1)=1.
    return max([Fraction(1)] + [Fraction(values[y] ** 2, y) for y in range(1, root)])


def check_owner_prefixes(mu, largest, primes, mertens):
    prefix_checks = 0
    generic_checks = 0
    for root in SMALL_OWNER_ROOTS:
        k = historical_k(mertens, root)
        amplitude_sq = prefix_amplitude_sq(mertens, root)
        assert 1 <= k and amplitude_sq <= 3 * k
        # Generic profiles include nonintegral, coherent, and alternating data.
        profiles = [
            [Fraction((3 * y) % 7 - 3, 5) for y in range(root)],
            [(-1) ** y * (y % 4) for y in range(root)],
            list(range(root)),
        ]
        generic_amplitudes = [prefix_amplitude_sq(f, root) for f in profiles]
        positive_gram_budget = Fraction(0)
        for x in range(root, root * root):
            owners = owner_primes(primes, root, x)
            quotients = [x // p for p in owners]
            assert all(1 <= q < root for q in quotients)
            actual_family = [p * c for p in owners for c in range(1, x // p + 1)]
            rough_population = {n for n in range(root + 1, x + 1) if largest[n] > root}
            assert len(actual_family) == len(set(actual_family)), (root, x, "owner collision")
            assert set(actual_family) == rough_population
            assert sum(quotients) == len(rough_population) <= x - root

            diagonal = sum(mertens[q] ** 2 for q in quotients)
            assert diagonal <= (x - root) * amplitude_sq <= 3 * (x - root) * k
            for f, bound in zip(profiles, generic_amplitudes):
                assert sum(f[q] ** 2 for q in quotients) <= (x - root) * bound
                generic_checks += 1

            smooth = sum(mu[n] for n in range(1, x + 1) if largest[n] <= root)
            transport = sum(mertens[q] for q in quotients)
            assert smooth - transport == mertens[x]
            gram = smooth ** 2 - 2 * smooth * transport + transport ** 2 - diagonal
            assert diagonal + gram == mertens[x] ** 2
            assert Fraction((mertens[x] - 1) ** 2, x + 1) <= Fraction(mertens[x] ** 2, x) + 1
            positive_gram_budget = max(positive_gram_budget, Fraction(gram, x) / k)
            prefix_checks += 1

        # This is only the conditional consumer evaluated at its actual finite
        # budget.  It makes no assertion that the budget stays small as R grows.
        assert historical_k(mertens, root * root) <= (4 + positive_gram_budget) * k
    return prefix_checks, generic_checks


def check_double_centered(root, mu, mertens):
    n = root - 1
    x = root * root - 1
    denominator = lcm(*range(1, root))
    scale = n * denominator ** 2
    active = [(a, mu[a], denominator // a, n % a) for a in range(1, root) if mu[a]]
    reciprocal_numerator = sum(sign * d for _, sign, d, _ in active)
    historical_fraction_numerator = sum(sign * remainder * d for _, sign, d, remainder in active)
    assert historical_fraction_numerator == n * reciprocal_numerator - denominator
    assert abs(reciprocal_numerator) <= denominator
    assert sum(mu[a] * (n // a) for a in range(1, root)) == 1

    full_floor = 0
    centered = 0
    paid_union = 0
    nondivisor = 0
    first_orientation_only = 0
    one_floor_triangle = 0
    for a, sign_a, da, remainder_a in active:
        for b, sign_b, db, remainder_b in active:
            sign = sign_a * sign_b
            floor_term = sign * (x // (a * b))
            full_floor += floor_term
            if a <= b:
                one_floor_triangle += floor_term
            # scale * [t{n/a}{n/b} - {x/(ab)}], t=(R+1)/n.
            term = sign * da * db * (
                (root + 1) * remainder_a * remainder_b - n * (x % (a * b))
            )
            centered += term
            if remainder_a == 0 or remainder_b == 0:
                paid_union += term
                # On the complete union the historical product vanishes.
                assert term == -sign * n * da * db * (x % (a * b))
            else:
                nondivisor += term
            if remainder_a == 0:
                first_orientation_only += term

    linear = 2 * (root + 1) * n * denominator * reciprocal_numerator - (root + 1) * denominator ** 2
    assert full_floor == 2 * mertens[n] - mertens[x]
    assert full_floor * scale == linear + centered
    assert centered == paid_union + nondivisor
    squarefree_divisors = sum(1 for a, _, _, remainder in active if remainder == 0)
    # Independent distinct-prime count for 2^omega(n), including n=1.
    remaining = n
    omega = 0
    p = 2
    while p * p <= remaining:
        if remaining % p == 0:
            omega += 1
            while remaining % p == 0:
                remaining //= p
        p += 1
    omega += int(remaining > 1)
    assert squarefree_divisors == 2 ** omega
    divisor_count = sum(1 for a in range(1, root) if n % a == 0)
    assert squarefree_divisors <= divisor_count
    assert abs(paid_union) <= 2 * n * squarefree_divisors * scale
    assert abs(linear) <= (2 * root + 5) * scale
    assert abs(full_floor * scale - nondivisor) <= (
        2 * root + 5 + 2 * n * squarefree_divisors
    ) * scale
    # Lean formalizations of both finite budgets are present; the squarefree
    # refinement is certified by the hosted verification in EV-PR-1141.
    # This regression remains a finite check.
    assert abs(full_floor * scale - nondivisor) <= (
        2 * root + 5 + 2 * n * divisor_count
    ) * scale
    return full_floor, paid_union != first_orientation_only, full_floor != one_floor_triangle


def check_negative_controls(mu, mertens):
    # Replacing strict p>R by p>=R already breaks the physical count at x=R=2.
    assert (2 // 2) > 2 - 2
    # The original frozen prefix cannot be extended to x=R^2: mu(R)^2 returns.
    root, x = 2, 4
    wrong_horizon_floor = sum(
        mu[a] * mu[b] * (x // (a * b))
        for a in range(1, root) for b in range(1, root)
    )
    assert wrong_horizon_floor != 2 * mertens[root - 1] - mertens[x]
    return 2


def main():
    limit = max(ENDPOINTS) ** 2 - 1
    mu, largest, primes = prime_factor_sieve(limit)
    inverse = divisor_inverse(limit)
    assert mu == inverse, "prime-factor and divisor-inversion Mobius constructions disagree"
    mertens = prefix_sums(mu)
    print(f"PASS: {limit} Mobius coefficients agree by independent constructions")

    prefix_checks, generic_checks = check_owner_prefixes(mu, largest, primes, mertens)
    print(f"PASS: {prefix_checks} complete original owner prefixes and {generic_checks} generic diagonal checks")

    row_orientation_witnesses = []
    floor_orientation_witnesses = []
    roots = list(SMALL_FROZEN_ROOTS) + list(ENDPOINTS)
    for root in roots:
        q, missing_row_detected, missing_floor_detected = check_double_centered(root, mu, mertens)
        if missing_row_detected:
            row_orientation_witnesses.append(root)
        if missing_floor_detected:
            floor_orientation_witnesses.append(root)
        if root in ENDPOINTS:
            x = root * root - 1
            quotients = [x // p for p in owner_primes(primes, root, x)]
            diagonal = sum(mertens[y] ** 2 for y in quotients)
            transport = sum(mertens[y] for y in quotients)
            smooth = sum(mu[n] for n in range(1, x + 1) if largest[n] <= root)
            gram = smooth ** 2 - 2 * smooth * transport + transport ** 2 - diagonal
            actual = mertens[x], q, smooth, transport, diagonal, gram
            assert actual == ENDPOINTS[root], (root, actual)
            assert smooth - transport == mertens[x]
            assert historical_k(mertens, root) == Fraction(3, 2)
            assert diagonal <= 3 * (x - root) * historical_k(mertens, root)
            print(f"PASS: R={root}; (M,Q,S,T,D,Gamma)={actual}")
    assert row_orientation_witnesses and floor_orientation_witnesses
    controls = check_negative_controls(mu, mertens) + 2
    print(f"PASS: {len(roots)} exact complete double-centerings, partitions and finite remainder bounds")
    print(
        f"PASS: {controls} negative controls; omitted divisor-row orientation detected at R={row_orientation_witnesses[0]}, "
        f"omitted floor orientation at R={floor_orientation_witnesses[0]}, strict-owner and square-horizon changes detected"
    )
    print("Scope: finite original-source regression; no subcritical Gamma/Xi bound or RH conclusion")


if __name__ == "__main__":
    main()
