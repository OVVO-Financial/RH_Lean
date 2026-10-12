#!/usr/bin/env python3
"""Exact arithmetic for live odd-Mobius pair signs at fixed ancestor cutoffs.

The physical signed pair Gamma_x admits the UNIQUE gcd normalization
(m,n)=(g*a,g*b), 1<=a<b<2a, gcd(a,b)=gcd(g,a*b)=1,
where a,b,g are odd squarefree and sign(mu(m)*mu(n))=mu(a)*mu(b).

For FIXED cutoff T, gamma_{g>x/T}(x) = (pi2_c[T]/pi**2)*x + O_T(sqrt(x)).
pi2_c[T] is a FINITE RATIONAL NUMBER computed exactly here; not an
RH hypothesis, statistical assumption or all-ancestor estimate.

Usage: python3 experiments/PrimePopulationCutoff/gcd_live_cutoff_rational.py
"""
from fractions import Fraction
from math import gcd, pi


def mobius_sieve(n):
    lp = [0] * (n + 1)
    mu = [0] * (n + 1)
    mu[1] = 1
    primes = []
    for m in range(2, n + 1):
        if not lp[m]:
            lp[m] = m
            mu[m] = -1
            primes.append(m)
        for p in primes:
            v = m * p
            if v > n or p > lp[m]:
                break
            lp[v] = p
            if m % p == 0:
                mu[v] = 0
                break
            mu[v] = -mu[m]
    return mu


def factor_h(n):
    """For n <= small fixed cutoff: h(n) = product_{p|n} p/(p+1)."""
    lp = [0] * (n + 1)
    ps = []
    h = [Fraction(1)] * (n + 1)
    for m in range(2, n + 1):
        if not lp[m]:
            lp[m] = m
            ps.append(m)
            h[m] = Fraction(m, m + 1)
        for p in ps:
            v = m * p
            if v > n or p > lp[m]:
                break
            lp[v] = p
            if m % p == 0:
                h[v] = h[m]
                break
            h[v] = h[m] * Fraction(p, p + 1)
    return h


def signed_cofactors(t, mu):
    for b in range(3, t, 2):
        if not mu[b]:
            continue
        for a in range(b // 2 + 1, b):
            if a % 2 == 0 or not mu[a] or gcd(a, b) != 1:
                continue
            yield a, b, mu[a] * mu[b]


def exact_pi2_coefficient(t, mu, h):
    """Returns pi**2 times asymptotic Gamma_{g>x/t}(x)/x, exactly."""
    ans = Fraction(0)
    terms = 0
    for a, b, sign in signed_cofactors(t, mu):
        # Fixed (a,b): gcd-normalized g must satisfy
        # x*max(1/(2a),1/t) < g <= x/b.
        width = Fraction(1, b) - max(Fraction(1, 2 * a), Fraction(1, t))
        assert width > 0
        # Density squarefree g coprime 2ab is (4/pi^2)*h(a)*h(b).
        ans += 4 * sign * h[a] * h[b] * width
        terms += 1
    return ans, terms


def physical_gamma_cutoff(x, t, mu):
    """Genuine finite x, integer exact: gcd-normalized count with true mu."""
    total, positive, negative = 0, 0, 0
    for a, b, sign in signed_cofactors(t, mu):
        lo = max(x // (2 * a), x // t) + 1
        hi = x // b
        for g in range(lo, hi + 1):
            if mu[g] != 0 and gcd(g, 2 * a * b) == 1:
                total += sign
                if sign > 0:
                    positive += 1
                else:
                    negative += 1
    return total, positive, negative


def main():
    cutoffs = (6, 15, 300, 500)
    small_mu = mobius_sieve(max(cutoffs))
    h = factor_h(max(cutoffs))
    print("Universal fixed-cutoff density coefficient: (pi2_c / pi^2) * x")
    coeffs = {}
    for t in cutoffs:
        val, count = exact_pi2_coefficient(t, small_mu, h)
        coeffs[t] = val
        print(f"T={t}: cofactor_pairs={count}, sign={'+' if val > 0 else '-'}, "
              f"pi2_c≈{float(val):+.12f}, c≈{float(val) / pi**2:+.12f}")

    assert coeffs[6] == Fraction(1, 12)
    assert coeffs[15] == Fraction(233, 720)
    assert coeffs[300] > 0
    assert coeffs[500] < -Fraction(9, 50)  # EXACT strict rational certificate
    print("CERTIFIED: pi^2 * c_500 < -9/50, while pi^2 * c_15 = 233/720")
    print("CERTIFIED: for sufficiently large x, the intermediate "
          "x/500 < gcd <= x/15 signed interaction is strictly negative.")

    xs = (317, 2808, 3135, 100488, 999999)
    mu = mobius_sieve(max(xs))
    for x in xs:
        for t in (15, 500):
            total, pos, neg = physical_gamma_cutoff(x, t, mu)
            print(f"x={x}, T={t}, true signed={total}, "
                  f"positive_pairs={pos}, negative_pairs={neg}, ratio={total / x:+.9f}")
    print("Finite values are checks only: no all-x finite A/C bound is asserted.")


if __name__ == "__main__":
    main()
