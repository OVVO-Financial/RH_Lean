#!/usr/bin/env python3
"""Genuine Mobius source: test root-phase harmonic cross terms.

The exact theta-Parseval identity has no independent-sign premise.
The k-harmonic diagonal, with |c_k|^2~1/k^2, omits signed
cross terms and is NOT automatically the original shell energy.

Uses only the standard library. The midpoint theta grid integrates
the original trigonometric polynomial exactly (up to rounding) when
Ntheta>=H. The finite harmonic expansion is an approximation.
"""
import cmath
import math


def mobius_upto(nmax):
    mu = [1] * (nmax + 1)
    prime = [True] * (nmax + 1)
    prime[0] = prime[1] = False
    for p in range(2, nmax + 1):
        if not prime[p]:
            continue
        for n in range(p, nmax + 1, p):
            mu[n] *= -1
        if p * p <= nmax:
            for n in range(p * p, nmax + 1, p * p):
                mu[n] = 0
            for n in range(p * p, nmax + 1, p):
                prime[n] = False
    return mu


def run(H=8, K=64, ntheta=64):
    assert H >= 2 and K > 0 and ntheta >= H
    mu = mobius_upto(4 * H * H)
    terms = [
        (math.sqrt(n), math.isqrt(n), mu[n])
        for n in range(H * H, 4 * H * H) if mu[n]
    ]
    assert all(int(root) != root for root, _, _ in terms)
    shells = [
        sum(mu[n] for n in range(R * R, (R + 1) * (R + 1)))
        for R in range(H, 2 * H)
    ]
    true_energy = sum(x * x for x in shells)
    exact_quad = diagonal_quad = complete_quad = 0.0
    for j in range(ntheta):
        theta = (j + 0.5) / ntheta
        exact = sum(
            a * cmath.exp(2j * math.pi * theta * R)
            for _, R, a in terms
        )
        exact_quad += abs(exact) ** 2
        complete = 0j
        for k in range(-K, K + 1):
            ck = ((1 - cmath.exp(-2j * math.pi * theta)) /
                  (2j * math.pi * (theta + k)))
            smooth = sum(
                a * cmath.exp(2j * math.pi * (theta + k) * root)
                for root, _, a in terms
            )
            term = ck * smooth
            complete += term
            diagonal_quad += abs(term) ** 2
        complete_quad += abs(complete) ** 2
    exact_quad /= ntheta
    diagonal_quad /= ntheta
    complete_quad /= ntheta
    mixed = complete_quad - diagonal_quad
    assert abs(exact_quad - true_energy) < 1e-8
    assert abs(mixed) > 1.0
    print(f"H={H} K={K} theta_samples={ntheta}")
    print(f"true_sharp_energy={true_energy}")
    print(f"finite_harmonic_energy={complete_quad:.6f}")
    print(f"harmonic_diagonal_energy={diagonal_quad:.6f}")
    print(f"SIGNED_MIXED_HARMONICS={mixed:.6f}")
    print("PASS: real Mobius square-root harmonics have nonzero cross energy")


if __name__ == "__main__":
    run()
