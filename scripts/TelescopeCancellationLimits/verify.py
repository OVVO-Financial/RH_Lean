#!/usr/bin/env python3
"""Exact limits of the telescope-cancellation target.

Tests whether the exact roughness telescope

    M(x) = sum_{d | W} mu(d) T_W(floor(x/d))

can carry a signed-cancellation argument. Four checks, all exact:

1. Marginal information is insufficient — with only per-term bounds, the
   triangle inequality is optimal.
2. The telescope strictly worsens — the L1/target ratio is 1 at the empty wheel
   and increases monotonically with every prime added.
3. Regrouping collapses — pairing along any wheel prime returns the telescope
   for the smaller wheel.
4. Truncation fails — Brun-style truncation at omega(d) <= r leaves an error
   larger than the target at every depth short of full.

Exact integer arithmetic, standard library only.
"""

from fractions import Fraction as F
from math import gcd

LIMIT = 200000
PRIMORIAL = (1, 2, 6, 30, 210, 2310, 30030)


def mobius_sieve(n: int) -> list[int]:
    mu = [1] * (n + 1)
    primes: list[int] = []
    composite = [False] * (n + 1)
    for i in range(2, n + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            composite[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


MU = mobius_sieve(LIMIT)
_CACHE: dict[int, list[int]] = {}


def T(W: int, x: int) -> int:
    if x <= 0:
        return 0
    if W not in _CACHE:
        table = [0] * (LIMIT + 1)
        s = 0
        for n in range(1, LIMIT + 1):
            if gcd(n, W) == 1:
                s += MU[n]
            table[n] = s
        _CACHE[W] = table
    return _CACHE[W][x]


def divisors(n: int) -> list[int]:
    out = [1]
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            out = [d * e for d in out for e in (1, p)]
            m //= p
        p += 1
    if m > 1:
        out = [d * e for d in out for e in (1, m)]
    return sorted(out)


def omega(d: int) -> int:
    c, m, p = 0, d, 2
    while p * p <= m:
        if m % p == 0:
            c += 1
            while m % p == 0:
                m //= p
        p += 1
    return c + (1 if m > 1 else 0)


def check_telescope_identity() -> None:
    for k in range(1, 7):
        W = PRIMORIAL[k]
        ds = divisors(W)
        for x in (20000, 100000, 199999):
            assert T(1, x) == sum(MU[d] * T(W, x // d) for d in ds), (W, x)
    print("[0] exact telescope M(x) = sum_{d|W} mu(d) T_W(x/d) reconfirmed")


def check_marginal_no_go() -> None:
    """With only per-term bounds Phi_d, the bound sum_d Phi_d is attained."""
    for k in (3, 4, 5):
        W = PRIMORIAL[k]
        ds = divisors(W)
        x = 100000
        phi = [abs(T(W, x // d)) for d in ds]
        # the adversarial assignment t_d = mu(d) * Phi_d respects every bound
        adversarial = sum(MU[d] * (MU[d] * phi[i]) for i, d in enumerate(ds))
        assert adversarial == sum(phi), (W, adversarial, sum(phi))
    print("[1] marginal no-go: t_d = mu(d)*Phi_d meets every per-term bound and")
    print("    attains sum_d Phi_d, so the triangle inequality is OPTIMAL among")
    print("    arguments using per-term bounds only.  Joint information is required.")


def check_monotone_worsening() -> None:
    print("[2] L1 / |M(x)| as primes are added to the wheel:")
    for x in (20000, 100000, 199999):
        target = abs(T(1, x))
        ratios = []
        for k in range(0, 7):
            W = PRIMORIAL[k]
            l1 = sum(abs(T(W, x // d)) for d in divisors(W))
            ratios.append(F(l1, max(1, target)))
        assert ratios[0] == 1
        assert all(ratios[i] <= ratios[i + 1] for i in range(6)), ratios
        pretty = "  ".join(f"k={k}:{float(r):.1f}x" for k, r in enumerate(ratios))
        print(f"      x={x:>6} |M|={target:>3}:  {pretty}")
    print("    ratio is exactly 1 at the EMPTY wheel and monotone increasing:")
    print("    the telescope strictly worsens the cancellation that must be proved.")


def check_regrouping_collapses() -> None:
    for W, p in ((30, 5), (210, 7), (2310, 11), (30030, 13)):
        Wp = W // p
        for x in (5000, 50000, 199999):
            paired = sum(MU[d] * (T(W, x // d) - T(W, x // (p * d))) for d in divisors(Wp))
            smaller = sum(MU[d] * T(Wp, x // d) for d in divisors(Wp))
            assert paired == smaller == T(1, x), (W, p, x)
    print("[3] regrouping collapse: pairing d with p*d along any wheel prime returns")
    print("    the telescope for W/p.  The expansion is exactly invertible, so no")
    print("    grouping of terms extracts information.")


def check_truncation_fails() -> None:
    print("[4] Brun-style truncation at omega(d) <= r (W = 210, x = 100000, M = -48):")
    W, x = 210, 100000
    ds = divisors(W)
    target = T(1, x)
    errors = []
    for r in range(0, 5):
        part = sum(MU[d] * T(W, x // d) for d in ds if omega(d) <= r)
        err = abs(part - target)
        errors.append(err)
        print(f"      r={r}: partial sum {part:>6}   error {err:>5}")
    assert errors[-1] == 0
    assert min(errors[:-1]) > abs(target), errors
    print("    partial sums oscillate and every truncation short of full depth is off")
    print("    by more than the target itself: the cancellation is entirely last-mile.")


def main() -> None:
    check_telescope_identity()
    check_marginal_no_go()
    check_monotone_worsening()
    check_regrouping_collapses()
    check_truncation_fails()
    print()
    print("CONCLUSION: the telescope is an exactly invertible re-expression of M.")
    print("Per-term bounds cannot beat the triangle inequality; the triangle bound")
    print("strictly worsens with every prime added; regrouping collapses it; and")
    print("truncation leaves an error larger than the target.  The telescope-")
    print("cancellation formulation of obligation A is NOT a viable target.")
    print()
    print("ALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
