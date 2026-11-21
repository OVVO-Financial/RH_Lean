#!/usr/bin/env python3
"""Alpoge prime-power Fourier -> genuine finite-C Mobius source regression.

Exact integer tests of the twisted local convolution on each prime fibre
before multiplying by log(p). Four quadratic channels are evaluated for
the small conductor 4*3*5. This is an illustrative character host, NOT
an automated verification of the concrete Frobenius choices in PR #1166.

No numerical sample implies an all-scale finite-A/C bound or RH.
"""
from __future__ import annotations

from math import sqrt


def mobius_spf(limit: int):
    mu = [0] * (limit + 1)
    spf = [0] * (limit + 1)
    primes = []
    mu[1] = 1
    for n in range(2, limit + 1):
        if spf[n] == 0:
            primes.append(n)
            spf[n] = n
            mu[n] = -1
        for p in primes:
            v = n * p
            if v > limit:
                break
            spf[v] = p
            if n % p == 0:
                mu[v] = 0
                break
            mu[v] = -mu[n]
    return mu, spf


def chi3(n: int):
    return 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)


def chi5(n: int):
    residue = n % 5
    return 0 if residue == 0 else (1 if residue in (1, 4) else -1)


def colours(n: int):
    a, b = chi5(n), chi3(n)
    return (1, a, b, a * b)


def factor(n: int, spf):
    ret = []
    while n > 1:
        p = spf[n]
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        ret.append((p, k))
    return ret


def test_primewise(mu, spf, test_limit: int):
    total = 0
    higher_power_checks = 0
    for n in range(2, test_limit + 1):
        target = tuple(-mu[n] * c for c in colours(n))
        for p, exponent in factor(n, spf):
            s = [0] * 4
            power = 1
            for k in range(1, exponent + 1):
                power *= p
                c_left = colours(n // power)
                c_right = colours(power)
                for j in range(4):
                    s[j] += mu[n // power] * c_left[j] * c_right[j]
                if k > 1:
                    higher_power_checks += 1
            assert tuple(s) == target, (
                f"primewise twisted Möbius/Λ coefficient failure: "
                f"n={n} p={p} actual={tuple(s)} target={target}"
            )
            total += 4
    return total, higher_power_checks


def test_two_walls(mu, limit: int, roots):
    pref = [[0] * (limit + 1) for _ in range(4)]
    for n in range(1, limit + 1):
        cs = colours(n)
        for j in range(4):
            pref[j][n] = pref[j][n - 1] + mu[n] * cs[j]

    summary = []
    for R in roots:
        X = R * R - 1
        K = max((pref[0][y] - 1) ** 2 / (y + 1) for y in range(R))
        q = [2 * pref[j][R - 1] - pref[j][X] for j in range(4)]
        for j in range(4):
            direct = sum(
                mu[n] * colours(n)[j] * (1 if n < R else -1)
                for n in range(1, X + 1)
            )
            assert direct == q[j]
        four = q[0] - q[1] + q[2] - q[3]
        summary.append((R, X, K, q, four, abs(q[0]) / (R * sqrt(K))))
    return summary


def main():
    roots = (10, 32, 56, 100, 317)
    limit = max(roots) ** 2 - 1
    mu, spf = mobius_spf(limit)
    total, high = test_primewise(mu, spf, 12000)
    summary = test_two_walls(mu, limit, roots)

    assert mu[3] * (1 + chi3(3) - chi5(3) - chi3(3) * chi5(3)) == -2
    assert mu[22] * (1 + chi3(22) - chi5(22) - chi3(22) * chi5(22)) == 4
    assert mu[30] * (1 + chi3(30) - chi5(30) - chi3(30) * chi5(30)) == -1
    assert summary[2][3][0] == -10 and summary[-1][3][0] == 22

    print(f"PASS exact primewise coefficient checks={total}, powers k>1={high}")
    print("R X K_R (Q0,Q5,Q3,Q15) fourColorQ |Q0|/(R sqrt(K_R))")
    for R, X, K, q, four, ratio in summary:
        print(f"{R} {X} {K:.5g} {tuple(q)} {four} {ratio:.6g}")
    print("PASS: four-colour ASK is positive at the prime-power level,")
    print("but the signed Mobius lift has both + and - coefficients.")
    print("NO uniform C and NO RH proof are inferred.")


if __name__ == "__main__":
    main()
