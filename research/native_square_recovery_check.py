#!/usr/bin/env python3
"""Independent finite diagnostics for the native square recovery/cost work.

Uses an integer sieve, exact rational kernel weights, and separately computed
von Mangoldt entries. Numerical logarithmic Gz values are diagnostics only;
they are not interval certificates or evidence of an all-scale estimate.
Run from any directory with Python 3: python research/native_square_recovery_check.py
"""

from array import array
from fractions import Fraction
from math import fsum, isqrt, log


def arithmetic(limit):
    least = array("I", [0]) * (limit + 1)
    mobius = array("b", [0]) * (limit + 1)
    mobius[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if least[n] == 0:
            least[n] = n
            primes.append(n)
            mobius[n] = -1
        for p in primes:
            product = p * n
            if product > limit:
                break
            least[product] = p
            if p == least[n]:
                break
            mobius[product] = -mobius[n]
    mangoldt = array("d", [0]) * (limit + 1)
    for p in primes:
        power = p
        while power <= limit:
            mangoldt[power] = log(p)
            power *= p
    return least, mobius, mangoldt


def check_recovery(radius, least, mobius):
    cutoff = max(3, radius // 2 + 1)
    endpoint = (radius + 1) ** 2
    survivors = [n for n in range(radius**2 + 1, endpoint) if least[n] > cutoff]
    primes = [n for n in survivors if least[n] == n]
    composites = [n for n in survivors if least[n] != n]
    assert all(mobius[n] == 1 for n in composites)
    for weight in (lambda n: n, lambda n: Fraction(endpoint, n) - 1):
        total = sum(weight(n) for n in survivors)
        signed = sum(mobius[n] * weight(n) for n in survivors)
        prime = sum(weight(n) for n in primes)
        removed = sum(weight(n) for n in composites)
        assert total - signed == 2 * prime
        assert total + signed == 2 * removed
        assert total**2 + signed**2 == 2 * (prime**2 + removed**2)
    return radius, cutoff, len(primes), len(composites)


def check_completed_capacity(radius, least, mangoldt):
    endpoint = radius**2 - 1
    candidates = [n for n in range(2, endpoint + 1) if least[n] > isqrt(n) // 2]
    composites = [n for n in candidates if least[n] != n]
    proper = fsum(
        mangoldt[n] * (endpoint / n - 1)
        for n in range(2, endpoint + 1) if least[n] != n
    )
    capacity = fsum(log(n) * (endpoint / n - 1) for n in candidates)
    removal = fsum(log(n) * (endpoint / n - 1) for n in composites)
    complete = fsum(mangoldt[n] * (endpoint / n - 1) for n in range(2, endpoint + 1))
    relative_error = (capacity - removal + proper - complete) / max(1, abs(complete))
    assert abs(relative_error) < 1e-12
    assert proper >= log(2) * endpoint / 8
    gamma = 0.5772156649015328606
    gz = complete - endpoint * log(endpoint) + (1 + gamma) * endpoint
    return radius, endpoint, len(candidates), len(composites), proper / endpoint, gz, relative_error


def main():
    radii = (3, 5, 317, 549, 1027)
    least, mobius, mangoldt = arithmetic((max(radii) + 1) ** 2)
    print("Exact rational recovery and energy checks: R A primes composites")
    for radius in radii:
        print(*check_recovery(radius, least, mobius))
    print("Floating-point completed-capacity diagnostics: R N candidates composites PP/N Gz residual")
    for radius in (317, 549, 1027):
        row = check_completed_capacity(radius, least, mangoldt)
        print(*row[:4], f"{row[4]:.9f}", f"{row[5]:.9f}", f"{row[6]:.3e}")
    print("PASS finite diagnostics; no asymptotic claim.")


if __name__ == "__main__":
    main()
