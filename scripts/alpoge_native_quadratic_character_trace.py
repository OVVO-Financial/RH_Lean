#!/usr/bin/env python3
"""Actual two-quadratic-Dirichlet-character four-channel Euler source.

Characters on (Z/15Z)^* are lifted from primitive characters modulo 3
and modulo 5, with zero on every nonunit modulo 15. Sums include all
prime powers, as the von Mangoldt function requires. All calculations
are finite deterministic arithmetic, not RH asymptotics.
"""
import argparse
import json
import math

GAMMA = 0.5772156649015328606065120900824


def von_mangoldt_table(limit):
    prime = bytearray(b"\x01") * (limit + 1)
    prime[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    lam = [0.0] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            k = p
            while k <= limit:
                lam[k] = math.log(p)
                k *= p
    return lam


def chars15(n):
    if n % 3 == 0 or n % 5 == 0:
        return (0, 0)
    a = 1 if n % 3 == 1 else -1
    b = 1 if n % 5 in (1, 4) else -1
    return a, b


def audit(x, lam):
    N = math.floor(x)
    principal, twistedA, twistedB, twistedAB, selected, bad = (
        [] for _ in range(6)
    )
    selected_count = bad_count = 0
    for n in range(1, N + 1):
        if lam[n] == 0:
            continue
        w = lam[n] * (x / n - 1)
        a, b = chars15(n)
        proj = 1 + b - a - a * b
        assert proj in (0, 1, 4), (n, a, b, proj)
        principal.append(w)
        twistedA.append(w * a)
        twistedB.append(w * b)
        twistedAB.append(w * a * b)
        if a == -1 and b == 1:
            selected.append(w)
            selected_count += 1
        if a == 0 or b == 0:
            bad.append(w * proj)
            bad_count += 1
    p, a, b, ab, selected_mass, bad_mass = [
        math.fsum(v) for v in
        (principal, twistedA, twistedB, twistedAB, selected, bad)
    ]
    trace = math.fsum([p, b, -a, -ab])
    assert math.isclose(trace, 4 * selected_mass + bad_mass,
                        rel_tol=3e-12, abs_tol=1e-7)
    gz = p - x * math.log(x) + (1 + GAMMA) * x
    gsig = gz + b - a - ab
    assert math.isclose(gsig, trace - x * math.log(x) + (1 + GAMMA) * x,
                        rel_tol=3e-12, abs_tol=1e-7)
    return {
        "x": x, "prime_powers": sum(v != 0 for v in lam[1:N + 1]),
        "selected_prime_powers": selected_count,
        "ramified_prime_powers": bad_count,
        "trace": round(trace, 6),
        "selected_fourfold": round(4 * selected_mass, 6),
        "ramified_return": round(bad_mass, 6),
        "trace_nonnegative": trace >= -1e-7,
        "Gz": round(gz, 6),
        "Gsig_without_ell": round(gsig, 6)
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--x", type=float, nargs="+",
                        default=[101, 317.5, 1027, 10000, 100000])
    args = parser.parse_args()
    if min(args.x) < 1:
        parser.error("require x>=1")
    lam = von_mangoldt_table(math.floor(max(args.x)))
    print(json.dumps([audit(x, lam) for x in args.x], indent=2))


if __name__ == "__main__":
    main()
