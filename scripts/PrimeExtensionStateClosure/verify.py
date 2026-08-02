#!/usr/bin/env python3
"""Exact verifier for the prime-extension state-closure results.

Establishes that a genuinely closed induction state exists — the scale-indexed
rough summatory function `T_W` — and that having it does not advance the
program, for two independently sufficient reasons.

Sections
--------
1. One-step transfer      T_pW(x) = T_W(x) + T_pW(floor(x/p)).
2. Geometric transfer     T_pW(x) = sum_{j>=0} T_W(floor(x/p^j)).
3. Exact telescope        M(x) = sum_{d|W} mu(d) T_W(floor(x/d)).
4. Descent loss           |M(x)| <= 2^k sup|T_{W_k}|, with the 2^k blowup measured.
5. Base case              T_{W_k}(y) = 1 + k - pi(y) for p_k < y < p_{k+1}^2.

Exact integer arithmetic, standard library only.
"""

from math import gcd

LIMIT = 40000
PRIMES = (2, 3, 5, 7, 11, 13)


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
    """The rough summatory function T_W(x), tabulated once per wheel."""
    if W not in _CACHE:
        table = [0] * (LIMIT + 1)
        s = 0
        for n in range(1, LIMIT + 1):
            if gcd(n, W) == 1:
                s += MU[n]
            table[n] = s
        _CACHE[W] = table
    assert 0 <= x <= LIMIT
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


def primorial(k: int) -> int:
    w = 1
    for p in PRIMES[:k]:
        w *= p
    return w


def section_1_and_2() -> None:
    pairs = ((6, 5), (30, 7), (210, 11), (2310, 13))
    for W, p in pairs:
        for x in range(0, 400):
            assert T(p * W, x) == T(W, x) + T(p * W, x // p), (W, p, x)
        for x in (0, 1, 7, 50, 113, 500, 1000, 2311, 9999, 30011):
            total, y = 0, x
            while y > 0:
                total += T(W, y)
                y //= p
            assert T(p * W, x) == total, (W, p, x)
    print("[1] one-step transfer  T_pW(x) = T_W(x) + T_pW(x/p)   verified "
          "for 4 wheel/prime pairs, all x < 400")
    print("[2] geometric transfer T_pW(x) = sum_j T_W(x/p^j)     verified "
          "at scales up to 30011")


def section_3() -> None:
    for W in (6, 30, 210, 2310):
        ds = divisors(W)
        for x in (100, 997, 5000, 20000, 40000):
            assert T(1, x) == sum(MU[d] * T(W, x // d) for d in ds), (W, x)
    print("[3] exact telescope    M(x) = sum_{d|W} mu(d) T_W(x/d)  verified "
          "for W = 6, 30, 210, 2310")


def section_4() -> None:
    x = 20000
    target = abs(T(1, x))
    rows = []
    for k in (2, 3, 4, 5):
        W = primorial(k)
        sup = max(abs(T(W, y)) for y in range(1, x + 1))
        rows.append((W, k, sup, (1 << k) * sup))
        assert target <= (1 << k) * sup
    print(f"[4] descent loss  |M({x})| = {target}  <=  2^k sup|T_W|:")
    for W, k, sup, bound in rows:
        print(f"      W = {W:>5}  k = {k}  sup = {sup:>4}  2^k sup = {bound:>6}  "
              f"slack {bound // max(1, target):>4}x")
    slacks = [b // max(1, target) for _, _, _, b in rows]
    assert slacks == sorted(slacks) and slacks[-1] > 20 * slacks[0] // 2
    print("[4] the slack grows geometrically: the generic descent loses a factor 2")
    print("    per prime, so a useful descent needs signed cancellation, not bounds")


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def section_5() -> None:
    pi_table = [0] * (LIMIT + 1)
    c = 0
    for n in range(2, LIMIT + 1):
        if is_prime(n) if n < 4000 else False:
            c += 1
        pi_table[n] = c
    for k in range(1, 6):
        W = primorial(k)
        pk = PRIMES[k - 1]
        hi = min(PRIMES[k] ** 2 - 1, 3999)
        for y in range(pk + 1, hi + 1):
            assert T(W, y) == 1 + k - pi_table[y], (k, y, T(W, y), pi_table[y])
        print(f"[5] k = {k}  W = {W:>5}:  T_W(y) = 1 + k - pi(y) verified on "
              f"({pk}, {hi}]")
    print("[5] the base of the closed induction is a prime-counting statement;")
    print("    at RH strength it IS the conclusion")


def main() -> None:
    section_1_and_2()
    section_3()
    section_4()
    section_5()
    print("\nCONCLUSION: a closed prime-extension state exists (the scale-indexed")
    print("T_W), so state closure is NOT the bottleneck.  The obstruction is the")
    print("2^k descent loss and an RH-equivalent base case - i.e. cancellation.")
    print("\nALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
