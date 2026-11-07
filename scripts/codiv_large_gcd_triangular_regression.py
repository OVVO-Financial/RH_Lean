"""Exact original-pair and lattice checks for the CODIV large-gcd bound."""

from fractions import Fraction
from math import gcd


def mu(n):
    if n == 0:
        return 0
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def check(X, h, G):
    pairs = [(d, n) for d in range(1, h) for n in range(X, 4 * X)
             if gcd(n, d) >= G]
    coordinates = [(gcd(n, d), d // gcd(n, d), n // gcd(n, d))
                   for d, n in pairs]
    assert len(coordinates) == len(set(coordinates))
    assert all((g * k, g * m) == p
               for p, (g, k, m) in zip(pairs, coordinates))
    assert all(G <= g < h and 1 <= k <= h // g
               and 1 <= m <= 4 * X // g for g, k, m in coordinates)
    signed = sum(2 * (h - d) * mu(n) * mu(n + d) for d, n in pairs)
    support = sum(2 * (h - d) * mu(n)**2 * mu(n + d)**2
                  for d, n in pairs)
    geometry = sum(2 * (h - d) for d, _ in pairs)
    lattice = sum(2 * (h - g * k) * (4 * X // g)
                  for g in range(G, h) for k in range(1, h // g + 1))
    tail = sum((Fraction(1, g * g) for g in range(G, h)), Fraction(0))
    assert abs(signed) <= support <= geometry <= lattice
    assert lattice <= 4 * X * h * h * tail
    assert tail <= Fraction(1, G - 1) - Fraction(1, h - 1)
    assert support <= Fraction(4 * X * h * h, G - 1)
    assert support <= Fraction(8 * X * h * h, G)
    for d, n in pairs:
        g = gcd(n, d)
        m, k = n // g, d // g
        assert gcd(m, k) == 1
        masked = mu(g)**2 * mu(m) * mu(m + k)
        if gcd(g, m * (m + k)) != 1:
            masked = 0
        assert mu(n) * mu(n + d) == masked
    return signed, support, any(n + d >= 4 * X for d, n in pairs)


def main():
    count = extended = empty = 0
    halo_seen = False
    for X in range(1, 33):
        for h in range(2, 19):
            for G in range(2, h + 1):
                signed, support, halo = check(X, h, G)
                count += 1
                extended += h > X
                halo_seen |= halo
                if G == h:
                    assert signed == support == 0
                    empty += 1
    for fixture in [(225, 6, 5), (1764, 12, 9), (49, 17, 2),
                    (1, 41, 2), (2, 64, 3), (4096, 16, 12)]:
        print(f"fixture {fixture}: {check(*fixture)[:2]}")
    assert check(225, 6, 5)[0] == 16
    assert check(1764, 12, 9)[0] == -16
    assert halo_seen
    print(f"PASS: {count} original/lattice cases, {extended} with h>X, "
          f"{empty} empty-cutoff cases; full forward halo retained")
    print("PASS: both signs occur; no favorable-covariance assertion")


if __name__ == "__main__":
    main()
