#!/usr/bin/env python3
"""Finite genuine-prime and Moebius audit of #974 vs original #915 VF source.

This is a diagnostic ONLY. The signed three-boundary residual is computed as
E - G using the existing identity, not by independently enumerating every
returned boundary raw parent; no all-R sign or descendant estimate is claimed.
"""
import math

ROOTS = (8, 18, 32, 56, 317, 1027)


def sieve(n):
    spf = [0] * (n + 1)
    mu = [0] * (n + 1)
    mu[1] = 1
    primes = []
    for x in range(2, n + 1):
        if not spf[x]:
            spf[x] = x
            mu[x] = -1
            primes.append(x)
        for p in primes:
            y = x * p
            if y > n:
                break
            spf[y] = p
            if x % p == 0:
                mu[y] = 0
                break
            mu[y] = -mu[x]
    pi = [0] * (n + 1)
    for i in range(2, n + 1):
        pi[i] = pi[i - 1] + (spf[i] == i)
    return spf, mu, pi


def highest_prime(x, spf):
    highest = 0
    while x > 1:
        p = spf[x]
        highest = max(highest, p)
        x //= p
    return highest


def vf_mass(r):
    return (2 * r + 1) / math.log(r * r + r + 0.5)


def check(R, spf, mu, pi):
    a = R // 2 + 1
    assert a * a > R
    low, upper = R * R, (R + 1) ** 2
    odd = [n for n in range(low + 1, upper) if n & 1]
    assert len(odd) == R
    w = vf_mass(R) / R
    assert 0 < w < 1
    P = pi[upper] - pi[low]
    assert sum(spf[n] == n for n in odd) == P
    vf_finished = sum(vf_mass(r) for r in range(2, R))
    D = pi[low] - vf_finished
    Dnext = pi[upper] - vf_finished - vf_mass(R)
    full_charges = [(w - 1 if spf[n] == n else w) for n in odd]
    active = [(w - 1 if spf[n] == n else w)
              for n in odd if mu[n] != 0]
    Q = w * sum(mu[n] == 0 for n in odd)
    assert math.isclose(sum(full_charges), vf_mass(R) - P, abs_tol=2e-9)
    X, tabsmass, diag = sum(active), sum(map(abs, active)), sum(z*z for z in active)
    absfull = sum(map(abs, full_charges))
    assert math.isclose(absfull, tabsmass + Q, abs_tol=1e-9)
    assert math.isclose(Dnext, D - X - Q, abs_tol=1e-8)

    # ORIGINAL anchored Co/Div, with historical D compressed ONCE.
    E = 2 * Dnext * Dnext - (abs(D) + absfull) ** 2

    # Exact global non-cell root / diagonal / squareful source residual.
    demand = (2 * (D*D - 2*D*X) + 2*diag
              - 2*Q*(2*Dnext + Q))
    capacity = (D*D + 2*abs(D)*tabsmass + diag
                + Q*(2*(abs(D)+tabsmass)+Q))
    G = demand - capacity
    boundary_excess = E - G  # Existing Fubini identity, NOT a bound.

    smooth, low_cofactor_transport = 0, 0
    for n in range(low, upper):
        p = highest_prime(n, spf)
        if p > R:
            c = n // p
            assert 1 <= c <= R < a * a
            assert not (a*a <= c < upper)
            assert mu[n] == -mu[c]
            low_cofactor_transport += mu[c]
        else:
            smooth += mu[n]
    increment = sum(mu[low:upper])
    assert increment == smooth - low_cofactor_transport
    assert math.isclose(E, G + boundary_excess, abs_tol=1e-8)
    print(f'{R:4d} A={a:4d} primes={P:3d} w={w:.6f} '
          f'D={D:10.5f} E={E:14.5f} G={G:14.5f} '
          f'boundary={boundary_excess:14.5f} '
          f'smoothMu={smooth:+d} lowCofBill={low_cofactor_transport:+d}')


def main():
    spf, mu, pi = sieve((max(ROOTS) + 1) ** 2)
    assert mu[327] == 1 and mu[345] == -1
    assert 18*18 < 327 < 19*19 and 18*18 < 345 < 19*19
    assert highest_prime(327, spf) == 109 and highest_prime(345, spf) == 23
    print('Exact genuine-Moebius half-run/root/source regression:')
    for R in ROOTS:
        check(R, spf, mu, pi)
    for T in (0, 1, 10, 100):
        D = 6*T + 1
        for X in (-T, -T/2, 0, T/2, T):
            assert 2*(D-X)**2 > (abs(D)+T)**2
    print('PASS physical census identities and algebraic no-go tests')


if __name__ == '__main__':
    main()
