#!/usr/bin/env python3
"""Exact subwheel comparison, preserving actual larger-prime Mobius cofactors.

Tests all subsets in the nested chain:
  {2}, {2,3}, {2,3,5}, {2,3,5,7}
No added primes enter the finite sign/square-kill coordinate operators.
"""
from fractions import Fraction
from itertools import combinations
from math import gcd, prod, factorial, isqrt

ALL_PRIMES = (2, 3, 5, 7)
EXPECTED = (
    # W, complete physical period, maximum truncated-cube amplitude,
    # parity-block max, last nonpositive square-killing block root
    (2,   1,    1,  1, 0),
    (6,   4,    1,  1, 9),
    (30,  64,   2,  7, 39),
    (210, 2304, 2, 13, 102),
)

def sign_ignoring_larger_primes(P, n, kill_squares):
    ans = 1
    for p in P:
        if kill_squares and n % (p * p) == 0:
            return 0
        if n % p == 0:
            ans = -ans
    return ans

def mu_up_to(N):
    mu = [1] * (N + 1)
    mu[0] = 0
    is_prime = bytearray([1]) * (N + 1)
    is_prime[0] = is_prime[1] = 0
    for p in range(2, isqrt(N) + 1):
        if is_prime[p]:
            for n in range(p * p, N + 1, p):
                is_prime[n] = 0
    for p in range(2, N + 1):
        if is_prime[p]:
            for n in range(p, N + 1, p):
                mu[n] = -mu[n]
            for n in range(p * p, N + 1, p * p):
                mu[n] = 0
    return mu

mu = mu_up_to(318 * 318)
mobius_prefix = [0] * len(mu)
for i in range(1, len(mu)):
    mobius_prefix[i] = mobius_prefix[i - 1] + mu[i]

def signed_orbit_prefix(P, W):
    d_sign = {}
    for r in range(len(P) + 1):
        for chosen in combinations(P, r):
            d_sign[prod(chosen)] = (-1) ** r
    S = [0] * (W + 1)
    for k in range(1, W + 1):
        S[k] = S[k - 1] + d_sign.get(k, 0)
    assert S[W] == 0
    return S

for i, exp in enumerate(EXPECTED):
    P = ALL_PRIMES[:i + 1]
    W, mass, max_S, par_max, last_nonpositive = exp
    assert W == prod(P)
    L = W * W
    qprefix = [0] * (L + 1)
    pprefix = [0] * (W + 1)
    for n in range(1, L + 1):
        qprefix[n] = qprefix[n - 1] + sign_ignoring_larger_primes(P, n, True)
    for n in range(1, W + 1):
        pprefix[n] = pprefix[n - 1] + sign_ignoring_larger_primes(P, n, False)
    assert qprefix[L] == mass and pprefix[W] == 0
    density = Fraction(qprefix[L], L)
    assert density == prod(Fraction(p - 1, p) ** 2 for p in P)
    S = signed_orbit_prefix(P, W)
    assert max(map(abs, S)) == max_S

    def G(x):
        return (x // L) * qprefix[L] + qprefix[x % L]
    def Q(x):
        return pprefix[x % W]
    def block(R):
        return G((R + 1)**2 - 1) - G(R**2 - 1)
    def parity_block(R):
        return Q((R + 1)**2 - 1) - Q(R**2 - 1)

    assert max(abs(parity_block(R)) for R in range(1, W + 1)) == par_max
    # Exhaustion of a complete square-root phase and the exact shift law
    # B(R+L)=B(R)+2*mass prove positivity after the checked threshold for ALL R.
    assert all(block(R + L) == block(R) + 2 * mass
               for R in range(1, min(L, 900) + 1))
    computed_last = 0
    for R in range(1, L + 1):
        b = block(R)
        if b <= 0:
            computed_last = max(computed_last, R + (-b // (2 * mass)) * L)
    assert computed_last == last_nonpositive
    for t in (1, 2, 3, 100, 10000):
        assert block(L * t) == 2 * mass * t
    if P == (2,):
        assert all(block(R) == (R + 1) // 2 for R in range(1, 10001))
        assert all(parity_block(R) == (1 if R % 2 else -1)
                   for R in range(1, 10001))
    # The real, unmodified Mobius source; full higher-prime signs are retained.
    for R in (14, 137, 317):
        X = R * R - 1
        direct = mobius_prefix[X]
        reconstruct = sum(mu[m] * S[min(W, X // m)]
                          for m in range(1, X + 1)
                          if gcd(m, W) == 1)
        assert reconstruct == direct
    actual_r137 = mobius_prefix[138**2 - 1] - mobius_prefix[137**2 - 1]
    assert actual_r137 == 44
    b137 = block(137)
    assert b137 == (69, 30, 22, 2)[i]
    print(f"PASS {P}: W={W} period={L} physical mass={mass} "
          f"rho={density}, |truncated cube|<={max_S}, "
          f"max parity-block={par_max}, "
          f"physical block positive for all R>={last_nonpositive+1}, "
          f"actual R=137: (M,g,difference)=({actual_r137},{b137},{actual_r137-b137})")

# Finite shifts annihilate polynomial log modes below the number of primes.
def D(h, f, u):
    return f(u) - f(u - h)
for k in range(1, 5):
    shifts = ALL_PRIMES[:k]
    for degree in range(k + 1):
        f = lambda u, j=degree: u ** j
        for h in shifts:
            old = f
            f = lambda u, old=old, h=h: D(h, old, u)
        for u in range(-3, 4):
            answer = 0 if degree < k else factorial(k) * prod(shifts)
            assert f(u) == answer
print("PASS: one, two, three and four finite prime shifts annihilate log degrees below their counts")
