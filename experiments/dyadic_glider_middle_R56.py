#!/usr/bin/env python3
"""Exact R=56 regression for the dyadic Othello/glider-wall split.

This checks:
  * M(3135) = 6;
  * the inert top-prime block has 198 primes;
  * the intermediate prime Mertens tail is -245;
  * the complete R-smooth mass is -41;
  * the exact active-middle residual is -6 = -M(3135);
  * the 634 gliders are exactly the squarefree odd top-wall cells;
  * every live glider lies in reciprocal replacement fibre z=1;
  * the full z=1 fibre is larger and has signed mass 9, not 6;
  * swapping one fresh prime for another at fixed cofactor preserves Mobius sign.

No asymptotic estimate is used.
"""

import math
from bisect import bisect_right

R = 56
X = R * R - 1


def mobius_sieve(nmax):
    lp = [0] * (nmax + 1)
    mu = [0] * (nmax + 1)
    mu[1] = 1
    primes = []
    for n in range(2, nmax + 1):
        if lp[n] == 0:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p > lp[n] or n * p > nmax:
                break
            lp[n * p] = p
            if p == lp[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]

    largest = [0] * (nmax + 1)
    for p in primes:
        for m in range(p, nmax + 1, p):
            largest[m] = p
    largest[1] = 1

    mertens = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        mertens[n] = mertens[n - 1] + mu[n]

    return mu, largest, primes, mertens


mu, largest, primes, mertens = mobius_sieve(X)

middle_primes = [q for q in primes if R < q <= X // 2]
top_primes = [q for q in primes if X // 2 < q <= X]

middle_tail = sum(mertens[X // q] for q in middle_primes)
smooth_mass = sum(
    mu[n] for n in range(1, X + 1)
    if largest[n] <= R
)
known_edge_mass = smooth_mass - len(top_primes)
middle_residual = middle_tail - known_edge_mass

assert X == 3135
assert mertens[X] == 6
assert len(top_primes) == 198
assert len(middle_primes) == 231
assert middle_tail == -245
assert smooth_mass == -41
assert known_edge_mass == -239
assert middle_residual == -6
assert middle_residual == -mertens[X]

# Prime-two Othello wall and its iterated odd-prime escape boundary.
def carrier_toggle(p, n):
    if n % (p * p) == 0:
        return n
    if n % p == 0:
        return n // p
    return n * p


def escape_part(p, carrier):
    return {n for n in carrier if carrier_toggle(p, n) not in carrier}


dyadic_wall = {
    n for n in range(1, X + 1)
    if n % 2 == 1 and X < 2 * n
}
assert len(dyadic_wall) == 784
assert sum(mu[n] for n in dyadic_wall) == mertens[X]

glider_boundary = set(dyadic_wall)
for p in [q for q in primes if 3 <= q <= R]:
    glider_boundary = escape_part(p, glider_boundary)

assert len(glider_boundary) == 634
assert sum(mu[n] for n in glider_boundary) == mertens[X]
glider_positive = sum(1 for n in glider_boundary if mu[n] == 1)
glider_negative = sum(1 for n in glider_boundary if mu[n] == -1)
assert glider_positive == 320
assert glider_negative == 314

# The iterated odd-prime wall is exactly the nonzero/squarefree part of the
# prime-two dyadic wall.
live_gliders = {n for n in dyadic_wall if mu[n] != 0}
assert glider_boundary == live_gliders
assert len(live_gliders) == 634

# Every top-wall glider has floor(X/n)=1, so the complete live wall embeds in
# reciprocal replacement fibre z=1.
assert all(X // n == 1 for n in live_gliders)

# The converse is false: replacement fibre z=1 also contains even states that
# prime-two Othello already paired away. Its full Mobius mass is 9, while the
# odd live-glider residual has mass 6.
replacement_fibre_one = {
    n for n in range(R, X + 1)
    if X // n == 1
}
assert min(replacement_fibre_one) == X // 2 + 1
assert max(replacement_fibre_one) == X
assert live_gliders <= replacement_fibre_one
assert sum(mu[n] for n in replacement_fibre_one) == 9
assert sum(mu[n] for n in live_gliders) == 6

# Root-cardinality and atomwise replacement remain impossible: the single
# cofactor c=1 has 198 top-prime edges, versus only 16 low primes through R.
low_primes = [q for q in primes if q <= R]
assert len(low_primes) == 16
assert len(top_primes) == 198
assert len(top_primes) > len(low_primes)

# Prime replacement at a fixed rough cofactor preserves, rather than reverses,
# the Mobius sign. Example: c=3, q_low=5, p_high=523.
c0, q_low, p_high = 3, 5, 523
assert q_low in primes and p_high in primes
assert largest[c0] < q_low < R < p_high
assert c0 * p_high in live_gliders
assert mu[c0 * q_low] == 1
assert mu[c0 * p_high] == 1
assert mu[c0 * q_low] == mu[c0 * p_high]

# Exact recursive-replacement row.  This is the actual nonlocal pushforward:
# kernel(R,n) = sum_{d|n, d<R} mu(d), then all n with the same quotient y are
# recombined before multiplying M(y).
def divisors(n):
    out = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
        d += 1
    return out


def replacement_kernel(n):
    return sum(mu[d] for d in divisors(n) if d < R)


replacement_tail_coeff = [0] * R
for n in range(R, X + 1):
    y = X // n
    replacement_tail_coeff[y] += replacement_kernel(n)

replacement_coeff = [
    (1 if y == R - 1 else 0) - replacement_tail_coeff[y]
    for y in range(R)
]
replacement_row_value = sum(
    replacement_coeff[y] * mertens[y]
    for y in range(R)
)

assert replacement_tail_coeff[1] == -2
assert replacement_coeff[1] == 2
assert replacement_row_value == mertens[X] == 6

# Independently construct the cofactor-prime Type-II windows, then compare
# them to the literal Mobius fibres.  These are exact integer calculations.
def reciprocal_prime_count(cutoff, endpoint, y):
    lower = max(cutoff, endpoint // (y + 1))
    upper = endpoint // y
    return max(0, bisect_right(primes, upper) - bisect_right(primes, lower))


tail_mobius = [0] * R
prime_face = [0] * R
for n in range(R, X + 1):
    tail_mobius[X // n] += mu[n]
for p in primes:
    if p >= R:
        prime_face[X // p] -= 1

type_ii = [0] * R
canonical_full = [0] * R
descendants = [0] * R
for y in range(1, R):
    root_composite = -sum(
        mu[c] * reciprocal_prime_count(c, X // c, y)
        for c in range(2, R)
    )
    smooth = -sum(
        mu[c] * sum(
            1 for p in primes
            if max(largest[c], X // c // (y + 1)) < p
            <= X // c // y and p < c
        )
        for c in range(1, X // 2 + 1) if mu[c]
    )
    type_ii[y] = -sum(
        mu[c] * reciprocal_prime_count(largest[c], X // c, y)
        for c in range(2, X // 2 + 1)
    )
    assert root_composite + smooth == type_ii[y]
    canonical_full[y] = type_ii[y] + prime_face[y]
    assert canonical_full[y] == tail_mobius[y]

for y in range(1, R):
    descendants[y] = sum(
        canonical_full[z] * (z // y - z // (y + 1))
        for z in range(y + 1, R)
    )
    assert replacement_coeff[y] == (
        (1 if y == R - 1 else 0) + prime_face[y]
        + type_ii[y] + descendants[y]
    )

assert prime_face[1] == -198
assert type_ii[1] == 207
assert descendants[1] == -7
assert prime_face[1] + type_ii[1] + descendants[1] == 2

# Find the first complete-layer crossing and the least sufficient seat.
layer_cards = [0] * R
for p in primes:
    if p > R:
        layer_cards[X // p] += 1
partial_before = 0
for K in range(1, R):
    partial_after = partial_before - layer_cards[K] * mertens[K]
    if partial_before < 0 <= partial_after:
        j = next(j for j in range(layer_cards[K] + 1)
                 if partial_before - j * mertens[K] >= 0)
        break
    partial_before = partial_after
else:
    raise AssertionError("No crossing found")

partial_packet = partial_before - j * mertens[K]
assert (K, j, partial_packet) == (18, 2, 0)
post_crossing_row = []
for y in range(1, R):
    removal = layer_cards[y] if y < K else (j if y == K else 0)
    prime_diagonal = prime_face[y] + removal
    if y < K:
        assert prime_diagonal == 0
    if y == K:
        assert prime_diagonal == j - layer_cards[K]
    coefficient = ((1 if y == R - 1 else 0) + prime_diagonal
                   + type_ii[y] + descendants[y])
    assert coefficient == replacement_coeff[y] + removal
    post_crossing_row.append(coefficient * mertens[y])

assert type_ii[1] + descendants[1] == 200
assert sum(post_crossing_row) == mertens[X] - partial_packet == 6

print("R =", R, "X =", X)
print("M(X) =", mertens[X])
print("middle prime count =", len(middle_primes))
print("top prime count =", len(top_primes))
print("middle Mertens tail =", middle_tail)
print("complete smooth mass =", smooth_mass)
print("known edge mass =", known_edge_mass)
print("active-middle residual =", middle_residual)
print("prime-2 dyadic wall card =", len(dyadic_wall))
print("iterated glider-boundary card =", len(glider_boundary))
print("iterated glider-boundary mass =", sum(mu[n] for n in glider_boundary))
print("glider signs: +", glider_positive, "/ -", glider_negative)
print("replacement z=1 full-fibre mass =", sum(mu[n] for n in replacement_fibre_one))
print("low-prime count through R =", len(low_primes))
print("same-c prime-swap witness: mu(15) =", mu[15],
      ", mu(1569) =", mu[1569])
print("replacement tail coefficient z=1 =", replacement_tail_coeff[1])
print("replacement full coefficient z=1 =", replacement_coeff[1])
print("recombined replacement row =", replacement_row_value)
print("z=1 prime face / Type-II / strict descendants =",
      prime_face[1], type_ii[1], descendants[1])
print("first crossing K / admitted seats j / partial packet =",
      K, j, partial_packet)
print("post-crossing first coefficient =", type_ii[1] + descendants[1])
print("complete signed canonical Type-II row =", sum(post_crossing_row))
print("PASS: active middle leaves -6 = -M(3135), not zero;")
print("      634 live gliders embed in z=1 but are not the whole fibre;")
print("      same-c fresh-prime replacement preserves Mobius sign.")
print("      prime-face cancellation and Type-II splice retain all descendants.")
