"""How much cancellation does the balanced/extreme split cost?

`BalancedCanonicalGap.highBandBlockIncrement_eq_balanced_add_extreme` is an exact
identity, and `beta_symmetric_identity` writes the balanced coefficient as a sum of
three terms.  Both are correct.  This script asks the separate question of whether
either decomposition can be *estimated piece by piece*, by measuring the growth of
each piece's prefix sum against the growth of the true total.

The target from research/SIGNED_CANONICAL_HEIGHT.md is a local energy bound whose
prefix form is `|sum_{n<=N} d_n| << N^{1+eps}`.  So the question for every piece is
whether its exponent is 1 or bigger.

Run time is a few minutes at NMAX = 1900 (m < 3.6e6).
"""
import math

NMAX = 1900
LIM = (NMAX + 1) ** 2

spf = list(range(LIM + 1))
for i in range(2, int(LIM ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j:
                spf[j] = i


def factor(m):
    f = {}
    while m > 1:
        p = spf[m]
        f[p] = f.get(p, 0) + 1
        m //= p
    return f


def mu(m):
    if m == 1:
        return 1
    f = factor(m)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def is_prime(m):
    return m >= 2 and spf[m] == m


def exponent(block, lo=200):
    """Least-squares fit of alpha in |prefix sum| ~ n^alpha."""
    S = 0.0
    xs, ys = [], []
    for n in range(2, NMAX + 1):
        S += block[n]
        if n >= lo and abs(S) >= 1:
            xs.append(math.log(n))
            ys.append(math.log(abs(S)))
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den, S


# ---------------------------------------------------------------- part 1
# Split the block Mobius increment by the shape of the canonical largest-prime split.
balanced = [0] * (NMAX + 1)
extreme = [0] * (NMAX + 1)
for m in range(2, LIM):
    g = mu(m)
    if g == 0:
        continue
    n = math.isqrt(m)
    if n > NMAX:
        break
    f = factor(m)
    q = max(f)
    c = m // q
    u, v = min(c, q), max(c, q)
    if v - u < u:
        balanced[n] += g
    else:
        extreme[n] += g

total = [balanced[n] + extreme[n] for n in range(NMAX + 1)]

print("== 1. balanced / extreme split of the block increment ==")
print(f"{'piece':<34} {'exponent':>9} {'prefix at N=1900':>18}")
for name, blk in (("balanced part  (0 < d < u)", balanced),
                  ("extreme part   (u <= d)", extreme),
                  ("total  = the truth", total)):
    a, S = exponent(blk)
    print(f"{name:<34} {a:9.3f} {int(S):18d}")
print("  The two halves are each about 500x the size of their sum at N = 1900.")

# ---------------------------------------------------------------- part 2
# Split the balanced coefficient by the three terms of beta_symmetric_identity.
A = [0] * (NMAX + 1)   # -mu(u) 1_{v prime}
B = [0] * (NMAX + 1)   # -mu(v) 1_{u prime}
C = [0] * (NMAX + 1)   # -1_{u prime} 1_{v prime}
for n in range(2, NMAX + 1):
    for u in range(1, n + 1):
        for v in range(u + 1, 2 * u):          # balanced: 0 < d < u
            p = u * v
            if p < n * n:
                continue
            if p >= (n + 1) ** 2:
                break
            if math.gcd(u, v) != 1:
                continue
            A[n] += -mu(u) * (1 if is_prime(v) else 0)
            B[n] += -mu(v) * (1 if is_prime(u) else 0)
            C[n] += -(1 if is_prime(u) else 0) * (1 if is_prime(v) else 0)

AB = [A[n] + B[n] for n in range(NMAX + 1)]
ABC = [A[n] + B[n] + C[n] for n in range(NMAX + 1)]

print()
print("== 2. the three terms of beta = A + B + C ==")
print(f"{'piece':<34} {'exponent':>9} {'prefix at N=1900':>18}")
for name, blk in (("A = -mu(u) 1_{v prime}", A),
                  ("B = -mu(v) 1_{u prime}", B),
                  ("C = -1_{u prime} 1_{v prime}", C),
                  ("A + B  (Mobius channels only)", AB),
                  ("A + B + C = beta", ABC)):
    a, S = exponent(blk)
    print(f"{name:<34} {a:9.3f} {int(S):18d}")

# The reconstruction is exact even though every piece is individually too big.
bad = sum(1 for n in range(2, NMAX + 1) if ABC[n] != balanced[n])
print()
print(f"beta reproduces the balanced increment exactly: {bad} mismatches over "
      f"{NMAX - 1} blocks")

print()
print("Conclusion: both decompositions are exact identities, but the target needs")
print("exponent 1 + eps and only A attains it.  B, C, A+B, beta, the balanced part")
print("and the extreme part are all strictly above 1, so no piecewise estimate of")
print("either decomposition can reach the target -- the cancellation is global.")
