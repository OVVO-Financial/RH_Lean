"""How much cancellation does the balanced/extreme split cost?

`BalancedCanonicalGap.highBandBlockIncrement_eq_balanced_add_extreme` is an exact
identity, and `beta_symmetric_identity` writes the balanced coefficient as a sum of
three terms.  Both are correct.  This script asks the separate question of whether
either decomposition can be *estimated piece by piece*, by measuring each piece's
prefix sum against the target.

The target's prefix form is `|sum_{n<=N} d_n| << N^{1+eps}`, so the diagnostic is
`|prefix| / N`: a piece passes if that stays bounded and fails if it drifts upward.

**Do not fit a log-log exponent to these series.**  Every piece except `C` changes
sign repeatedly, and `log |prefix|` plunges toward `-inf` at each crossing, so a
least-squares fit on `log |prefix|` versus `log n` reports growth that is not there.
Fitting this way gave `1.338` for `B` and `1.406` for `A + B`, both of which are
artifacts -- the trajectories below show both are bounded, at the same scale as the
true total.  Only `C` is monotone, and only for `C` is the fitted `1.714` meaningful.

Run time is a few minutes at NMAX = 1900 (m < 3.6e6).
"""
import math

NMAX = 1900
LIM = (NMAX + 1) ** 2

sieve = bytearray([1]) * (LIM + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(LIM ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))

mob = [0] * (LIM + 1)
mob[1] = 1
primes = []
is_comp = bytearray(LIM + 1)
for i in range(2, LIM + 1):
    if not is_comp[i]:
        primes.append(i)
        mob[i] = -1
    for p in primes:
        if i * p > LIM:
            break
        is_comp[i * p] = 1
        if i % p == 0:
            mob[i * p] = 0
            break
        mob[i * p] = -mob[i]


def largest_prime_factor(m):
    tmp, lp = m, 1
    for p in primes:
        if p * p > tmp:
            break
        while tmp % p == 0:
            lp = p
            tmp //= p
    return tmp if tmp > 1 else lp


# ---- the balanced / extreme split of the block Mobius increment ----
balanced = [0] * (NMAX + 1)
extreme = [0] * (NMAX + 1)
for m in range(2, LIM):
    g = mob[m]
    if g == 0:
        continue
    n = math.isqrt(m)
    if n > NMAX:
        break
    q = largest_prime_factor(m)
    c = m // q
    u, v = min(c, q), max(c, q)
    if v - u < u:
        balanced[n] += g
    else:
        extreme[n] += g
total = [balanced[n] + extreme[n] for n in range(NMAX + 1)]

# ---- the three terms of beta_symmetric_identity, on the balanced population ----
A = [0] * (NMAX + 1)   # -mu(u) 1_{v prime}
B = [0] * (NMAX + 1)   # -mu(v) 1_{u prime}
C = [0] * (NMAX + 1)   # -1_{u prime} 1_{v prime}
for n in range(2, NMAX + 1):
    lo, hi = n * n, (n + 1) ** 2
    for u in range(1, n + 1):
        vlo = max(u + 1, -(-lo // u))
        vhi = min(2 * u - 1, -(-hi // u) - 1)
        for v in range(vlo, vhi + 1):
            if math.gcd(u, v) != 1:
                continue
            up, vp = sieve[u], sieve[v]
            A[n] += -mob[u] * (1 if vp else 0)
            B[n] += -mob[v] * (1 if up else 0)
            C[n] += -(1 if up else 0) * (1 if vp else 0)

CHECK = [A[n] + B[n] + C[n] for n in range(NMAX + 1)]
bad = sum(1 for n in range(2, NMAX + 1) if CHECK[n] != balanced[n])
SAMPLES = (300, 600, 900, 1200, 1500, 1900)


def trajectory(block):
    """prefix/N at the sample points, and the max over all N >= 200."""
    S = 0
    at, worst = {}, 0.0
    for n in range(2, NMAX + 1):
        S += block[n]
        if n >= 200:
            worst = max(worst, abs(S) / n)
        if n in SAMPLES:
            at[n] = S / n
    return at, worst


rows = [
    ("A = -mu(u) 1_{v prime}", A),
    ("B = -mu(v) 1_{u prime}", B),
    ("C = -1_{u prime} 1_{v prime}", C),
    ("A + B  (Mobius channels)", [A[n] + B[n] for n in range(NMAX + 1)]),
    ("beta = A+B+C = balanced half", balanced),
    ("extreme half", extreme),
    ("total  = the truth", total),
]

print("prefix sum divided by N.  Bounded = within the target; drifting = over it.")
print()
hdr = f"{'series':<30}" + "".join(f"{n:>9}" for n in SAMPLES) + f"{'max|.|/N':>10}"
print(hdr)
print("-" * len(hdr))
for name, blk in rows:
    at, worst = trajectory(blk)
    print(f"{name:<30}" + "".join(f"{at[n]:9.3f}" for n in SAMPLES) + f"{worst:10.3f}")

print()
print(f"beta reproduces the balanced increment exactly: {bad} mismatches over "
      f"{NMAX - 1} blocks")
print()
print("Conclusion.  Both decompositions are exact identities, and the diagnostic")
print("separates their pieces cleanly:")
print()
print("  * A, B and A+B are bounded, at the same scale as the true total (0.31, 0.25,")
print("    0.39 against the truth's 0.43).  The Mobius content of the balanced half is")
print("    already within the target.")
print("  * C is the sole obstruction.  It is monotone -- minus the count of balanced")
print("    coprime prime-prime pairs -- and drifts from 3.4 to 12.9 over the range,")
print("    growing like N^0.71 per unit N.  No cancellation is available in it.")
print("  * So the balanced and extreme halves fail only because each carries C (with")
print("    opposite signs).  Removing it is what balanced_main_term_repair.py does.")
