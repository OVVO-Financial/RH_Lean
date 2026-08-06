"""Independent check of RHLean/Proof/BalancedCanonicalGap.lean.

Every theorem in that module is a statement about factor pairs (u, u+d) whose
product lies in the square block B_n = [n^2, (n+1)^2).  Each is re-tested here by
direct enumeration, so a Lean statement that says less than intended shows up as a
check that passes trivially rather than as a silent gap.
"""
import math

LIM = UMAX * (UMAX + GMAX)
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


UMAX = 700          # enumerate every pair with lower endpoint u <= UMAX
GMAX = 4000         # and gap d <= GMAX

failures = 0


def report(name, bad, total, extra=""):
    global failures
    if bad:
        failures += 1
    tag = "FAIL" if bad else "ok"
    print(f"  [{tag}] {name}: {bad} failures / {total} cases {extra}")


def pairs():
    for u in range(1, UMAX + 1):
        for d in range(0, GMAX + 1):
            yield u, u + d, d


# ---- 1. blockIndex_mem, left_le_block_index, factor_sum_ge_two_n ----
print("== 1. unconditional block facts ==")
bad_mem = bad_left = bad_sum = 0
tot = 0
for u, v, d in pairs():
    n = math.isqrt(u * v)
    tot += 1
    if not (n ** 2 <= u * v < (n + 1) ** 2):
        bad_mem += 1
    if not u <= n:
        bad_left += 1
    if not 2 * n <= u + v:
        bad_sum += 1
report("blockIndex_mem      n = isqrt(uv) puts uv in B_n", bad_mem, tot)
report("left_le_block_index u <= n", bad_left, tot)
report("factor_sum_ge_two_n 2n <= u + v", bad_sum, tot)

# ---- 2. scale_localization and height_sandwich (balanced regime 0 < d < u) ----
print("== 2. balanced regime 0 < d < u ==")
bad_loc = bad_lo = bad_hi = 0
tot_bal = 0
tight_lo = tight_hi = None
for u, v, d in pairs():
    if not (0 < d < u):
        continue
    n = math.isqrt(u * v)
    tot_bal += 1
    if not (n ** 2 < 2 * u ** 2 and u <= n <= v < 2 * n):
        bad_loc += 1
    Z2 = d * (u + v)                       # doubledHeight = d(2u+d)
    if not 2 * d * n <= Z2:
        bad_lo += 1
    if not Z2 < 3 * d * n:
        bad_hi += 1
    r = Z2 / (d * n)
    if tight_lo is None or r < tight_lo:
        tight_lo = r
    if tight_hi is None or r > tight_hi:
        tight_hi = r
report("scale_localization  n^2 < 2u^2, u <= n <= v < 2n", bad_loc, tot_bal)
report("height_sandwich lo  2dn <= 2Z", bad_lo, tot_bal)
report("height_sandwich hi  2Z < 3dn", bad_hi, tot_bal)
print(f"        observed 2Z/(dn) range: [{tight_lo:.6f}, {tight_hi:.6f}]"
      f"  (proved bounds 2 and 3)")

# ---- 3. canonicalPair_iff_endpoint_prime ----
# CanonicalPair u d := coprime(u, v) and (DominantPrime v u or DominantPrime u v).
print("== 3. canonical pair <-> an endpoint is prime (balanced) ==")


def dominant_prime(q, c):
    return is_prime(q) and all(p <= q for p in factor(c)) if c > 1 else is_prime(q)


bad_iff = 0
tot_iff = 0
n_can = 0
for u, v, d in pairs():
    if not (0 < d < u):
        continue
    tot_iff += 1
    can = math.gcd(u, v) == 1 and (dominant_prime(v, u) or dominant_prime(u, v))
    end = is_prime(u) or is_prime(v)
    if can != end:
        bad_iff += 1
    if can:
        n_can += 1
report("canonicalPair_iff_endpoint_prime", bad_iff, tot_iff,
       f"({n_can} canonical pairs)")

# The equivalence is genuinely balance-dependent.  Outside 0 < d < u it fails, and
# not only in the degenerate d = 0 / non-coprime cases: the first coprime witness is
# the honest one, where u is prime but does not dominate the prime factors of v.
bad_unbal = 0
first_unbal = None
for u, v, d in pairs():
    if 0 < d < u:
        continue
    can = math.gcd(u, v) == 1 and (dominant_prime(v, u) or dominant_prime(u, v))
    end = is_prime(u) or is_prime(v)
    if can != end:
        bad_unbal += 1
        if first_unbal is None and math.gcd(u, v) == 1 and d > 0:
            first_unbal = (u, v, d, can, end)
if first_unbal:
    u0, v0, d0, can0, end0 = first_unbal
    print(f"  [info] outside 0 < d < u the equivalence fails {bad_unbal} times; first "
          f"coprime witness u={u0} v={v0} d={d0}: canonical={can0}, "
          f"endpoint-prime={end0}")
    print(f"         ({u0} is prime but {v0} has the larger prime factor "
          f"{max(factor(v0))}, so neither endpoint dominates)")
else:
    print("  [warn] equivalence never fails outside the balanced regime "
          "-- is the hypothesis doing any work?")

# ---- 4. canonicalCoefficient_eq_beta and beta_symmetric_identity ----
print("== 4. the symmetric balanced coefficient ==")
bad_beta = bad_sym = 0
tot_beta = 0
for u, v, d in pairs():
    if not (0 < d < u):
        continue
    if u * v > LIM:
        continue
    tot_beta += 1
    can = math.gcd(u, v) == 1 and (dominant_prime(v, u) or dominant_prime(u, v))
    coeff = mu(u * v) if can else 0
    beta = mu(u) * mu(v) * (1 if (is_prime(u) or is_prime(v)) else 0)
    if coeff != beta:
        bad_beta += 1
    rhs = (-mu(u) * (1 if is_prime(v) else 0)
           - mu(v) * (1 if is_prime(u) else 0)
           - (1 if is_prime(u) else 0) * (1 if is_prime(v) else 0))
    if beta != rhs:
        bad_sym += 1
report("canonicalCoefficient_eq_beta", bad_beta, tot_beta)
report("beta_symmetric_identity (two channels - overlap)", bad_sym, tot_beta)

# ---- 5. blockIndex_injective ----
print("== 5. fixed-gap injectivity of the block coordinate ==")
bad_inj = 0
tot_inj = 0
for d in range(0, 200):
    seen = {}
    for u in range(1, 3000):
        n = math.isqrt(u * (u + d))
        tot_inj += 1
        if n in seen:
            bad_inj += 1
        seen[n] = u
report("blockIndex_injective (per gap, distinct u -> distinct block)", bad_inj, tot_inj)

# ---- 6. mem_pairUniverse_of_block ----
print("== 6. the pair universe is complete ==")
bad_uni = 0
tot_uni = 0
for u, v, d in pairs():
    n = math.isqrt(u * v)
    tot_uni += 1
    if not (u < n + 1 and d < (n + 1) ** 2 + 1):
        bad_uni += 1
report("mem_pairUniverse_of_block", bad_uni, tot_uni)

# ---- 7. highBandBlockIncrement_eq_balanced_add_extreme ----
# Direct evaluation of the three finite sums for small n and several thresholds K.
print("== 7. exact balanced/extreme reconstruction ==")
bad_rec = 0
tot_rec = 0
for n in range(2, 120):
    for K in (0, n, 2 * n, 5 * n, n * n):
        full = bal = ext = 0
        for u in range(1, n + 1):
            for d in range((n + 1) ** 2 + 1):
                v = u + d
                if not (n ** 2 <= u * v < (n + 1) ** 2):
                    continue
                if not K < d * (u + v):
                    continue
                can = math.gcd(u, v) == 1 and (dominant_prime(v, u) or dominant_prime(u, v))
                coeff = mu(u * v) if can else 0
                full += coeff
                if d < u:
                    bal += mu(u) * mu(v) * (1 if (is_prime(u) or is_prime(v)) else 0)
                else:
                    ext += coeff
        tot_rec += 1
        if full != bal + ext:
            bad_rec += 1
report("highBandBlockIncrement = balanced + extreme", bad_rec, tot_rec)

print()
print("ALL CHECKS PASSED" if failures == 0 else f"{failures} CHECK GROUP(S) FAILED")
raise SystemExit(1 if failures else 0)
