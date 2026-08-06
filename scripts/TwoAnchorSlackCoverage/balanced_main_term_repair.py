"""Can the balanced/extreme split be rescued by subtracting a main term?

`balanced_split_frontier.py` shows the raw halves drift to `13.2 N` against a true
`0.43 N`, so a piecewise estimate of the raw halves cannot reach the target.  This
script asks the follow-up question: is the excess a *smooth main term* that can be
identified and subtracted, or is it genuine unstructured growth?

It is a main term, and it is a single explicit one.  But subtracting it is NOT a
repair: this script measures the prefix norm at n <= 1900, where the subtracted half
comes inside budget, while main_term_vs_bridge.c measures the energy norm the target
actually uses out to N = 40000 and finds the same subtracted half diverging again
(0.071, 0.253, 0.973, 1.009, 4.434, growing like N^1.08).  Read the two together.

Where it comes from.  Split the balanced pair population by primality of the two
endpoints and let `N_pp(n)` be the number of balanced coprime prime-prime pairs whose
product lies in `B_n`.  With `beta = mu(u) mu(v) 1_{u or v prime}`:

  * both prime          `beta = +1` on every pair       -> contributes `+N_pp`
  * `u` prime, `v` composite   `beta = -mu(v)`, and
    `sum_{v composite} mu(v) = sum_all mu(v) - sum_{v prime} mu(v) ~ +N_pp`
                                                        -> contributes `-N_pp`
  * `v` prime, `u` composite   symmetrically            -> contributes `-N_pp`

so the predicted main term of the whole balanced half is `-N_pp`, which is exactly the
overlap term `C` of `beta_symmetric_identity`.  The point of this script is that
`N_pp` can be replaced by its prime-density prediction, which uses no Mobius input:
for each prime `u <= n` the admissible `v` window is an explicit interval and primes
in it have density `1 / log v`.

Run time is a few minutes at NMAX = 1900.
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

balanced = [0.0] * (NMAX + 1)
Cactual = [0.0] * (NMAX + 1)      # -N_pp, the overlap term of beta_symmetric_identity
Cpredicted = [0.0] * (NMAX + 1)   # -N_pp predicted from prime density alone

for n in range(2, NMAX + 1):
    lo, hi = n * n, (n + 1) ** 2
    b = 0
    npp = 0
    pred = 0.0
    for u in range(1, n + 1):
        vlo = max(u + 1, -(-lo // u))          # ceil(lo / u)
        vhi = min(2 * u - 1, -(-hi // u) - 1)  # balanced: v < 2u
        if vhi < vlo:
            continue
        for v in range(vlo, vhi + 1):
            if math.gcd(u, v) != 1:
                continue
            up, vp = sieve[u], sieve[v]
            if up or vp:
                b += mob[u] * mob[v]
            if up and vp:
                npp += 1
        if sieve[u]:
            vmid = (vlo + vhi) / 2
            if vmid > 2:
                pred += (vhi - vlo + 1) / math.log(vmid)
    balanced[n] = b
    Cactual[n] = -npp
    Cpredicted[n] = -pred


SAMPLES = (300, 600, 900, 1200, 1500, 1900)


def trajectory(block):
    """prefix/N at the sample points, and the max over all N >= 200.

    The diagnostic is |prefix|/N, not a fitted log-log exponent: these series change
    sign repeatedly and a least-squares fit on log |prefix| reports growth that is not
    there.  See the note in balanced_split_frontier.py.
    """
    S = 0.0
    at, worst = {}, 0.0
    for n in range(2, NMAX + 1):
        S += block[n]
        if n >= 200:
            worst = max(worst, abs(S) / n)
        if n in SAMPLES:
            at[n] = S / n
    return at, worst, S


rows = [
    ("balanced half, raw", balanced),
    ("C = -N_pp, the overlap term", Cactual),
    ("Cpred, density prediction of C", Cpredicted),
    ("balanced - C   (exact count)", [balanced[n] - Cactual[n]
                                      for n in range(NMAX + 1)]),
    ("balanced - Cpred   <-- the repair", [balanced[n] - Cpredicted[n]
                                           for n in range(NMAX + 1)]),
]

print("prefix sum divided by N.  Bounded = within the target; drifting = over it.")
print()
hdr = (f"{'series':<36}" + "".join(f"{n:>9}" for n in SAMPLES)
       + f"{'max|.|/N':>10}" + f"{'prefix':>10}")
print(hdr)
print("-" * len(hdr))
for name, blk in rows:
    at, worst, S = trajectory(blk)
    print(f"{name:<36}" + "".join(f"{at[n]:9.3f}" for n in SAMPLES)
          + f"{worst:10.3f}" + f"{S:10.0f}")

print()
print("For reference the true total has max|prefix|/N = 0.430 on the same range.")
print()
print("Reading: the raw balanced half drifts to 13.2 N and fails.  Subtracting the")
print("main term brings it to 0.39 N -- indistinguishable in scale from the true")
print("total's 0.43 N.  The excess was therefore a main term, not unstructured")
print("growth, and it is identifiable in closed form.")
print()
print("Both the exact count C and its Mobius-free density prediction Cpred work, which")
print("matters: the repair needs only an asymptotic for the prime-pair count, not the")
print("count itself.  Because the two halves sum to the true total, subtracting from")
print("the balanced half and adding to the extreme half repairs both at once.")
print()
print("This is the prefix norm at n <= 1900 only.  In the energy norm out to N = 40000")
print("the same subtraction diverges (main_term_vs_bridge.c), so the split is not")
print("usable even after main-term subtraction -- the main term is real and removing")
print("it helps by a large factor, but it does not bound the sector diagonals.")
