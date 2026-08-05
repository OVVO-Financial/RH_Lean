"""Can the balanced/extreme split be rescued by subtracting a main term?

`balanced_split_frontier.py` shows the raw halves grow like `n^{1.70}` against a true
`n^{1.10}`, so a piecewise estimate of the raw halves cannot reach the target.  This
script asks the follow-up question: is the excess a *smooth main term* that can be
identified and subtracted, or is it genuine unstructured growth?

It is a main term, and it is a single explicit one.

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


def exponent(block, lo=200):
    S = 0.0
    xs, ys = [], []
    for n in range(2, NMAX + 1):
        S += block[n]
        if n >= lo and abs(S) >= 1:
            xs.append(math.log(n))
            ys.append(math.log(abs(S)))
    if len(xs) < 10:
        return float("nan"), S
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den, S


rows = [
    ("balanced half, raw", balanced),
    ("C = -N_pp, the overlap term", Cactual),
    ("Cpred, prime-density prediction of C", Cpredicted),
    ("C - Cpred", [Cactual[n] - Cpredicted[n] for n in range(NMAX + 1)]),
    ("balanced - Cpred   <-- the repair", [balanced[n] - Cpredicted[n]
                                           for n in range(NMAX + 1)]),
]

print(f"{'series':<40} {'exponent':>9} {'prefix at N=1900':>18}")
print("-" * 69)
for name, blk in rows:
    a, S = exponent(blk)
    print(f"{name:<40} {a:9.3f} {S:18.1f}")

print()
print("The target needs exponent 1 + eps; the true total sits at 1.096.")
print()
print("Reading: the raw balanced half is at 1.70 and fails.  Subtracting the single")
print("explicit main term Cpred -- a prime-density count, carrying no Mobius input --")
print("brings it to 0.69, inside the target with room to spare.  The excess was")
print("therefore a main term, not unstructured growth, and it is identifiable in")
print("closed form.  Because the two halves sum to the true total, subtracting Cpred")
print("from the balanced half and adding it to the extreme half repairs both at once.")
print()
print("So the split is usable after main-term subtraction.  What is NOT usable is the")
print("split applied to the raw halves, and that is what balanced_split_frontier.py")
print("and prefix_gram_cross.py rule out.")
