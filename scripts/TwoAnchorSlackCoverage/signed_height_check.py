"""Verify the corrected signed-height attack: clock identity, counting theorem, band energy."""
import math

LIM = 4_000_000
spf = list(range(LIM+1))
for i in range(2, int(LIM**0.5)+1):
    if spf[i] == i:
        for j in range(i*i, LIM+1, i):
            if spf[j] == j: spf[j] = i

def factor(m):
    f = {}
    while m > 1:
        p = spf[m]; f[p] = f.get(p,0)+1; m //= p
    return f

def is_squarefree(m):
    return all(e == 1 for e in factor(m).values())

def mu(m):
    f = factor(m)
    if any(e > 1 for e in f.values()): return 0
    return -1 if len(f) % 2 else 1

def Pplus(m): return max(factor(m))

# ---- 1. the corrected clock identity ----
print("== 1. pointwise clock identity ==")
bad_correct = bad_wrong = 0
first_wrong = None
for m in range(2, 4000):
    if not is_squarefree(m): continue
    q = Pplus(m); c = m // q
    e = math.isqrt(m) if math.isqrt(m)**2 == m+1 else math.ceil(math.sqrt(m+1)) - 1
    e = math.ceil(math.sqrt(m+1)) - 1
    h = q - 1
    for n in range(0, 200):
        lhs = mu(m) * (1 if e <= n else 0)
        rhs_ok = -mu(c)*(1 if e <= n < h else 0) + mu(m)*(1 if max(e,h) <= n else 0)
        rhs_bad = -mu(c)*(1 if e <= n < h else 0) + mu(m)*(1 if h <= n else 0)
        if lhs != rhs_ok: bad_correct += 1
        if lhs != rhs_bad:
            bad_wrong += 1
            if first_wrong is None: first_wrong = (m,q,c,e,h,n,lhs,rhs_bad)
print(f"   corrected identity failures : {bad_correct}")
print(f"   'h <= n' version failures    : {bad_wrong}   first at (m,q,c,e,h,n,lhs,rhs)={first_wrong}")
assert bad_correct == 0 and bad_wrong > 0

# ---- 2. regimes and the signed height ----
print("\n== 2. transport-born <-> Y_* > 0, up to the boundary c = q-1 ==")
mismatch = []
for m in range(2, 200000):
    if not is_squarefree(m): continue
    q = Pplus(m); c = m // q
    e = math.ceil(math.sqrt(m+1)) - 1; h = q - 1
    transport_born = (e < h)
    Ypos = (q*q - c*c) > 0
    if transport_born != Ypos: mismatch.append((m,q,c))
print(f"   mismatches: {len(mismatch)}; all have c = q-1: "
      f"{all(c == q-1 for _,q,c in mismatch)}")
assert all(c == q-1 for _,q,c in mismatch)

# ---- 3. the unconditional counting theorem ----
print("\n== 3. #{m in B_n : mu(m) != 0, Z(m) <= H} <= 1 + floor(H/n) ==")
def Z(m):
    q = Pplus(m); c = m // q
    return abs(q-c)*(q+c)/2
worst = None
for n in range(2, 700):
    lo, hi = n*n, (n+1)*(n+1)
    zs = [(m, Z(m)) for m in range(lo, hi) if mu(m) != 0]
    for H in (0, n//2, n, 2*n, 5*n, 17*n):
        cnt = sum(1 for _, z in zs if z <= H)
        bound = 1 + H//n
        assert cnt <= bound, (n, H, cnt, bound)
        slack = bound - cnt
        if worst is None or slack < worst[0]: worst = (slack, n, H, cnt, bound)
print(f"   holds for every tested (n,H); tightest case slack={worst[0]} at "
      f"n={worst[1]}, H={worst[2]}: count={worst[3]} <= {worst[4]}")

# ---- 4. band energy ----
print("\n== 4. low band: |d_n| <= C_Lambda and |S_n| <= C_Lambda n ==")
for Lam in (0, 1, 2, 5):
    C = 1 + Lam
    S = 0; okd = oks = True
    for n in range(2, 700):
        d = sum(mu(m) for m in range(n*n,(n+1)*(n+1)) if mu(m) != 0 and Z(m) <= Lam*n)
        S += d
        if abs(d) > C: okd = False
        if abs(S) > C*n: oks = False
    print(f"   Lambda={Lam}  C={C}:  |d_n|<=C {okd},  |S_n|<=C n {oks}")
    assert okd and oks
print("\nAll checks passed.")
