# Independent check of EXT-20261014-1 (sharp quotient wheel capacity) on genuine primes.
from math import gcd, isqrt
import sys
NMAX = 20001**2
spf = None
def build_spf(n):
    s = list(range(n+1))
    for i in range(2, isqrt(n)+1):
        if s[i] == i:
            for j in range(i*i, n+1, i):
                if s[j] == j: s[j] = i
    return s
spf = build_spf(10001**2 + 10)   # enough for runs up to B=10000
def is_prime(n): return n > 1 and spf[n] == n
def W30(t): return sum(1 for j in (1,2,3,4) if gcd(t+j, 30) == 1)
def C(m, t, u): return sum(1 for q in range(t+1, u+1) if gcd(q, m) == 1)
def run(A, B, check=True):
    tot = dict(slots=0, actual=0, w30=0, c30=0, c210=0, c2310=0); viol = 0
    for R in range(A, B):
        lo, hi = R*R, (R+1)**2
        for p in range(A+1, R+1):
            if not is_prime(p): continue
            t, u = lo // p, (hi - 1) // p
            fib = sum(1 for n in range(lo+1, hi) if spf[n] == p and n != p)
            c2310 = C(2310, t, u); c210 = C(210, t, u); c30 = C(30, t, u); w = W30(t)
            assert u - t <= 4, (A, R, p)
            if check and not (fib <= c2310 <= c210 <= c30 <= w <= 2): viol += 1
            tot['slots'] += 1; tot['actual'] += fib; tot['w30'] += w
            tot['c30'] += c30; tot['c210'] += c210; tot['c2310'] += c2310
    return tot, viol
for (A, B) in [(50,100), (100,200), (500,1000)]:
    tot, viol = run(A, B)
    print(f"[{A},{B}): {tot}  chain violations: {viol}")
# exhaustive per-fibre check for every admissible (A,R,p), 11 <= A <= 1200 via unique (R,p) with max(11, R//2+1) <= A < p
viol = 0; fibres = 0; maxfib = 0
for R in range(11, 2400):
    lo, hi = R*R, (R+1)**2
    for p in range(R//2 + 2, R+1):
        if not is_prime(p): continue
        if max(11, R//2 + 1) >= p: continue
        t, u = lo // p, (hi - 1) // p
        fib = sum(1 for n in range(lo+1, hi) if spf[n] == p and n != p)
        fibres += 1; maxfib = max(maxfib, fib)
        if fib > C(2310, t, u): viol += 1
print("exhaustive fibres (R<2400):", fibres, "max fibre", maxfib, "C2310 violations", viol)
print("sharp witness (12,22,17):", [n for n in range(22*22+1, 23*23) if spf[n] == 17 and n != 17])
