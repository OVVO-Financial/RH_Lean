#!/usr/bin/env python3
"""Independent small-R cross-check of ledger_lab (different code path, exact factoring).

For every R in [6, Rmax] it classifies each raw odd seat by trial division, assigns
it to its greatest prime factor, recomputes the four tag sectors S1..S4, the band
deviation Delta_R and the band identity residual rho_R = Delta_R - F_R*(E(2R-1)-E(R-1)),
and also checks the complete-fibre claim directly: for every prime q in [R, R^2)
the fibre {seats n : P+(n) = q} equals {a*q : a odd, a*q < R^2}.
Compares with ledger_lab's CSV.  Usage: crosscheck_small.py ledger600.csv 200
"""
import csv, math, sys
from mpmath import mp, mpf, log, mertens

mp.dps = 30
M = mertens

def gpf(n):
    p, last, m = 2, 1, n
    while p * p <= m:
        while m % p == 0:
            last, m = p, m // p
        p += 1
    return max(last, m) if m > 1 else last

def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

def main():
    ref = {int(r['R']): r for r in csv.DictReader(open(sys.argv[1]))}
    Rmax = int(sys.argv[2])
    maxdiff = 0.0; fibre_fail = 0; checked = 0
    primes = [p for p in range(2, 2 * Rmax + 2) if isprime(p)]
    for R in range(6, Rmax + 1):
        x = R * R
        w = {r: mpf(2 * r + 1) / (r * log(mpf(r * r + r) + mpf(1) / 2)) for r in range(2, R)}
        S = [mpf(0)] * 4
        fib = {}
        for r in range(2, R):
            for n in range(r * r + 1, (r + 1) * (r + 1)):
                if n % 2 == 0: continue
                q = gpf(n)
                c = w[r] - (1 if q == n else 0)
                sec = 0 if q < R else 1 if q < 2 * R else 2 if 3 * q <= x else 3
                S[sec] += c
                if q >= R: fib.setdefault(q, set()).add(n)
        for q, s in fib.items():
            full = {a * q for a in range(1, x // q + 1, 2) if a * q < x}
            if s != full: fibre_fail += 1
        F = sum(r * w[r] for r in range(2, R))
        def E(y):
            return sum(mpf(1) / p for p in primes if p <= y) - log(log(mpf(y))) - M
        pi = lambda y: sum(1 for p in primes if p <= y)
        Mband = F * (log(log(mpf(2 * R - 1))) - log(log(mpf(R - 1)))) - (pi(2 * R - 1) - pi(R - 1))
        Delta = S[1] - Mband
        rho = Delta - F * (E(2 * R - 1) - E(R - 1))
        rr = ref[R]
        for val, key in [(S[0], 'S1'), (S[1], 'S2'), (S[2], 'S3'), (S[3], 'S4'), (Delta, 'Delta'), (rho, 'rho')]:
            maxdiff = max(maxdiff, abs(float(val) - float(rr[key])))
        checked += 1
    print(f"checked R=6..{Rmax}: max |python - ledger_lab| over S1..S4,Delta,rho = {maxdiff:.3e}; complete-fibre failures = {fibre_fail}")

if __name__ == '__main__':
    main()
