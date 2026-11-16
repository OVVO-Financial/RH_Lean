#!/usr/bin/env python3
"""envelope_kernel_check.py  --  EXT-20261115-ENV reproduction (claims ENV-1, ENV-2)

ENV-1 (exact identity).  For any kappa0 on [1,oo) put kappa(u) = sum_{n<=u} kappa0(u/n).  Then for Y>=1
        int_1^Y M(x) kappa(Y/x) dx/x  =  int_1^Y kappa0(v) dv/v ,
    because sum_{n<=z} M(z/n) = 1 for every real z>=1.

ENV-2 (zero-forced envelope).  With kappa0(v) = (1-rho) v^rho - 1 and zeta(rho)=0, rho = beta + i gamma:
        |kappa(u)| <= C_rho := 1 + |1-rho| (1 + |rho|/beta)        for all u>=1   (bounded kernel),
        int_1^Y |M(x)| dx/x  >=  ( |1-rho| (Y^beta - 1)/|rho| - log Y ) / C_rho   for all Y>=1.
    At a point s that is NOT a zero the same kernel grows like |(1-s) zeta(s)| u^{Re s}.

Provenance: user-supplied external handoff, 2026-11-15; reviewed copy.
Requires numpy and mpmath.  Default reproduces the original N=10^6 scan.
Use --quick for a small smoke check; finite numerical checks are not proofs.
"""
import argparse
import math
import numpy as np
import mpmath as mp

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--quick", action="store_true", help="use N=10000 and 40 random kernel samples")
parser.add_argument("--max-n", type=int, help="largest Mobius argument (at least 1000)")
parser.add_argument("--kernel-samples", type=int, help="number of random kernel sample points")
args = parser.parse_args()
N = args.max_n if args.max_n is not None else (10**4 if args.quick else 10**6)
sample_count = args.kernel_samples if args.kernel_samples is not None else (40 if args.quick else 400)
if N < 1000 or sample_count < 1:
    parser.error("--max-n must be at least 1000 and --kernel-samples must be positive")
mp.mp.dps = 30

# ---- Moebius and Mertens up to N (exact) ----
mu = np.ones(N + 1, dtype=np.int8); mu[0] = 0
isp = np.ones(N + 1, dtype=bool); isp[:2] = False
for p in range(2, int(N**0.5) + 1):
    if isp[p]:
        isp[p*p::p] = False
for p in np.nonzero(isp)[0]:
    mu[p::p] *= -1
    mu[p*p::p*p] = 0
M = np.cumsum(mu.astype(np.int64))
for n, expected in ((10, -1), (100, 1), (1000, 2), (10**6, 212)):
    if n <= N:
        assert M[n] == expected, (n, M[n], expected)

def kappa(u, s):
    n = np.arange(1, int(math.floor(u)) + 1, dtype=np.float64)
    return np.sum((1 - s) * (u / n)**s - 1.0)

def C_rho(rho):
    return 1 + abs(1 - rho) * (1 + abs(rho) / rho.real)

def lhs(Y, s):
    """Evaluate int_1^Y M(x) kappa(Y/x) dx/x by closed-form step integrals in floating point."""
    tot = 0j
    Yf = float(Y)
    for m in range(1, int(Y) + 1):
        top = Yf / m
        nmax = int(math.floor(top))
        n = np.arange(1, nmax + 1, dtype=np.float64)
        a = n; b = np.minimum(n + 1, top)
        I = (1 - s) * (top**s) * (a**(-s) - b**(-s)) / s - np.log(b / a)
        tot += np.sum(M[1:nmax + 1] * I)
    return tot

rng = np.random.default_rng(1)
anchors = [u for u in (1.0, 1.5, 2.0, 7.3, 50.0, 333.3, 1e3, 12345.6, 1e5, 987654.3, 1e6) if u <= N]
if float(N) not in anchors:
    anchors.append(float(N))
samples = np.concatenate([anchors, np.exp(rng.uniform(0, math.log(N), sample_count))])

print("== ENV-2: the kernel is bounded exactly at zeros ==")
s_bad = 0.5 + 10j                                   # not a zero
for k in (1, 2, 3):
    rho = complex(mp.zetazero(k))
    mx = max(abs(kappa(u, rho)) for u in samples)
    print(f"zero #{k}: rho = {rho.real:.1f} + {rho.imag:.6f} i   sup_samples |kappa| = {mx:8.3f}   C_rho = {C_rho(rho):9.2f}")
    assert mx <= C_rho(rho)
grow_us = (100, math.isqrt(100 * N), N)
grow = [abs(kappa(u, s_bad)) for u in grow_us]
print(f"non-zero s = 0.5+10i: |kappa(u)| at u = {grow_us}: {grow[0]:.1f}, {grow[1]:.1f}, {grow[2]:.1f}   (u^0.5 reference growth)")
assert grow[2] > 0.5 * math.sqrt(N / 100) * grow[0]

print("\n== ENV-1: exact identity  int_1^Y M(x) kappa(Y/x) dx/x = (1-s)(Y^s-1)/s - log Y ==")
rho = complex(mp.zetazero(1))
for s, label in ((rho, "s = first zero"), (s_bad, "s = 0.5+10i  ")):
    for Y in (10, 100, 1000, min(N, 2000 if args.quick else 20000)):
        L = lhs(Y, s); Rr = (1 - s) * (Y**s - 1) / s - math.log(Y)
        assert abs(L - Rr) < 1e-6 * max(1, abs(Rr))
        print(f"{label}  Y = {Y:6d}   LHS = {L:.6f}   RHS = {Rr:.6f}   |diff| = {abs(L-Rr):.1e}")

print("\n== ENV-2: all-scale lower bound for the log-weighted L1 mean (first zero) ==")
n = np.arange(1, N, dtype=np.float64)
cum = np.concatenate([[0.0], np.cumsum(np.abs(M[1:N]) * np.log((n + 1) / n))])   # cum[k] = int_1^{k+1} |M| dx/x
beta = rho.real; C = C_rho(rho)
print("       Y    int_1^Y |M| dx/x    lower bound    (integral)/sqrt(Y)")
for Y in (10**2, 10**3, 10**4, 10**5, 10**6):
    if Y > N:
        continue
    Lw = cum[Y - 1]
    lb = ((abs(1 - rho) / abs(rho)) * (Y**beta - 1) - math.log(Y)) / C
    assert Lw >= lb
    print(f"{Y:8d}   {Lw:14.4f}   {lb:11.4f}   {Lw / math.sqrt(Y):12.4f}")
print("\nall checks passed")
