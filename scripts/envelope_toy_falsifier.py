#!/usr/bin/env python3
"""envelope_toy_falsifier.py  --  EXT-20261115-ENV reproduction (claims ENV-3/ENV-4 illustrated, falsifier T1)

(A) Brute-force check of the frozen-root identity   Q_R = sum_{a,b<R} mu(a)mu(b) floor((R^2-1)/(ab)) = 2M(R-1) - M(R^2-1).

(B) Planted-zero model T1.  F_a(s) = zeta(s) (1 - 2^(a-s)) has an Euler product, a pole at 1, and zeros on
    Re s = a at s = a + 2 pi i k / log 2.  Its Dirichlet inverse has coefficients g = mu * t, t(2^k) = 2^(a k),
    summatory function M_g(x) = sum_k 2^(a k) M(x/2^k), and the SAME frozen-root algebra:
        Q^g_R := sum_{a',b<R} g(a') g(b) F1((R^2-1)/(a'b)) = 2 M_g(R-1) - M_g(R^2-1),   F1(y) = floor(y) - 2^a floor(y/2).
    The full exponent uses max(a, Theta), where Theta is the zero supremum of zeta.
    The displayed 2a-1 is only the planted-zero reference slope; it is the full
    predicted slope if Theta <= a.  The envelope theorem permits subpower losses,
    and does not assert a bounded critical ratio without them.
    The theoretical model falsifier also needs the two-adjacent-endpoint
    interpolation lemma in docs/UNIVERSAL_ENVELOPE_NUMERICAL_REVIEW_20261115.md;
    finite scans alone do not establish divergence or boundedness.
    Any argument for finite A / finite C that never uses a property of mu absent from g (|mu|<=1, squarefree
    support, the exact floor) would prove a false statement here.

(C) Bite test.  In the model the zero-forced lower bound of ENV-2 is not vacuous: the f-weighted identity ENV-1
        int_1^Y M_g(x) kappa_f(Y/x) dx/x = (1-s0)(Y^s0 - 1)/s0 - log Y,   kappa_f(u) = sum_{n<=u} f(n) kappa0(u/n),
    is evaluated by closed-form integrals in floating point at a planted zero s0.
    The lower bound uses a proved uniform kernel constant, not the sampled maximum.

Provenance: user-supplied external handoff, 2026-11-15; reviewed copy.
Requires numpy.  Default reproduces the original N=10^7 range.
Use --quick for a small smoke check; finite numerical checks are not proofs.
"""
import argparse
import math
import numpy as np

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--quick", action="store_true", help="use N=100000 and fewer kernel samples")
parser.add_argument("--max-n", type=int, help="largest Mobius argument (at least 10000)")
parser.add_argument("--kernel-samples", type=int, help="number of random kernel sample points")
args = parser.parse_args()
N = args.max_n if args.max_n is not None else (10**5 if args.quick else 10**7)
sample_count = args.kernel_samples if args.kernel_samples is not None else (40 if args.quick else 600)
if N < 10000 or sample_count < 1:
    parser.error("--max-n must be at least 10000 and --kernel-samples must be positive")
mu = np.ones(N + 1, dtype=np.int8); mu[0] = 0
isp = np.ones(N + 1, dtype=bool); isp[:2] = False
for p in range(2, int(N**0.5) + 1):
    if isp[p]:
        isp[p*p::p] = False
for p in np.nonzero(isp)[0]:
    mu[p::p] *= -1
    mu[p*p::p*p] = 0
M = np.cumsum(mu.astype(np.int64))
mu64 = mu.astype(np.int64)

# ---- (A) ----
for R in range(2, 80):
    X = R * R - 1
    b = np.arange(1, R)
    Q = 0
    for a in range(1, R):
        if mu64[a] == 0:
            continue
        Q += int(mu64[a]) * int(np.sum(mu64[1:R] * (X // (a * b))))
    assert Q == 2 * M[R - 1] - M[X], (R, Q)
print("(A) Q_R = 2M(R-1) - M(R^2-1): brute-force verified for 2 <= R < 80")

# ---- (B) ----
def Mg_array(a_exp):
    out = np.zeros(N + 1, dtype=np.float64)
    k = 0
    idx0 = np.arange(N + 1)
    while (1 << k) <= N:
        out += (2.0 ** (a_exp * k)) * M[idx0 >> k]
        k += 1
    return out

def toy_kernel(u, s, a_exp):
    """kappa(u) = sum_{n<=u} f(n) [ (1-s)(u/n)^s - 1 ],  f(n) = 1 - 2^a [2|n]  (coefficients of F_a)."""
    n = np.arange(1, int(math.floor(u)) + 1, dtype=np.float64)
    f = 1.0 - (2.0 ** a_exp) * (np.arange(1, len(n) + 1) % 2 == 0)
    return np.sum(f * ((1 - s) * (u / n) ** s - 1.0))

def toy_kernel_bound(s, a_exp):
    """Uniform bound at a planted zero; see the accompanying numerical review.

    F1(u) = (1 - 2**(a-1))*u + D(u), with |D(u)| <= 2**(a-1).
    Euler summation gives this constant when Re(s)=a and F_a(s)=0.
    """
    return 2.0 ** (a_exp - 1) * (1 + abs(1 - s) * (1 + abs(s) / a_exp))

rng = np.random.default_rng(7)
for a_exp in (0.8, 0.65):
    planted_slope = 2 * a_exp - 1
    Mg = Mg_array(a_exp)
    g = np.diff(np.concatenate([[0.0], Mg]))
    for R in (5, 12, 37):                                   # same frozen-root identity, modified floor
        X = R * R - 1; Q = 0.0
        for a in range(1, R):
            y = X // (a * np.arange(1, R))
            Q += g[a] * np.sum(g[1:R] * (y - (2.0 ** a_exp) * (y // 2)))
        assert abs(Q - (2 * Mg[R - 1] - Mg[X])) < 1e-6 * max(1.0, abs(Q)), R
    s0 = a_exp + 2j * math.pi / math.log(2)                 # a planted zero of F_a
    us = np.concatenate([np.linspace(1, 40, 500 if args.quick else 2000),
                         np.exp(rng.uniform(0, math.log(min(3e5, N)), sample_count))])
    kz = max(abs(toy_kernel(u, s0, a_exp)) for u in us)
    kernel_bound = toy_kernel_bound(s0, a_exp)
    assert kz <= kernel_bound
    off_zero_us = (100, min(100000, N))
    kn = [abs(toy_kernel(u, s0 + 0.07j, a_exp)) for u in off_zero_us]
    Rmax = int(math.isqrt(N))
    y = np.arange(0, Rmax + 1)
    K = np.maximum.accumulate((Mg[:Rmax + 1] - 1) ** 2 / (y + 1.0))      # K[r] = max_{0<=y<=r}
    Rs = np.arange(2, Rmax + 1); KR = K[Rs - 1]; X = Rs * Rs - 1
    al = (Mg[X] - 1) ** 2 / (Rs * Rs * KR)
    crit = np.abs(Mg[X] - 1) / (Rs * KR)
    A = np.maximum.accumulate(al)
    sel = Rs >= 30
    slope_A = np.polyfit(np.log(Rs[sel]), np.log(A[sel]), 1)[0]
    slope_K = np.polyfit(np.log(Rs[sel]), np.log(KR[sel]), 1)[0]
    print(f"\n(B) planted zeros on Re s = {a_exp}   (frozen-root identity re-verified in the model at R = 5, 12, 37)")
    print(f"    f-weighted kernel: sampled max over {len(us)} points = {kz:.6f} (diagnostic only); proved uniform bound = {kernel_bound:.6f}")
    print(f"    off-zero sampled magnitudes: {kn[0]:.1f} at u={off_zero_us[0]} -> {kn[1]:.1f} at u={off_zero_us[1]}")
    print("       R        K_R   K_R/R^(2a-1)    alpha_R   alpha_R/R^(2a-1)   |M_g(X_R)-1|/(R K_R)")
    for R in (10, 30, 100, 300, 1000, 2000, 3000):
        if R > Rmax:
            continue
        i = R - 2
        print(f"    {R:5d}  {KR[i]:9.3f}   {KR[i] / R**planted_slope:10.4f}   {al[i]:8.3f}   {al[i] / R**planted_slope:14.4f}   {crit[i]:18.4f}")
    print(f"    fitted slopes: K_R = {slope_K:.3f}; running max alpha = {slope_A:.3f}; planted-zero reference = {planted_slope:.2f}")
    print("    full model exponent uses max(a, Theta); reference slope assumes Theta <= a")
    print(f"    finite-range maxima (2<=R<={Rmax}): alpha_R = {al.max():.2f}; critical ratio = {crit.max():.3f}; no asymptotic claim from this scan")
    # ---- (C) bite test ----
    def lhs(Y):
        tot = 0j; Yf = float(Y)
        for m in range(1, int(Y) + 1):
            top = Yf / m; nmax = int(math.floor(top))
            n = np.arange(1, nmax + 1, dtype=np.float64)
            lo = n; hi = np.minimum(n + 1, top)
            I = (1 - s0) * (top ** s0) * (lo ** (-s0) - hi ** (-s0)) / s0 - np.log(hi / lo)
            tot += (1.0 - (2.0 ** a_exp) * (m % 2 == 0)) * np.sum(Mg[1:nmax + 1] * I)
        return tot
    for Y in (1000, min(N, 2000 if args.quick else 20000)):
        L = lhs(Y); Rr = (1 - s0) * (Y ** s0 - 1) / s0 - math.log(Y)
        assert abs(L - Rr) < 1e-7 * abs(Rr)
        print(f"(C) f-weighted ENV-1 at the planted zero, Y = {Y:5d}: LHS = {L:.4f}   RHS = {Rr:.4f}   rel diff = {abs(L-Rr)/abs(Rr):.1e}")
    n = np.arange(1, N, dtype=np.float64)
    cum = np.concatenate([[0.0], np.cumsum(np.abs(Mg[1:N]) * np.log((n + 1) / n))])
    print("            Y   int_1^Y |M_g| dx/x    analytic lower bound    true/bound   true/Y^a")
    for Y in (10**3, 10**4, 10**5, 10**6, 10**7):
        if Y > N:
            continue
        Lw = cum[Y - 1]
        lb = ((abs(1 - s0) / abs(s0)) * (Y ** a_exp - 1) - math.log(Y)) / kernel_bound
        assert Lw >= lb
        print(f"    {Y:9d}   {Lw:16.2f}   {lb:12.2f}   {Lw / lb:9.2f}   {Lw / Y ** a_exp:8.4f}")
print("\nall checks passed")
