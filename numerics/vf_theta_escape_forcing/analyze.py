import numpy as np, math, sys
Th = np.fromfile('theta.bin', dtype=np.longdouble)
N = len(Th) - 1                       # blocks r = 1..N-1 known; E(R) known for R <= N
R = np.arange(N + 1, dtype=np.int64)
theta = np.zeros(N + 1, dtype=np.longdouble)
theta[2:] = np.cumsum(Th[1:N])        # theta(R^2) = sum_{r<R} Theta_r
E = (theta - R.astype(np.longdouble) ** 2).astype(np.float64)   # vfMidDirectThetaEndpointError
Rf = R.astype(np.float64)
L = np.log(np.maximum(Rf, 1.0))
U = -(Th[:N].astype(np.float64) - (2 * Rf[:N] + 1))             # protected pull U_R, R < N
assert np.allclose(E[1:N] - U[1:N], E[2:N+1])

def decades(lo=3):
    k = 0
    while 10 ** k < N:
        a, b = max(lo, 10 ** k), min(N, 10 ** (k + 1))
        if a < b: yield a, b
        k += 1

print(f"N = {N}  (largest square endpoint x = {N*N:.3e})\n")
# ---- 1. square-theta envelope constant  |E(R)| <= C R log^2 R
c = np.abs(E) / (Rf * L ** 2 + (Rf < 3))
init = c[3:8].max()
print("1. Envelope ratio |E(R)|/(R log^2 R)")
print(f"   initialization max over 3<=R<=7: {init:.4f} at R={3+int(c[3:8].argmax())}")
for a, b in decades():
    i = a + int(c[a:b].argmax())
    print(f"   R in [{a:>7},{b:>7}): max {c[a:b].max():.4f} at R={i}   max|E|/R {np.abs(E[a:b]/Rf[a:b]).max():.3f}")
print(f"   overall max over R>=8: {c[8:].max():.4f}")

# ---- 2. route-2 barrier statement (VFMidThetaProtectedPullBarrierStatement)
G = Rf ** 2 * L ** 4
num = U[7:N] ** 2 - 2 * E[7:N] * U[7:N]
den = G[8:N+1] - G[7:N]
need = num / den                       # C^2 needed at step R
print("\n2. Barrier route: C^2 needed at step R = (U^2 - 2EU)/(G(R+1)-G(R)), G=R^2 log^4 R")
Rs = Rf[7:N]
heur = np.sqrt(Rs) / np.log(Rs) ** 3.5
for a, b in decades(7):
    s = slice(a - 7, b - 7)
    i = a + int(need[s].argmax())
    q = np.quantile(need[s], [0.5, 0.99])
    print(f"   R in [{a:>7},{b:>7}): max {need[s].max():9.4f} (R={i:>6})  median {q[0]:8.4f}  p99 {q[1]:8.4f}"
          f"  frac>0 {np.mean(need[s] > 0):.3f}  sqrt(R)/log^3.5 R ~ {heur[s].mean():.3f}")
# trend of the top 0.1% per decade-ish window normalized by heuristic
print("   ratio (p99.9 of need) / (sqrt(R)/log^3.5 R) per window:")
for a, b in decades(1000):
    s = slice(a - 7, b - 7)
    print(f"     [{a},{b}): {np.quantile(need[s], 0.999) / heur[s].mean():.3f}")

# ---- 3. route-3 forcing statements (#858)
odd_primes = [p for p in range(3, int(round(N ** (2 / 3))) + 3) if all(p % d for d in range(2, int(p ** .5) + 1))]
def isqrt_arr(m):
    s = np.floor(np.sqrt(m.astype(np.float64))).astype(np.int64)
    s -= (s * s > m); s += ((s + 1) * (s + 1) <= m)
    return s
def child_witness(Rset, outside):
    """Generous superset of #858 recursive-child endpoints T in {S,S+1} (ignores the p-rough
    condition on the child, so 'no witness' here is a genuine counterexample)."""
    Rset = np.asarray(Rset, dtype=np.int64)
    w = np.zeros(len(Rset), dtype=bool); nchild = np.zeros(len(Rset), dtype=np.int64)
    for p in odd_primes:
        ok = (p ** 3 < (Rset + 1) ** 2) & (p <= Rset)
        if not ok.any(): break
        r = Rset[ok]
        mlo = (r * r + 1 + p - 1) // p; mhi = ((r + 1) ** 2 - 1) // p
        slo, shi = isqrt_arr(mlo), isqrt_arr(mhi)
        hit = outside[slo] | outside[slo + 1] | outside[shi + 1]
        w[ok] |= hit; nchild[ok] += 1
    return w, nchild

def matched_background(big, esc, k=20):
    """k non-escape scales drawn uniformly from [0.9R, 1.1R] for each escape R."""
    escset = set(int(e) for e in esc); out = []
    for r in big:
        lo, hi = max(8, int(0.9 * r)), min(N - 2, int(1.1 * r))
        c = rng.integers(lo, hi + 1, size=3 * k)
        out.extend([int(x) for x in c if int(x) not in escset][:k])
    return np.array(out, dtype=np.int64)

print("\n3. #858 forcing statements, F_R = C R log^2 R")
rng = np.random.default_rng(0)
for C in [0.004, 0.008, 0.015, 0.02, 0.025, 0.03, 0.06, 0.12, 0.25, 0.5, 1.0, init, 1.05 * init]:
    F = C * Rf * L ** 2
    outside = np.abs(E) > F
    outside[:3] = False
    esc = np.nonzero((~outside[7:N]) & outside[8:N+1])[0] + 7
    big = esc[esc >= 1000]
    init_ok = not outside[3:8].any()
    line = f"   C={C:7.4f} init_ok={init_ok!s:5}  escapes R>=7: {len(esc):6}  (R>=1000: {len(big):6})"
    if len(big):
        w, nch = child_witness(big, outside)
        bg = matched_background(big, esc)
        wb, _ = child_witness(bg, outside)
        fr_out = outside[1000:N].mean()
        line += (f"  child-witness at escapes {w.mean():.3f} vs R-matched background {wb.mean():.3f}"
                 f"  | escapes w/o witness {int((~w).sum())}  | frac endpoints outside {fr_out:.3f}")
        if (~w).any():
            line += f"  e.g. R={int(big[~w][-1])}"
    print(line)

# ---- 3b. where do child witnesses sit?  and a shape-neutral control F_R = c R
def child_witness_detail(Rset, outside):
    out = []
    for r in Rset:
        Ts = set()
        for p in odd_primes:
            if p ** 3 >= (r + 1) ** 2 or p > r: break
            mlo = (r * r + p) // p; mhi = ((r + 1) ** 2 - 1) // p
            slo, shi = math.isqrt(mlo), math.isqrt(mhi)
            Ts.update([slo, slo + 1, shi + 1])
        hits = sorted(t for t in Ts if outside[t])
        out.append((len(Ts), hits))
    return out
print("\n3b. Witness location for #858 shape (F = C R log^2 R), C = 0.03:")
F = 0.03 * Rf * L ** 2; outside = np.abs(E) > F; outside[:3] = False
esc = np.nonzero((~outside[7:N]) & outside[8:N+1])[0] + 7
esc = esc[esc >= 1000]
for r, (nT, hits) in zip(esc[-5:], child_witness_detail(esc[-5:], outside)):
    print(f"   escape R={r}: {nT} child endpoints, outside ones: {hits[:6]}{'...' if len(hits) > 6 else ''}"
          f"  (max witness T / R = {max(hits) / r if hits else float('nan'):.4f})")

print("\n3c. Shape-neutral control, F_R = c R (removes the log^2 normalization bias):")
for cc in [0.6, 0.9, 1.2, 1.4, 1.6]:
    F = cc * Rf; outside = np.abs(E) > F; outside[:3] = False
    esc = np.nonzero((~outside[7:N]) & outside[8:N+1])[0] + 7
    big = esc[esc >= 1000]
    if not len(big):
        print(f"   c={cc}: no escapes for R>=1000"); continue
    w, _ = child_witness(big, outside)
    bg = matched_background(big, esc)
    wb, _ = child_witness(bg, outside)
    noesc = np.setdiff1d(np.arange(1000, N - 1), esc)
    print(f"   c={cc}: escapes(R>=1000) {len(big):6}  witness at escapes {w.mean():.3f}  vs R-matched background {wb.mean():.3f}"
          f"  | escapes w/o witness {int((~w).sum())}  | frac outside {outside[1000:N].mean():.3f}")
