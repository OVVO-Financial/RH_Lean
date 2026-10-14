# Prime Census for the 2026-10-14 Claude cycle.
# Input: exact band prime counts P[R] = #primes in (R^2,(R+1)^2) from band_sieve.c (validated).
# Computes, with the repository's exact definitions:
#   m_R  = (2R+1)/log(R^2+R+1/2)            (vfMidBandMass)
#   F_R  = sum_{r=2}^{R-1} m_r                (vfMidFinishedMass)
#   D_R  = pi(R^2) - F_R                      (vfMidActualPrimeEndpointDefect, raw)
#   w_R  = m_R / R ;  absmass_R = (R-P_R)|w_R| + P_R|1-w_R|   (sum of |vfMidOddSignedSeatCharge|)
#   TotalMass(R) = (|D_R| + absmass_R)^2 ;  Source(R) = D_{R+1}
#   Payment(R)  :<=> 2 D_{R+1}^2 <= TotalMass(R)
# Float pipeline uses math.fsum for F_R; small-R and boundary rows are re-checked with mpmath (dps 50).
import struct, sys, math
import mpmath as mp

path, RMAX = sys.argv[1], int(sys.argv[2])
P = struct.unpack(f'<{RMAX+1}I', open(path, 'rb').read())
s2 = math.sqrt(2.0)

def m(R): return (2*R + 1) / math.log(R*R + R + 0.5)

# cumulative arrays
F = [0.0] * (RMAX + 2); pi_sq = [0] * (RMAX + 2)
acc = []; pi = 0
for R in range(1, RMAX + 1):
    pi_sq[R] = pi                       # pi(R^2) = sum_{r<R} P_r (squares are not prime)
    pi += P[R]
pi_sq[RMAX + 1] = pi
partial = 0.0; comp = 0.0              # Kahan-Neumaier running sum for F_R
F[2] = 0.0
for R in range(2, RMAX + 1):
    x = m(R); t = partial + x
    comp += (partial - t) + x if abs(partial) >= abs(x) else (x - t) + partial
    partial = t; F[R + 1] = partial + comp

D = [0.0] * (RMAX + 2)
for R in range(2, RMAX + 2): D[R] = pi_sq[R] - F[R]

out = {}
# (a) base window at K=2 and ratio profile
base = [(R, abs(D[R]) / (R * math.log(R))) for R in range(2, 9)]
out['base_ratios_K2'] = base
sup9 = max(((abs(D[R]) / (R * math.log(R)), R) for R in range(9, RMAX + 2)))
out['sup_ratio_R>=9'] = sup9
# critical K: for K below the running max ratio a first-bad event exists; first-bad location for given K (from R>=2)
def first_bad(K, start=2):
    for R in range(start, RMAX + 2):
        if K * R * math.log(R) < abs(D[R]): return R
    return None
out['first_bad'] = {K: first_bad(K) for K in (2.0, 1.5, 1.443, 1.0, 0.5, 0.1, 0.05, 0.02, 0.019)}
# first-bad restricted to R>=9 with all of [2,R) good is impossible for K < 1.4427 (R=2 is bad);
# report also the 'tail first-bad' ignoring the base window, as diagnostics only
def tail_first_bad(K, start=9):
    for R in range(start, RMAX + 2):
        if K * R * math.log(R) < abs(D[R]): return R
    return None
out['tail_first_bad_from9'] = {K: tail_first_bad(K) for K in (0.1, 0.05, 0.03, 0.02, 0.019, 0.015, 0.01)}

# (b) hypothesis-free payment inequality, R in [8, RMAX]
fails = []; min_norm = (math.inf, None); max_ratio = (0.0, None)
hold_suff = 0; fail_suff = 0; undecided = 0
nu_min = (math.inf, None); nu_max = (-math.inf, None)
for R in range(8, RMAX + 1):
    w = m(R) / R
    absmass = (R - P[R]) * abs(w) + P[R] * abs(1 - w)
    beta = m(R) + (1 - 2 * w) * P[R]
    assert abs(absmass - beta) <= 1e-9 * max(1.0, beta)
    TM = (abs(D[R]) + absmass) ** 2
    src = D[R + 1]
    slack = TM - 2 * src * src
    norm = slack / TM
    if slack < 0: fails.append(R)
    if norm < min_norm[0]: min_norm = (norm, R)
    delta = P[R] - m(R)
    r = abs(src) / beta
    if r > max_ratio[0]: max_ratio = (r, R)
    if abs(src) <= (1 + s2) * (beta - abs(delta)): hold_suff += 1
    elif abs(src) > 2 * (1 + s2) * beta: fail_suff += 1
    else: undecided += 1
    nu = D[R] * math.log(R) / R
    if nu < nu_min[0]: nu_min = (nu, R)
    if nu > nu_max[0]: nu_max = (nu, R)
out['payment_fail_count'] = len(fails); out['payment_fail_first'] = fails[:10]
out['payment_min_normalized_slack'] = min_norm
out['max |D_{R+1}|/beta_R'] = max_ratio
out['sandwich_counts (hold_suff, fail_suff, undecided)'] = (hold_suff, fail_suff, undecided)
out['nu_R = D_R log R / R  min,max'] = (nu_min, nu_max)
for k, v in out.items(): print(k, '=', v)

# (c) mpmath re-check of base window and of the extremal rows
mp.mp.dps = 50
def F_mp(R): return mp.fsum((2*r + 1) / mp.log(mp.mpf(r)**2 + r + mp.mpf(1)/2) for r in range(2, R))
print("mpmath base check (R, D_R, 2RlogR, good?):")
for R in range(2, 9):
    Dm = pi_sq[R] - F_mp(R); wall = 2 * R * mp.log(R)
    print(" ", R, mp.nstr(Dm, 12), mp.nstr(wall, 8), abs(Dm) <= wall)
for R in sorted({min_norm[1], max_ratio[1], nu_min[1], nu_max[1], sup9[1]} - {None}):
    if R <= 200000:
        Dm = pi_sq[R] - F_mp(R)
        print(f"  recheck R={R}: D_R float={D[R]:.9f} mp={mp.nstr(Dm, 15)}")
