# Signed CRT square-run mixing and physical parity-transfer gate

Date: 2026-10-10.  **Status: unconditional elementary identities and independently
checked physical arithmetic; the uniform signed high-owner estimate is OPEN.
No RH proof is claimed.**  Do not substitute this note for the existing
post-789/first-bad quantitative theorem.

## 1. A finite signed Euler wheel that works on incomplete square runs

Fix a finite set P of distinct primes, k = |P|, and Q = product(P).
For positive n put

    s_P(n) = product_{p in P}(1 - 2*1_{p|n} + 1_{p^2|n}).

For each p, the local factor is +1 if p does not divide n, -1
if p divides n exactly once, and 0 if p^2 divides n. Consequently
s_P(n) is the signed Mobius contribution of the P-part of n.

Put F_P(x) = sum_{1 <= n <= x} s_P(n), and

    rho_P = product_{p in P} (1 - 1/p)^2.

**Proved by finite expansion.** Index e in {0,1,2}^P, set

    d_e = product p^e_p
    c_e = product alpha(e_p),   alpha(0)=1, alpha(1)=-2, alpha(2)=1.

Expansion of the finite Euler product and elementary divisibility counting
give, for EVERY integer x >= 0,

    F_P(x) = sum_e c_e floor(x/d_e)
    rho_P = sum_e c_e/d_e
    |F_P(x) - rho_P*x| <= sum_e |c_e| = 4^k.                 (S1)

No complete Q^2 CRT period is required. The last inequality follows by
bounding each (floor(x/d)-x/d) by 1 before summing its coefficient.

The standard square blocks B_r = [r^2,(r+1)^2) telescope. Hence for
all integers 2 <= a < b, with L=b^2-a^2,

    sum_{a^2 <= n < b^2} s_P(n) = rho_P*L + e_P(b^2-1)-e_P(a^2-1)
    |sum_{a^2 <= n < b^2} s_P(n) - rho_P*L| <= 2*4^k,       (S2)

where e_P(x)=F_P(x)-rho_P*x. The bound is UNIFORM IN THE NUMBER
OF COMPLETED SQUARE BLOCKS. It is not an RH/Mertens estimate: the
nonzero main mode rho_P*L must still be canceled by large-prime parity.

## 2. Exact correction to the ORIGINAL OPEN VF square carrier

The physical VF carrier deletes EVERY perfect square, even when a
partial signed wheel would still count the square. This matters.

Define v_P(n) = 1_{gcd(n,Q)=1}, U_P(x)=sum_{1<=n<=x} v_P(n),
tau_P=product_{p in P}(1-1/p), and u_P(x)=U_P(x)-tau_P*x.
The ordinary subset expansion proves |u_P(x)|<=2^k.

Because s_P(r^2)=v_P(r), the open-square signed population is EXACTLY

    O_P(a,b) =
      sum_{a<=r<b} sum_{r^2<n<(r+1)^2} s_P(n)
      = F_P(b^2-1)-F_P(a^2-1) - U_P(b-1)+U_P(a-1).         (S3)

The uniform signed DOUBLE-ENDPOINT telescope is

    O_P(a,b) = rho_P*(b^2-a^2) - tau_P*(b-a)
      + [e_P(b^2-1)-e_P(a^2-1)]
      - [u_P(b-1)-u_P(a-1)].                               (S4)

Consequently

    |O_P(a,b) - rho_P*(b^2-a^2) + tau_P*(b-a)|
      <= 2*4^k + 2*2^k.                                    (S5)

This retains the missing square-endpoint survivor charge instead of
mistaking selected-wheel square survivors for actual primes. Compare
research/VF_MID_FIRST_BAD_PAYMENT_V2_PROOF_CONTRACT.md, section 0D,
whose existing double-endpoint telescope handles the UNSIGNED wheel.

## 3. Full physical Mobius identity and the open gate

Let d_P(n) be the entire P-supported factor of n, INCLUDING repeated
powers, and let m_P(n)=n/d_P(n). The coprime multiplicativity law gives

    mu(n) = s_P(n) * mu(m_P(n)).                             (S6)

(The equality remains valid when any prime square divides n.)
Define the genuine high-prime parity correction

    H_P(x) = sum_{1<=n<=x} s_P(n)*(mu(m_P(n))-1)
           = M(x)-F_P(x).                                  (S7)

Every physical signed square run therefore obeys

    M(b^2-1)-M(a^2-1)
       = rho_P*(b^2-a^2) + e_P(b^2-1)-e_P(a^2-1)
           + H_P(b^2-1)-H_P(a^2-1).                         (S8)

For a>=2 the actual square sites have mu(r^2)=0. The same actual
left side is the OPEN VF run mass; the low signed term then uses
(S4), and the complementary high-prime correction includes exactly
the corresponding square-survivor restoration. No terms are lost.

**The open analytic/arithmetic gate is the high-prime, occurrence-preserving
SIGNED covariance/compensation in H_P.** CRT phase control alone only bounds
e_P and u_P. It does not bound H_P, the positive zero-frequency
mode rho_P*L, or the fixed-A amplification ratio.

In particular rho_P>0 for every finite P. Letting P grow produces
rho_P -> 0 by Euler's divergent reciprocal-prime sum, but convergence
of this product is much too slow to give root-scale Mertens cancellation
at finite square-root cutoffs. Invoking (S8) as though it already
bounds H_P would be circular.

## 4. Actual physical conditional residue covariance, no probability

Fix a prime p, q=p^2, and f_p(t)=1-2*1_{p|t}+1_{p^2|t}.
On any integer interval I, define

    g_p(n) = mu(n)*f_p(n),  N_t=sum_{n in I, n mod q=t} g_p(n),
    G=sum_t N_t,  rho=(p-1)^2/q,  Nbar=G/q.

Since f_p(n)*g_p(n)=mu(n), and sum_{t mod q} f_p(t)=(p-1)^2,

    C_p(I) := sum_{n in I} mu(n) - rho*G
           = sum_{t mod q} (f_p(t)-rho)*(N_t-Nbar).         (S9)

The physical signed Cauchy-Schwarz certificate is

    C_p(I)^2 <= V_p * sum_{t mod q} (N_t-Nbar)^2,          (S10)
    V_p = q-1 - (p-1)^4/q.

This is exact for any I, including incomplete CRT windows, and
g_p carries the actual remaining first-power prime parity.
The physical complementary residue class sums N_t are NOT known
to be equidistributed. Proving a UNIFORM estimate for their
centered aggregate at the needed square-root scale is a proposed
independent quantitative inlet, not a theorem already supplied
by tensorization.

The repository already proves complete-fibre CRT factorization in
RHLean/Analysis/ElevenWeightOneFirstMoment.lean, and proves a
counterexample to applying the same tensor multiplier to the physical
Mobius field in RHLean/Analysis/PhysicalRecoveredPrimeTensorCompatibility.lean
(the actual one-period factor 4/7 is NOT the formal factor 19/23).
Do not silently identify those observables.

## 5. Independently recomputed numerical examples (integer exact)

True Mobius signs and the 100,000-root census were used.

For a=5267, b=5417, P={2,3,5,7,11,13,17,19}, k=8:

    square-block count                  150
    physical Mobius run mass           -496
    half-open low signed wheel        +46917
    high-prime physical correction    -47413
    low signed wheel phase            +42.206048
    artificial square survivors          24
    ORIGINAL OPEN low signed wheel    +46893
    ORIGINAL OPEN high correction     -47389
    ORIGINAL OPEN centered phase      +43.859651

For a=6000, b=6154 at the same cutoff:

    Mobius run mass                   -580
    half-open low wheel             +54741
    high-prime correction           -55321
    artificial square survivors         26
    OPEN low wheel                  +54715
    OPEN high correction            -55295

For a=88130, b=100000 at the same cutoff:

    Mobius run mass                -83799
    half-open signed wheel      +65316728
    high-prime correction       -65400527

The physical cross-block covariance of Mobius block increments on
the 88130..100000 run is POSITIVE, +5,678,179,854 (diagonal
1,344,092,547; squared run mass 7,022,272,401).
Therefore a universal claim that every run has a nonpositive
signed covariance is already false.

A second, separately compiled integer sieve verifies (S9),(S10)
on the genuine 5267..5417 and 6000..6154 physical windows.
For 5267..5417 and p=11,13,19,29 respectively:

    measured C_p : +429.620, -615.290, +105.330, -447.524
    Cauchy cap   : 5609.073, 6622.695, 8178.091, 10185.188

These are necessary numerical diagnostics, not new uniform estimates.
The centered bound is currently loose and the coherent mean remains.

## 6. Next Lean-accepted proof spine (no new RH criterion)

1. Prove (S1)-(S5) in Mathlib arithmetic as *signed* low-prime
   comb lemmas, carefully retaining the square-survivor correction.
2. Attach (S6)-(S9) to physical canonical greatest-prime/cofactor
   occurrences, with every zero mask, multiplicity and age retained.
3. Fubini/Abel reassemble the high-prime part over whole square runs.
   Center BEFORE taking a norm. Show explicit signed treatment of
   the coherent mean and its positive-lag cross-owner terms.
4. Supply an actually UNCONDITIONAL bound with one coefficient C,
   independent of R and the chosen cutoff; the acceptance currency is
   LowOwnerPost789SignedCrossDiagonalRemainderBound 2 C, or the
   final Stokes 9/4 daughter-energy inequality.
5. Invoke the existing compiled CORR-4 and RH consumers, unchanged.

Neither a 27-state finite Markov surrogate nor truncated Walsh
eigenvalue < 1 is to be substituted for the actual physical high-prime
compensation. Data near a first-bad wall are not supplied by finite scans.

This document establishes the elementary signed low-wheel and
physical covariance statements by explicit finite proofs, not by
Lean-kernel certification of those new statements. The missing
uniform high-owner theorem is OPEN.
