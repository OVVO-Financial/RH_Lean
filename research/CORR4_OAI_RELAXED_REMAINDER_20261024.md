# CORR-4: OAI 7/8 guidepost and a genuinely relaxed physical remainder attack

**2026-10-24 | Draft research PR | Lean 4.34.1 | NOT an RH proof.**

## Exact source and strength labels

For R >= 56 put X_R=R^2-1, S_R={odd prime q : q^2 < R}, Y_q=floor(X_R/q^2), and

- C_R = squareRootCanonicalRoughCorrelation R = M(R-1)-M(X_R);
- E_R = canonicalRoughLowQ2DaughterEnergy R = sum_(q in S_R) M(Y_q)^2;
- U_R = lowOwnerCriticalMertensSynthesis R 0 = sum_(q in S_R) M(Y_q)/q;
- B_R = lowOwnerPhysicalAmplitudeRemainder R 0 = C_R-U_R;
- K_R is ANY actual LowerMertensCriticalEnvelope R K (not a guessed squarefree mass).

Every identity above is on the ACTUAL physical carrier. In particular B_R is the complete near-high / tower / Go-wall / renewal / owner-two / terminal / root-corrected zero-frequency remainder; it is not a sum of assumed pointwise ownerwise small errors.

**PROVED existing deterministic input:** the two-term Basel bound

    sum_(q in S_R) 1/q^2 <= 211/900

is already in STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING.lean.

**New deterministic Lean target:** applying the exact critical synthesis frame gives

    |U_R|^2 <= (211/900)*E_R.

Consequently:

    |C_R|^2 <= 4*|U_R|^2 + (4/3)*|B_R|^2
             <= (211/225)*E_R + (4/3)*|B_R|^2.

If one INDEPENDENTLY proves the full source-level inequality

    |B_R|^2 <= (9/4)*E_R + C*R^2*K

for some fixed C>=0, all R>=56, all genuine historical envelopes K, then

    |C_R|^2 <= (886/225)*E_R + (4/3)*C*R^2*K,
    886/225 < 4.

The existing CORRELATION_FOUR_TERMINAL_BRIDGE.lean proves CORR-4 -> RH. This is a compiled CONDITIONAL closure, NOT a new independent bound on B_R. The new Lean file CORR4_OAI_RELAXED_REMAINDER_20261024.lean formalizes this implication.

## OAI is replaceable, not a hard-coded exponent

Using the *same* 211/900 frame, the OPTIMIZED Young comparison is

    |B_R|^2 <= (9/4)*E_R + (2025/1814)*|C_R|^2.

The previous 162/145 coefficient from the looser 17/72 frame is valid but weaker.

For any MertensPowerBound(a), a>=0,

    |C_R| <= 2*C_a*X_R^a
    |B_R|^2 <= (9/4)*E_R + (2025/1814)*(2*C_a*X_R^a)^2.

The already imported original OpenAI 7/8 certificate is one instance (a=7/8+epsilon):

    |B_R|^2 <= (9/4)*E_R + O_epsilon(R^(7/2+epsilon)).

Nothing in the new proof depends on 7/8 being the best possible exponent. Any better independently established all-integer exponent immediately improves this GUIDEPOST remainder power. It does NOT alone prove the critical R^2 K_R relative allowance.

The OAI theorem lives in CORR4_OAI_POWER_GUIDEPOST_20261024.lean.

## Full physical signed NNS Co-Div target

The repository already proves, on one weighted Mobius clock,

    |B_R|^2 = D_R + 2*Gamma_R,

where D_R is the actual squarefree weighted diagonal (already bounded by 3R^2) and Gamma_R is the full real first-separation-owner pair sum with all mixed cross terms. The new relative hypothesis is equivalently

    2*Gamma_R <= (9/4)*E_R + C*R^2*K - D_R.

This is NOT the same as just equal positive/negative densities, and it is NOT supplied by an unweighted OAI covariance theorem. It demands a quantitative signed payment against the ACTUAL weighted diagonal. Theorem relaxedFirstOwnerGram_iff_physicalRemainder pins this obligation.

## Exact cross-currency weight to OAI integer norm coefficient

The ACTUAL physical weight is

    omega_R(n) = 1_{R<=n<=X_R} +
                 sum_(q in S_R) (1/q)*1_{n<=Y_q}.

Its exact restored norm kernel is

    B_R = - sum_(m<=X_R) a_6(m) sum_(d<=X_R) chi_-3(d) *
          [omega_R(md)-omega_R(3md)-omega_R(4md)+omega_R(12md)].

CORR4_OAI_RESTORED_PHYSICAL_KERNEL_20261024.lean specializes the existing
vf919WeightedMobius_eq_excludedNormKernel for the true finite physical
weight. The resulting equality is INTEGER/NORM algebra: NO claim that the
sharp weight is an admitted original OAI marked/Hecke row with controlled
uniform sixth moment. Converting this one physical source into such an
analytic row is the FIRST independent OAI hypothesis still to be proved.

## Independent finite falsification (not asymptotic evidence)

Reproducer: scripts/corr4_oai_remainder_census_20261024.py

    python3 scripts/corr4_oai_remainder_census_20261024.py \
      --max-root 2000 --assert-identity

The diagonal D_R is calculated with the exact squarefree counting expansion,
independently checked against site-by-site physical omega_R(n) on sampled
roots, retaining all q,q' interactions. K_R includes every y<R, including
the crucial small-y maximum 1.5 at y=5.

At roots 56 through 5000 inclusive (4,945 roots, 24,999,999 actual integers),
the smallest needed empirical boundary coefficient

    c_R = (|B_R|^2-(9/4)*E_R)/(R^2*K_R)

has observed maximum 0.12018444535655791 at R=244, where
M(R^2-1)=-102, C_R=100, U_R=-7.72047952, B_R=107.72047952,
E_R=387, K_R=1.5. The C=0 daughter-only assertion FAILS at 2,866 of
these roots. This establishes that the critical historical term cannot simply
be dropped. No observed maximum is claimed to be uniform for all R.


**Extended adversarial sweep (Numba, genuine Mertens through 99,999,999):**

    python3 scripts/corr4_oai_remainder_numba_20261024.py 10000

For all 9,945 roots 56<=R<=10,000 the maximum moves to
**0.14418310472084428 at R=5561**. There X=30,924,720,
M(X)=-2544, C_R=2549, U_R=-121.191365..., B_R=2670.191365...,
E_R=196306 and historical K_R=1.5. A proposed universal C<=0.12 is thus
falsified by the genuine original source. There are 5,772 failures of C=0.
The R=5561 peak overlaps the historical FINITE-A/C stress point; require it
as a regression fixture, not a proof of the bound at all roots. The 0.1442
finite maximum is NOT claimed to persist beyond the tested range.

## Research next action: independently pay ONE new bill

1. **Owner-signed route:** prove a source-specific upper bound
   2*Gamma_R <= (9/4)*E_R + C*R^2*K - D_R, using the already exact
   first-separation-owner Gram and complete four-corner threshold differences;
   do NOT bound individual atoms by daughters (R=64,q=5 disproves that).
2. **OpenAI analytic route:** apply compensated HECKE ideal moments to the
   exact restored omega_R kernel, with ALL masks, Gauss phases, 3/4/12
   exclusions, conductor and height parameters, principal row and sharp
   window costs. First prove source admission; the physical p>R as a direct
   OAI marked slot is already ruled out by the moment-scale inequalities.
3. **Referee/falsifier:** challenge any claimed C and source moment estimate at
   genuine first-bad roots and compare to the explicit signed Gram and daughter
   energies. Report first counterexample, not a smaller convenient surrogate.

**Acceptance is an unconditional independently proved signed bound, a
warning-fatal Lean proof with standard axiom footprint, and the existing
CORR-4 terminal theorem. Conditional wiring alone is not RH.**
