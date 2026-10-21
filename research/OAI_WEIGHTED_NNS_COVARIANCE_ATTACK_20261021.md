# The missing NNS covariance layer INSIDE the actual OpenAI weighted marked kernel

Date: 2026-10-21. Follow-on to merged PR #997. Formal Lean:
[VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021.lean](VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021.lean).

**Status:** exact lossless finite identities under a visible actual-source-admission condition; no new arithmetic power saving, no stronger zero-free bound and no RH claim. All Hecke character phases, selected-mark physical weights and source labels must remain intact.

## 1. Insert NNS AT THE QUADRATIC FORM, BEFORE NONNEGATIVE NORM BOUNDS

OpenAI's true refined marked family in DetectorPlainMarkedFineField.lean is:

    M_jk(U) = sum_{u in F.rows} |W(u)|² |P_j(u)P_k(u)|²,
    W(u)=F.physicalProduct selected u, j+k<=2.

The earlier #997 Lean result already proves the REAL Phi reassembly and polarized degree-four partial-moment identity. The next exact insertion is the physical-weighted character kernel.

For each actual row u, let the COMPLETE ideal pair product admit its original-source finite expansion:

    P_j(u) P_k(u) = sum_{m in I_u} a_{u,jk}(m).

The coefficient a must contain its full ideal ancestry, actual Hecke phase, derivative log profile, conductor dependence and admission masks; never deduplicate different ideal labels by their rational norms. When a true fixed row-independent source exists, it may take the shape b_jk(m) chi_u(m), and b_jk is the genuine IDEAL convolution a_j*a_k. When row data vary, keep a_{u,jk} row-dependent.

The new Lean theorem vf919MarkedFiniteProductAtoms proves the source-level algebra:

    (sum_i A_j(i))*(sum_l A_k(l))
      = sum_{(i,l)} A_j(i)*A_k(l).

The theorem vf919Phi_sum_idealAtoms proves Phi commutes with the FULL finite atom sum. The **remaining actual OAI source-lift** is proving its concrete P_j/P_k polynomial equals that precise original ideal-indexed sum, rather than postulating it.

Let Phi(a_{u,m})=(x_{u,m},y_{u,m}) with
Phi(z)=(Re z-Im z, Re z+Im z).
Then |sum_m a_{u,m}|² = [(sum_m x_{u,m})²+(sum_m y_{u,m})²]/2.

The original physical weight is omega_u=|W(u)|² >=0, NOT the row count or a normalized surrogate. Define

    D = 1/2 sum_u omega_u sum_m (x_{u,m}²+y_{u,m}²)
      = sum_u omega_u sum_m |a_{u,m}|².

For real a,b, define the unnormalized zero-target NNS pair operators already compiled in RH_Lean:

    Co0(a,b) = U1(a)U1(b)+L1(a)L1(b)
    Div0(a,b)= U1(a)L1(b)+L1(a)U1(b)
    Co0(a,b)-Div0(a,b)=ab.

The R x R real Gram on the FULL diagonal-inclusive original ideal carrier is

    C_all = 1/2 sum_u omega_u sum_{m,n}
              [Co0(x_m,x_n)+Co0(y_m,y_n)]
    V_all = 1/2 sum_u omega_u sum_{m,n}
              [Div0(x_m,x_n)+Div0(y_m,y_n)].

The new Lean theorem vf919WeightedPhiMarkedMoment_eq_co_sub_div proves

    M_jk=C_all-V_all.

The diagonal contributes ONLY to C_all: Co0(a,a)=a², Div0(a,a)=0. Let C_off=C_all-D and V_off=V_all. Then

    *** M_jk=D+C_off-V_off. ***

This is the exact original weighted *unnormalized target-zero covariance*; it is NOT a statistical mean-centered covariance and does not silently import independence.

The production-style interface theorem vf919ActualMarkedMoment_eq_exactWeightedNNSCovariance has LHS literally sum_u |W(u)|² |P_j(u)*P_k(u)|², and retains the only missing premise explicitly:

    Phi(P_j(u)*P_k(u)) = sum_m Phi(a_{u,m})  for each u in F.rows.

It proves the original marked moment equals C_all-V_all. The physical W weights, per-row amplitudes and pair multiplicity are NEVER altered. The theorem does not claim to derive this premise from the actual OAI SourceData definition.

## 2. WHERE SOURCE COMPENSATION ENTERS

On an Euler-toggle matched ideal pair (T,Tp), let A_u and B_u be the COMPLETE phase-weighted ideal contributions (including theta_u=chi_u(p) on B). The genuinely compensated source is A_u-B_u.

The direct NNS identity, proved by vf919EulerPairWeightedNNSCovariance, is

    sum_u omega_u |A_u-B_u|²
       = sum_u omega_u (|A_u|²+|B_u|²)
         - sum_u omega_u [
             Co0(xA,xB)+Co0(yA,yB)
              -Div0(xA,xB)-Div0(yA,yB)
           ].

In the normalized Phi coordinates the cross bracket equals 2*Re(A*conj B); with the correct factors it is the exact Hilbert-space compensation.

Thus there are TWO distinct primitive analytic tasks:

(A) Prove a NEW source-specific lower bound on the net aligned same-sign Co0-minus-opposite Div0 Euler compensation over legitimate matched ideal labels, while explicitly paying unpaired cutoff boundary and original selected masks.

(B) Control all remaining interactions between different Euler pairs in the full original ideal-atom quadratic form, including resonant and nonresonant four-point correlations. A local pair saving alone does not control the full fourth moment if interpair covariance is positive.

The complete same-sign-minus-opposite bookkeeping is now an algebraic theorem in the actual original weight. A **uniform sign-sensitive** estimate is still absent.

The conditional Lean implication vf919EulerPairPowerSaving_of_independent_alignment is deliberately conditional; it neither assumes nor establishes any uniform analytic estimate.

## 3. Numerical identity audit: actual RH_Lean ideal sextic PHASES

The independent script scripts/oai_weighted_nns_covariance_kernel_audit.py checks ALL original finite 317/1027 ideal-phase arrays, with all 6 log derivative j,k combinations (the log-power and external W are illustrative; not the full OAI physical F.rows).

For j=k=0, each tagged finite fibre has FOUR original ideals. The literal product P0*P0 expands into SIXTEEN pair-labelled atoms; their diagonal D is 16 on each fibre.

| Native tagged phase fibre | |P0|^4 | Convolution-pair diagonal | Signed off-diagonal = Co_off-Div_off |
|---|---:|---:|---:|
| x=317 | 16 | 16 | 0 |
| x=1027 | 1 | 16 | -15 |
| R=317 | 1 | 16 | -15 |
| R=1027 | 1 | 16 | -15 |
| TOTAL | 19 | 64 | -45 |

This is a DIFFERENT, more direct kernel decomposition than the earlier polynomial rearrangement 19=64+80-152+27. Both are exact but expand different algebraic levels. The new one decomposes the ACTUAL fourth-order ideal convolution directly into a diagonal and NNS offdiagonal payment.

The script also checks all 6 allowed derivative j,k pairs with nonuniform positive external weights, preserving phase. It checks Euler A-B weighted NNS energy and the exact complete sixth-root phase-average obstruction:

    mean_{theta^6=1}|a-theta*b|²=|a|²+|b|².

**Inference limit:** finite negative covariance (-45) is not an unconditional uniform power saving. In complete character families Parseval may cancel its average and other resonances can offset it.

## 4. Quantitative analytic acceptance target

The known OAI source bound is M_jk(U) <= C(1+H)^J U^(1+t).

A genuine NEW sufficient estimate is

    V_off(U)-C_off(U)
       >= D(U)-C'(1+H)^J U^(1+t-sigma), sigma>0,

for all actual accepted rows and profiles, with source labels, conductor/masks and heights respected. This statement is **equivalent to the sharpened bound once the identity is inserted**, so it may NOT be assumed as the new proof. It must be derived independently, e.g.:

- a phase-correct, physically weighted Euler-toggle pairing with a quantitative matched-pair Co0 payment;
- control of every unmatched original boundary/forbidden ideal population and compensation derivative bill;
- separate uniform spectral/large-sieve control of the inter-pair and off-resonant kernel on precisely the original source.

The source and covariance estimation cannot be deduced from the unweighted PNT statement M(X)=o(X) or from equal Mobius parity densities. Character weights may correlate with Mobius signs. For a complete uniform sixth-root ensemble, pure phase pairing gives NO mean L2 energy gain, as the script confirms.

**Correct bottleneck:** prove the sign-sensitive arithmetic inequality governing the ACTUAL original weighted Co-minus-Div ledger after phase-aware Euler pairing, while retaining all interpair kernel sectors. THEN propagate any positive fixed exponent gain through the OAI moment geometries and tracker admissibility constraints.

## 5. CI authority

The new warning-fatal CI checks:
- source product convolution on arbitrary finite ideal sets;
- Phi sum commutation without loss of phase;
- original marked-moment Co-minus-Div theorem conditional on true source admission;
- correct original diagonal and same-sign remainder accounting;
- signed local Euler A-B energy with original physical weights;
- an independent-alignment -> bound implication with its hypothesis fully visible.

No new analytic inequality appears as an axiom; no sorry or sorryAx is permitted. Do NOT claim Lean-certified until the complete final-head CI passes.
