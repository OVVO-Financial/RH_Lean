# One simultaneous ledger: sequential prime wheel, OpenAI Hecke compensation, and unnormalized NNS covariance

Date: 2026-10-21. This is an explicit relationship and audit, NOT a claim that rational integer Mobius seats are the same as Hecke ideal atoms or that the finite identities improve 7/8.

## 1. Put the clocks side by side

| Chronological event | Actual prime-wheel visualization | OpenAI Hecke character source | Same NNS quantity |
|---|---|---|---|
| Initial atom | n in [1,X], seed +1 at n=1 and -1 for n>=2 | actual ideal-labelled source coefficient, original selected-prime mask and conductor | retain source coefficient BEFORE taking its norm |
| New prime | integer prime p adjoined to the wheel S | marked prime ideal p, original character phase theta=chi_u(p) | one signed operator applied to the current state |
| First hit | proper previously untouched multiple remains -1; root p was already -1 | empty cofactor / identity-face contribution, possibly an unmatched boundary | never spend the same prime root twice |
| Square hit | p² divides n: live integer seat killed to 0 | forbidden/ramified/nonunit/zero-character and actual support masks | omit dead/zero atoms from active support |
| Later squarefree hit | nonzero existing integer seat flips sign | chi_u(Tp)=chi_u(T)*theta; genuine phase retained in marked-minus-rescaled source | pre-norm Co/Div measures aligned versus divergent pair |
| Arithmetic result | exact finite signed prime-wheel recurrence | uniform phase-weighted Hecke second/fourth moment and large-sieve bound | same SIGNED real NNS accounting, different arithmetic input |

The prime-wheel parity phase is -1 on a new Boolean prime coordinate. A sextic Hecke phase theta need NOT equal -1. The finite algebra is shared; actual arithmetic sources and analytic bounds are not automatically identified.

## 1B. The actual OpenAI source to place in the neighboring column

This crosswalk must reuse the SOURCE-LEVEL OpenAI declarations already catalogued in [OAI_919_COMPENSATION_NNS_SIMULTANEOUS_CROSSWALK_20261021.md](OAI_919_COMPENSATION_NNS_SIMULTANEOUS_CROSSWALK_20261021.md), not a made-up Euler toy model:

1. Detector/Compensation.lean (tupleOperation_one) and Detector/Physical.lean (compensatedTuple_one). For a single selected prime IDEAL p of norm Np, the ACTUAL terms are

    A = conjugate(eta(p)) * markedPhysicalProbe(...,D=(p),X,Y,Z*Np)
    B = Np^(-3/2) * physicalProbe(...,X/Np,Y/Np,Z),
    compensatedTuple_one = A-B.

   Observe the true conjugated Hecke character, the Np^(-3/2) scalar, and BOTH rescalings. An arbitrary a(T)-theta*a(Tp) is a reusable algebraic primitive, NOT the full physical probe.

2. Detector/GaussianCompensation.lean (compensatedPhysicalProbe_eq_subsets). The complete selected-prime source expands over subsets J of selected prime slots with ORIGINAL coefficient

    (-1)^|J| * N(p_J)^(-3/2) *
       conjugate(eta(p_complement(J))),

   multiplied by the original product of prime-slot windows and the correspondingly marked/rescaled probe. The alternating (-1)^|J| is the same Boolean-face parity operation visible in the frozen wheel; the conjugated character, norm weight, window and X/Y/Z modifications are the ADDITIONAL arithmetic structure of OpenAI's compensation.

3. Detector/CompensatedTriple.lean (compensatedPhysicalProbe_eq_row_triples), Moments/DetectorDictionaryFiber.lean (fiber_plain_energy_eq), and Moments/DetectorPlainFiberSource.lean (detector_row_eq_source) are the ACTUAL already-proved OpenAI source/moment identifications. At each accepted row u, after finite-column reindexing,

    detectorPositiveRow(u)
      = D_U^(-1/2) * sum_(I in finiteColumns) c_(u,I),
    D_U=(U^F.m)^2 * product_(slot s) U^F.widths(s).

   The *original marked moment* equals D_U^(-1) times the sum of squared norms of these row sums under the source's original hypotheses.

**Critical no-double-count distinction:** c_(u,I) ALREADY contains the actual selected physical W(u) through the source column construction. At the original polynomial expression the moment is sum_u |W(u)|² |P_j(u)P_k(u)|². After source reindexing it is D_U^(-1) sum_u |sum_I c_(u,I)|², WITHOUT a second external |W(u)|². The new native Lean theorem vf919NormalizedColumnSource_NNSCovariance handles THIS finite-column representation; vf919ActualMarkedMoment_eq_exactWeightedNNSCovariance handles the external-W expression under explicit raw source-atom admission. They are two coordinate expressions for an upstream-identified source, not two simultaneous physical costs.

This means the OpenAI mathematical source identification ALREADY EXISTS in the upstream proof. What remains on the RH_Lean side is the concrete cross-repository Lean instantiation of the NNS covariance theorem on those very source-data declarations, and then the separate stronger arithmetic estimate.

## 2. The precise original Lean theorems: three distinct, not conflated, ledgers

1. PrimeCombVisualizationRecurrence.lean proves primeCombAnimationStepSite_eq_insert for every n. The actual displayed frame J_S(n) has kill, first-hit and flip events.

2. It also proves primeCombFramePrefixMass_insert_eq_old_sub_channels. With SIGNED OLD mass KILL_p and FLIP_p (not the positive event counts!), at cutoff X:

    S_new = S_old - KILL_p - 2*FLIP_p.

   First-hit proper multiples have zero animation increment. The prime root p itself was seeded -1 and has zero increment in this displayed frame.

3. The separate frozen Boolean cube (PrimeCombVisualizationDynamics.lean) has

    Frozen_(S+p)(X) = Frozen_S(X) - ReachableParent_S(p,X) + FirstHit_p(X).

   Its first-hit EMPTY parent carries -1 if p<=X; this is the prime-face charge in the frozen subset sum, NOT an additional animation update. Mixing these two root conventions would introduce a spurious -1.

4. On the actual post-square-root phase, p>sqrt(X), every proper child n=pc has 2<=c<=floor(X/p)<p and p²>X. Since the old lower primes are complete on c, the visible site goes from mu(c) to -mu(c), including zero squareful cofactors. Hence every such prime stage obeys

    delta_p S_X = -2 sum_(2<=c<=floor(X/p)) mu(c)
                = -2*( M(floor(X/p)) - 1 ).

   The c=1 prime root was already -1 in the animation seed; the frozen Boolean child contribution includes it. This factor-of-two and root difference is explicit.

## 3. SAME NNS Co/Div ledger, computed before dropping signs

At any displayed integer frame, let U=#positive (+1) seats, L=#negative (-1) seats, S=U-L, K=U+L. For UNORDERED distinct site pairs,

    Co=U*(U-1)/2 + L*(L-1)/2,
    Div=U*L,
    S²=K+2*(Co-Div).

At a new prime stage put delta_n=J_new(n)-J_old(n), delta=Sum delta_n, U_delta=Sum max(delta_n,0), L_delta=Sum max(-delta_n,0). The unnormalized NNS cross-source terms are

    Co(old,delta)=U_old*U_delta + L_old*L_delta,
    Div(old,delta)=U_old*L_delta + L_old*U_delta,
    Co(old,delta)-Div(old,delta)=S_old*delta.

Hence S_new²=S_old²+2*(Co(old,delta)-Div(old,delta))+delta² exactly at EACH PRIME INSERTION. These include every integer and have no independence assumption.

OpenAI analog: Fred's Phi(z)=(Re z-Im z, Re z+Im z) has normalized real energy E(Phi(z))=|z|². For genuine ideal atoms z_alpha, Re(z_alpha*conj(z_beta)) is their normalized Phi dot product. Each real coordinate product splits exactly as Co_0-Div_0.

For one phase-correct Euler pair, take real pairs A=Phi(chi_u(T) A_u(T)) and B=Phi(chi_u(T)*theta_u A_u(Tp)). Then

    E(A-B) = E(A)+E(B)
             -[(Co_x+Co_y)-(Div_x+Div_y)].

This is the *same zero-target signed NNS currency* as the wheel flip. However the OAI masks, original physical product W(u), derivative profiles j+k<=2, restricted ideal rows and theta_u must all remain as originally defined. Certified native phase/leibniz identities are in VF_919_OAI_POLARIZED_EULER_BRIDGE_20261021.lean. The newly authored VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021.lean preserves the actual marked moment conditional on an explicit literal full source-atom equality; that condition is NOT silently discharged.

## 4. Reproducible every-integer 317/1027 audit

The independent script scripts/prime_wheel_oai_simultaneous_317_1027.py processes **all** primes through floor(X/2), *every* live affected integer site, verifies each kill/flip signed delta and exact cross Co/Div, compares the final frame to an independently computed Mobius sieve, and independently tests the frozen Boolean first-hit/parent recurrence.

| Exact property | R=317 | R=1027 |
|---|---:|---:|
| X=R²-1 | 100488 | 1054728 |
| Actual chronological prime stages | 5157 | 43631 |
| After low primes through sqrt(X) | -20940 | -178151 |
| High-prime chronological delta | +20912 | +178518 |
| Final M(X) | -28 | +367 |
| Final diagonal K=sum mu² | 61094 | 641207 |
| Final signed Co-Div across unordered integer pairs | -30155 | -253259 |
| Check K+2(Co-Div)=M² | 784 | 134689 |

Selected stage-by-stage physical integers:

| R | Entering p | First hits (no change) | Square kills | Sign flips | Delta S | New S |
|---:|---:|---:|---:|---:|---:|---:|
| 317 | 2 | 25121 | 25122 | 0 | +25122 | -75364 |
| 317 | 3 | 11164 | 8374 | 5583 | +19540 | -55824 |
| 317 | 5 | 5358 | 2680 | 5359 | +9376 | -46448 |
| 317 | 313 | 1 | 1 | 194 | +5 | -20940 |
| 317 | 317 | 0 | 0 | 192 | +8 | -20932 |
| 1027 | 2 | 263681 | 263682 | 0 | +263682 | -791044 |
| 1027 | 3 | 117191 | 87894 | 58596 | +205086 | -585958 |
| 1027 | 1021 | 2 | 1 | 624 | +9 | -178151 |
| 1027 | 1031 | 0 | 0 | 623 | +10 | -178141 |

At R=317, first post-root prime p=317 gives k=floor(X/p)=316, M(k)=-3, and delta=-2(-3-1)=+8. At R=1027, first post-root prime p=1031 gives k=1023, M(k)=-4, delta=+10.

The script also checks the *distinct* frozen Boolean-face mass through eleven sequential primes; first actual incomplete face occurs at p=17 for R=317 (new frozen mass -2) and p=19 for R=1027 (new frozen mass +2). These are NOT the actual prime-comb animation prefix scores.

## 5. Simultaneous genuine sextic ideal-phase examples

RH_Lean already proves the actual finite Eisenstein ideal exponent labels:
x317=[5,5,1,1], x1027=[1,3,3,5], R317=[0,4,2,0], R1027=[3,1,5,3], with actual sixth-root phases zeta_6^e.

The independent script applies the SAME Phi and zero-target Co/Div sums to these *separate* ideal-labelled families:

| Ideal witness | Diagonal | Positive offCo | Divergent Div | Completed energy |
|---|---:|---:|---:|---:|
| x317 | 4 | 4 | 4 | 4 |
| x1027 | 4 | 2sqrt(3) | 3+2sqrt(3) | 1 |
| R317 | 4 | 2sqrt(3) | 3+2sqrt(3) | 1 |
| R1027 | 4 | 2sqrt(3) | 3+2sqrt(3) | 1 |

Thus completed energies satisfy E=diagonal+offCo-Div on BOTH arithmetic populations, and the four Hecke witness fourth powers sum to 19. Those finite ideal witnesses are NOT OpenAI's complete weighted F.rows and have not been identified with a physical integer wheel stage.

## 6. What is actually new, and what remains open

The prime wheel VISUALIZES, at the level of individual admitted integers, the precise event whose signs produce the NNS mixed covariance. OpenAI's HECKE COMPENSATOR retains the matching abstract signed-difference architecture, but with nontrivial phases, selected ideal slots, and nonuniform physical weights. The current contribution is this exact side-by-side documentation and regression, not a new moment inequality.

The bottleneck is STILL an independent positive power estimate for the complete genuine phase-weighted OAI coefficient or four-point character kernel, including bad/admissible rows, conductor, source masks, derivative profiles, resonant classes, and boundary/unmatched children. Equivalently, establish an independent signed Co/Div payment that survives the full HIGH/LOW detector optimization.

Merely summing the integer-wheel telescope is equivalent to reconstructing M(X); the existing research/TELESCOPE_CANCELLATION_LIMITS.md explicitly documents this obstruction. Complete uniform character phases have a Parseval floor. No PNT/marginal Mobius density theorem by itself pays the weighted Hecke source.

Acceptance: original Lean wheel recurrence + Phi/NNS identities + reproducible all-prime-stage integer audit + separately checked native weighted marked-source theorem; no assertion of a native OpenAI source lift or new zero-free bound without a further proof.
