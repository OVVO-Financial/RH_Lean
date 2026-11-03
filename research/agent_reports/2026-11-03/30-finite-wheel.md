# RH | Finite Wheel & Incidence - 2026-11-03

## Early Research Checkpoint

**Status:** PARTIAL / IN_PROGRESS. Scheduled invocation began 2026-11-03 02:05:02 EST (-0500); RUN_ID_UNAVAILABLE. This is one actual invocation.

### Mathematical Question

Resume CORR4's original coefficient-4 first-owner/daughter mixed expression, not the separate hybrid shell carrier. The accepted fixed-cell saturation (20261102-wheel-1) rules out an unsigned incidence power saving. The earlier sharp scalar corridor (20261101-wheel-1) ends at 478/211 and cannot alone pay the full forward bill. This run investigates additional restrictions from the genuinely nested integer daughter prefixes and the exact one-use square reserve. A precise inverse restriction or a legal adverse example is an eligible outcome; no new inequality is claimed yet.

### Authority And Continuity

Pinned main: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
AGENTS.md: 9fa5e9519e2fb6dde22217aa2a18982dafef373a.
CURRENT_PROOF_CONTRACT.md: 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a.
Research engine: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
Complete return: 16838f7f3c8724b970f8b8ece0bceaab9418066d.
Reports intake: 3171a6da22e83a2cb0884bd728233bed51332e87.

Canonical objective remains the actual-prime VFCanonicalSquareVonKochStatement:
exists C>=0, forall R>=2, |pi(R^2)-VF_can(R^2)|<=C R log R.
Canonical VF, RH and the sharp signed shell improvement remain open.

Today's Owner 20261103-owner-1 and Analytic 20261103-analytic-1 are available. Coordinator, Census, Referee and Lean are TODAY=PENDING at intake; November 2 is YESTERDAY=CARRY_FORWARD. Retrieved all November 2 role reports, latest external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52, and the earlier Wheel CORR4 derivation specifically needed for continuation. Detailed relevant reading and original-source audit are continuing.

Project gain status: Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 accept VERIFIED_ETA only on PR #1073 head 9cbfce5295343bcb411e6d2cb159b59995cd985b. Main still contains the non-strict baseline; no independent re-review or new gain is claimed by this checkpoint. PRs #1073-#1076 are draft/unmerged. Exact source and relevant CI refresh will be recorded in the final section.

### Task And Falsification

deployment_ack: NEXT-WHEEL resumed under current engine and protected rotation. The last three actual Wheel attempts were CORR4 / FINITE-AC / MU-LIFT on November 2. Today's due turn is CORR4; FINITE-AC is next.

The selected source is the exact original endpoint gap G, reciprocal daughter column U, daughter energy E and physical diagonal difference D-P:
2 Mixed = G^2+2 G U-(D-P).
All low-q daughters, original strict cutoff q^2<R, weights 1/q, returned terms and diagonals will be retained. The genuine R=2002 adverse-sign witness is mandatory. No negative-square reserve may be spent twice.

Author checking will be SELF_AUDIT. No Lean execution, Lean edit, proof branch, PR change, other-report edit or agent launch is performed. Final proof, limitations, handoffs and verified publication will follow in this same file.


---

## Final Research Synthesis - Claim 20261103-wheel-1

**Result:** On the original CORR4 mixed carrier, the one-use daughter-square reserve and the actual squarefree overlap diagonal impose an exact integer-valued positivity gate. A daughter can contribute positively only when its Mobius prefix has the same sign as the parent gap, its prime label is strictly smaller than the absolute parent gap, and it overcomes a specified overlap count. The stronger conjecture that every corrected daughter is nonpositive is false: the genuine admitted pair R=125, q=11 contributes exactly 10/11.

**Classification:** PAPER_PROOF / SELF_AUDIT; EXACT_FINITE_COUNTEREXAMPLE; SOURCE_FAITHFUL_RECONSTRUCTION. Independent Referee review: PENDING. New Lean declaration: NONE. New endpoint gain from this claim: UNKNOWN / NOT ESTABLISHED. This is the completion of the scheduled 02:05:02 EST invocation, not another run. Synthesis prepared after the 02:30 EST authority refresh.

### A. Most Important Structural Discovery

The new result concerns the complete original signed bill

    B_R = 2 Mixed_R - 2 E_R
        = G_R^2 + 2 G_R U_R - 2 E_R - (D_R-P_R).

After restoring the actual diagonal overlap, it has the exact decomposition

    B_R = G_R^2 - V_0(R) + sum_(q in S_R) T_q(R),
    T_q = (2/q)(G_R d_q - V_q) - 2 d_q^2.                 (W1)

Here d_q is an integer Mobius prefix, not an arbitrary real frame coordinate. For every genuine admitted daughter,

    T_q > 0
      iff G_R d_q > 0 and |G_R| |d_q| - q |d_q|^2 > V_q. (W2)

Consequently T_q>0 forces q<|G_R| and G_R^2>4qV_q. Section D gives the sharp integer cap and an exact nonnegative reserve, not merely these necessary conditions.

This is a narrow but unconditional restriction on the original mixed source. It neither assumes daughter cancellation nor discards the tail/tail term. Its falsifier is equally important: at R=125, q=11, T_q=10/11>0, while the FULL bill is negative. Thus ownerwise nonpositivity is unavailable even after the literal diagonal has been restored. A joint estimate remains necessary.

### B. Current Authoritative Objective

**Authority.** Main was retrieved at intake and reconfirmed at 2026-11-03 02:29-02:30 EST (07:29-07:30 UTC):

    main = 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015
    tree = fac86ac5944aab6f7b65e88b4f7d3dc1f166f4ef
    AGENTS.md = 9fa5e9519e2fb6dde22217aa2a18982dafef373a
    CURRENT_PROOF_CONTRACT.md = 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a
    task selector = d05c327ae694ea54b599dab0a21032a056b521f1
    broad-search policy = b5c063c51556ba57c4b25bcc380a606fa8daa207
    complete-return contract = 16838f7f3c8724b970f8b8ece0bceaab9418066d
    research engine = 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55
    role prompts = 7366bb71e8a97fd11689a64311c7f590edeb1adf
    dynamic protocol = fe21d2824491fb001726311f736b9825a8f97eca
    multirun policy = 643cfd596116720a8e5b1efc07a6124b55d70946

The canonical target remains VFCanonicalSquareVonKochStatement:

    exists C >= 0, forall integer R >= 2,
    |pi(R^2) - VF_can(R^2)| <= C R log R.

It is OPEN. The exact canonical statement and conditional von Koch interface were checked in research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean, blob 79030d70e8d3e0d08eef9bac53fef95c36eca2fb. The sharp signed square-shell improvement in the proof contract remains OPEN. No RH claim is made.

**Current campaign.** This invocation resumes the Coordinator's latest original-CORR4 ticket, with the Nov 1 scalar threshold and the R=2002 genuine adverse-sign regression. It does not replace this carrier with the hybrid frozen shell of Coordinator C25. The last three observed Wheel invocations on November 2 covered CORR4, FINITE-AC, MU-LIFT. This is the next CORR4 turn; FINITE-AC is next due.

**Project gain versus this claim.** Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 accept VERIFIED_ETA / PR_HEAD_ONLY at draft PR #1073, exact head 9cbfce5295343bcb411e6d2cb159b59995cd985b. This run consumed that verdict, inspected the actual terminal source, and refreshed exact-head CI; it did not independently re-audit the unchanged complete proof. The terminal claims include an existential fixed positive gap below 7/8 for the actual Mertens power bound. Material terminal blobs are b33a4883e1ddb0551b0f11f062bce46680d87450 (VF919NativeStrictMertens.lean) and efbf2780f0b453a702fb8847f2d360d8faf0fa66 (VF919NativeStrictSevenEighths.lean). The previously reported standard-axiom and live-dependency audit is attributed to the Referee, not to this run.

Exact-head workflow results were refreshed at approximately 02:22 EST; open draft heads and bases were reconfirmed at 02:30 EST:

| PR | Exact head | Observed workflow state | Scope |
| --- | --- | --- | --- |
| 1073 | 9cbfce5295343bcb411e6d2cb159b59995cd985b | 13 success; dedicated run 41554561404 success | Accepted strict gain on PR head only; base main |
| 1074 | 5f53bca7d728576efcbbf2762885b7720e89aef7 | 7 success; dedicated run 41561947246 success | Stacked on 1073 branch; stronger scope review pending |
| 1075 | acaa66c510259a6722e3d5590106fcb9b7d50181 | 8 success, 1 failure; dedicated run 41580316113 failure | Stacked; no green dedicated proof at this head |
| 1076 | f676c9b13960f8c80b68bdf35a5f04b07370e228 | 8 success; dedicated run 41579190117 success | Stacked on 1073 branch; stronger scope review pending |

All four remain draft/unmerged. Main includes the merged address interface #1070, parity obstruction #1071, and non-strict native 7/8 replay #1072. This claim changes none of those statuses. Successful CI is not independent acceptance of an unreviewed stronger scope.

**Continuity actually consumed.** Intake reporting head was 3171a6da22e83a2cb0884bd728233bed51332e87. The following exact report bytes were retrieved and read; verification here means source retrieval, not independent validation of every reported theorem.

| Role / report date | Blob | Relevant claims and status |
| --- | --- | --- |
| Coordinator, Nov 2, both mirrors | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | 20261102-coordinator-1/2/3; latest invocation 23:09 EST, receipt 23:36 EST; C20-C25 paper results and exact next CORR4 ticket |
| Owner, Nov 2 | abfe546d72b151f4cd200fc61de3197efe23a65c | 20261102-owner-1/2/3; kernel and full signed-sector warnings |
| Analytic, Nov 2 | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 20261102-analytic-1/2/3; repaired inverse constant, frozen activation error |
| Wheel, Nov 2 | abf8ac8c22a708886183849552c90dd62787ac8d | 20261102-wheel-1/2/3; 02:10, 10:24, 18:12 EST syntheses |
| Census, Nov 2 | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 20261102-census-1/2/3; 03:22, 11:04, 19:06 EST; exact affine and burst falsifiers |
| Referee, Nov 2 | 814af1684df66e6ac99b8df1f102cb592b316f89 | 20261102-referee-1/2/3; latest checkpoint 20:13 EST; scoped saturation/parity acceptance and PR1073 verdict |
| Lean, Nov 2 | 02d19d792e26f072004cb5909f149538752626e9 | 20261102-lean-1/2/3; latest 21:08 EST section is PARTIAL, not an invented final handoff |
| Owner, Nov 3 | 5c085d12ca455327b2a9ab42d7e55a1b6b2d631b | 20261103-owner-1; 00:24 EST synthesis; SAT dilation and complete-return cancellation |
| Analytic, Nov 3 | 7a167a551ca047c0b5bccf6220f40152d78ea176 | 20261103-analytic-1; 01:25 EST synthesis, 01:26 receipt; NYMAN corrected-coefficient remote-tail bound |

At intake and the 02:30 EST refresh, today's Coordinator, Census, Referee and Lean reports were absent: TODAY=PENDING; YESTERDAY=CARRY_FORWARD for those roles. Owner and Analytic were TODAY=AVAILABLE, unchanged at refresh. No scheduled execution is inferred from absence or configuration.

The specific earlier CORR4 continuation, 20261101-wheel-1, was retrieved at blob 707a31ba0fa7b4a04266730236a9e79d4947e91a. The external inbox research/agent_reports/EXTERNAL_HANDOFFS.md was retrieved at blob 038018145c0fddb2f6306c0712373adf9cd1ea52; its newest entries are no later than October 18. They supply historical safeguards, not a newer routing override.

**Relevant retained findings.** Wheel Nov 1's sharp scalar record threshold is 478/211, with reserve 13/3600 at coefficient 9/4 under its explicit record hypothesis; that does not pay the whole coefficient-4 consumer. Wheel Nov 2 claim 1's genuine hybrid (q,p)=(3,5) affine family, m=14+25t and n=5+9t, has gap 1 and first fresh owner 2; its accepted absolute-incidence saturation does not prove a signed lower bound or a map to this prefix carrier. Claim 2's FINITE-AC parity packet has the exact R=5 balance 10-8-8+6=0 and is accepted/merged in its scope. Claim 3's sharp finite mu-lift radius s^k and first defect mu(s)^k remain a paper continuation, not a summatory recurrence.

Referee 2 repaired Analytic 2's inverse constant to 2/(9 sqrt(3)); the original submitted 1/(3 sqrt(3)) is not carried forward. Coordinator C25's physical/frozen energy error is <=65 H^2, but no occurrence-preserving bridge to the present mixed source is established. Census's R=18988 witness L=138>floor(sqrt(R))=137 refutes its literal burst bound; R=53 remains a lower-spreading counterexample. Those claims are not rerun or silently strengthened here.

### C. Structural Mechanism Investigated

Three distinct moves were compared.

1. **Scalar or nested-support control alone.** Resume the existing sharp frame corridor and the nested-square source modules. They retain useful identities but do not supply the missing all-scale joint upper estimate. No repeat wheel enlargement or unsigned incidence scan was performed.
2. **Exact diagonal overlap plus integer daughter coordinates.** Keep G, each literal d_q, every weight 1/q, and the full -2E credit. Expand D-P before any inequality, then optimize each combined cross/energy term over the integer lattice. This is the selected derivation below.
3. **Stronger per-daughter sign payment.** Test the falsifiable assertion T_q<=0 on every genuine admitted daughter. The exact R=125, q=11 counterexample retires it. The weaker integer cap and full reconstruction survive.

The new information is lattice-valued Mobius prefixes and physical overlap counts, not a new distribution theorem or a new matching. The completed-square algebra itself is elementary; its source-faithful application and the legal falsifier are the contribution. Unique factorization is used by the Mobius/squarefree definitions, but no stronger multiplicative independence is claimed.

### D. Exact Theorem Statement

Fix an integer R>=56. All sums below are finite unless explicitly stated otherwise. Define

    X = R^2-1,
    S_R = {q : q is an odd prime and q^2<R},
    Y_q = floor(X/q^2),
    M(x) = sum_(1<=n<=x) mu(n),
    d_q = M(Y_q) in Z,
    G = M(X)-M(R-1) in Z,
    U = sum_(q in S_R) d_q/q,
    E = sum_(q in S_R) d_q^2,
    a(n) = sum_(q in S_R) (1/q) 1_(n<=Y_q),
    t(n) = 1_(R<=n),
    D = sum_(1<=n<=X) mu(n)^2 (t(n)+a(n))^2,
    P = sum_(1<=n<=X) mu(n)^2 a(n)^2,
    V_0 = sum_(R<=n<=X) mu(n)^2,
    V_q = sum_(R<=n<=Y_q) mu(n)^2.

The exact source owner set also requires q<=R-1; that is automatic from q^2<R for these primes. Admission is STRICT. If q^2=R the daughter is excluded. For admitted q, q^2<=R-1 and hence Y_q>=R+1, so the overlap interval is well-defined without a convention-changing clipping step.

Let Mixed denote lowOwnerPrefixTailMixedRawCellMass R. Put

    B = 2 Mixed - 2 E,
    J_q = 2Gd_q/q - 2d_q^2,
    T_q = J_q - 2V_q/q,
    A = |G|.

**W1: exact physical reconstruction.**

    D-P = V_0 + 2 sum_(q in S_R) V_q/q,
    B = G^2-V_0 + sum_(q in S_R) T_q.

**W3: sharp integer cap.** For every integer G, positive integer q and integer d, set

    k_q(A) = floor((A+q)/(2q)),
    C_q(A) = 2 k_q(A) (A-q k_q(A))/q,
    z_q = G/(2q),
    e_q = distance(z_q, Z).

Then

    2Gd/q - 2d^2 <= C_q(A)
                   = A^2/(2q^2)-2e_q^2.                (W3)

Equality is attained at d=sign(G) k_q(A), with the usual additional nearest integer in a tie; if G=0, d=0 is a maximizer. On the actual arithmetic source define

    r_q = 2[(d_q-z_q)^2-e_q^2] >= 0.

There is the exact identity

    B = G^2-V_0
        + sum_(q in S_R) [C_q(A)-2V_q/q-r_q].           (W4)

**W2: exact positivity gate.** For the actual d_q and V_q>=0,

    T_q>0 iff Gd_q>0 and A|d_q|-q|d_q|^2>V_q.

In particular,

    T_q>0 implies d_q!=0, q|d_q|<A, q<A,
                       and A^2>4qV_q.                 (W5)

If q>=A then T_q<=-2V_q/q<=0. If A^2<=4qV_q then T_q<=0, even before using integrality. The integer envelope itself permits a positive corrected contribution precisely when k_q(A)(A-qk_q(A))>V_q. This last criterion concerns the envelope, not a claim that the actual d_q attains it.

**W6: high-label truncation with the FULL diagonal retained.** For any integer Q>=2 set

    B_<Q = G^2 + sum_(q in S_R, q<Q) J_q - (D-P).

Then

    B-B_<Q
      = sum_(q in S_R, q>=Q) J_q
      <= sum_(q in S_R, Q<=q<A) C_q(A)
      <= (A^2/2) sum_(q in S_R, q>=Q) 1/q^2
      <= A^2/[2(Q-1)].                                 (W6)

If Q>=A, B<=B_<Q. The exact high-label reserve is

    sum_(q in S_R, q>=Q) J_q
      = (G^2/2) sum_(q in S_R, q>=Q) 1/q^2
        -2 sum_(q in S_R, q>=Q) (d_q-G/(2q))^2.         (W7)

This is one-sided control of the original combined cross/energy contribution, not an absolute bound on U, not a bound on a hybrid shell, and not a second expenditure of the daughter square reserve.

### E. Mathematical Proof And Source Bridge

**1. Exact source dictionary.** The inspected declaration corr4_mixed_tail_eq_actual_endpoint_gap proves, for R>=56,

    2 Mixed = G^2 + 2 G U - (D-P).                      (W8)

Its imports supply the full signed first-owner telescope and the reciprocal-prefix Fubini identity. Thus the fresh first-owner labels p and signatures are already fully summed in Mixed. Our q labels index literal q^2 daughters, not fresh first owners; no identification p=q is made.

The common-clock coefficients a(n) are precisely lowOwnerReciprocalDaughterWeight. The tail coefficient t(n) is lowOwnerFarTailWeight. The squarefree factor is mu(n)^2, including its zero values on squareful n. These are source definitions, not replacement masks. The source denominator is q and the raw daughter energy is the UNSHIFTED M(Y_q)^2.

**2. Diagonal identity.** Since t(n)^2=t(n),

    (t(n)+a(n))^2-a(n)^2 = t(n)+2t(n)a(n).

Multiply by mu(n)^2 and sum over the actual common clock 1<=n<=X. Finite interchange of the n and q sums gives

    D-P = V_0 + 2 sum_q (1/q) sum_(R<=n<=Y_q) mu(n)^2.

This is W1's first identity. Subtract 2E in W8 and distribute it once over q to obtain its second identity. The strict owner condition gives

    (R+1)q^2 <= (R+1)(R-1) = X,

hence Y_q>=R+1; at the excluded boundary q^2=R, Y_q=R-1. No floor is replaced by a real approximation.

**3. Integer optimization.** For any integer d,

    2Gd/q - 2d^2 = G^2/(2q^2)-2(d-G/(2q))^2.

The maximum over the integer lattice occurs at a nearest integer to G/(2q). The nonnegative nearest-integer magnitude, choosing the upper integer at a half-integer tie, is floor((A+q)/(2q)). Sign reflection handles G<0; G=0 is direct. This proves W3, including attainment. Subtracting the minimum squared distance gives r_q>=0 and W4.

**4. Positivity restriction.** Multiplying T_q>0 by q/2>0 gives

    Gd_q - q d_q^2 > V_q >= 0.

This forces Gd_q>0 and d_q!=0, after which Gd_q=A|d_q|. This proves both directions in W2. Let h=|d_q|>=1. From Ah-qh^2>V_q>=0 we get qh<A and therefore q<A. Also

    A^2 - 4qV_q
      = (A-2qh)^2 + 4q(Ah-qh^2-V_q) > 0.

The integrality strengthening A^2>=4q(V_q+1) follows because Ah-qh^2-V_q is a positive integer. For q>=A, the integer cap is zero (including the A=q tie), giving T_q<=-2V_q/q. The real cap directly gives the other nonpositivity criterion.

**5. Truncation.** B_<Q deliberately keeps the ENTIRE D-P, including high-label overlap diagonals. Subtraction therefore leaves exactly the high-label sum of J_q, not T_q. For q>=A, J_q<=0; for the remaining terms apply W3, C_q(A)<=A^2/(2q^2), and

    sum_(n>=Q) 1/n^2 <= integral_(Q-1)^infinity x^(-2) dx
                      = 1/(Q-1).

This proves W6. W7 is termwise completion of the same squares. No prime number theorem, independence assumption, density asymptotic, lower-envelope hypothesis, or Mertens bound is used in W1-W7.

**Source inventory.** All following blobs are on the pinned main. File paths beginning with GLOBAL_, CORR4_, CANONICAL_, OAI78_ or LOW_ are under research/; the SignedTransport path is shown in full.

| File | Blob SHA | Verified role |
| --- | --- | --- |
| RHLean/Proof/SignedTransportAmplificationAudit.lean | 746f35f126f36e024d39e38c92dde30aabca266b | rawQ2ChildCutoff and unshifted rawQ2ChildEnergyReal definitions |
| CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 | exact low-owner carrier and E |
| GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 | U, a(n), common-clock finite Fubini |
| GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 | t(n), actual signed site, owner differences |
| GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean | 36141a8caec5f99d6c40cb72ae1fdbcf6f462b82 | full diagonal and first-owner reconstruction |
| GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean | 5ca177548e91dd8bc6535e9913b29dc81cdfccea | literal cell population and multiplicities |
| GLOBAL_RETURNED_CORE_ONE_AMPLITUDE.lean | b69a36ec4305a9309a5212358569905a968f4d63 | full returned amplitude |
| GLOBAL_RETURNED_CORE_Q2_DAUGHTER_FIRST_OWNER_GRAM.lean | b57a3e9030445262ec847ca0e20a60bc35ff127c | actual daughter energy reconstruction |
| GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean | ac8015a1dd87aea23d35d57f5102efd38f4a105b | reciprocal-prefix payment |
| GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 | Mixed with BOTH cross orientations and tail/tail |
| GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf | P and exact mixed remainder |
| GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean | ba95beda901719afaabca9011b8dbae6fc69662d | G and complete coefficient dictionary |
| CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean | a4abeb13653076bedd8e1173c933ee3324bfea26 | W8, scalar record plateau |
| CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a | conditional full mixed-power consumer |
| CORR4_OAI_POWER_GRAM_EQUIVALENCE_20261025.lean | 49a3ecb8fbb934d58c1d171ce1cc0275f1e6c8b9 | exponent currency |
| CORRELATION_FOUR_TERMINAL_BRIDGE.lean | 0193a86c2d464044b0cad298acba3f11c104838c | original coefficient-4 consumer |
| CORR4_FRAME_ONLY_INVERSE_20261026.lean | fe318e29f348644bdd0896eba897a1d12b8d38ec | prior scalar no-go comparison |
| OAI78_CORR4_NESTED_SQUARE_RESERVES_20261028.lean | 159b3c8053d6ecc7ee412a68424f1062d216f81e | existing nested-square identities, not a new estimate here |
| OAI78_CORR4_OWNER_TAIL_PAID_20261028.lean | 03c05e38fb2415105de9cccd3680b03c21c4be5c | existing input-dependent absolute reciprocal tail |
| LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean | 72d66f61b3eeb000117ecdac393572558bb7c378 | source transport safeguards |

The repository's existing compiled identities are reused as established inputs. W1-W7 and the new falsifier are not represented as newly compiled declarations.

### F. Structural Consequence

The following configurations are excluded on the genuine source: a positively contributing corrected daughter with d_q=0; one opposing the sign of G; one with q>=|G|; and one whose overlap count satisfies 4qV_q>=G^2. More precisely, positivity requires the integer h=|d_q| to lie in the finite set

    {h>=1 : Ah-qh^2>V_q}.

This retains a distinction that an unrestricted real-vector model loses. For example, when G is nonzero and q>|G|, the real choice d=G/(2q) gives positive J=G^2/(2q^2), whereas EVERY integer d gives J<=0. The squarefree overlap further narrows the allowed set.

The restriction is arithmetic but modest. It does not assert that the remaining integer choices can be realized independently by genuine Mobius prefixes. It supplies no Hall matching, no favorable graph spectrum, no universal sign reversal, and no estimate on the number or coherence of the surviving positive daughters.

### G. Signed And Quantitative Relevance

The target here is the existing mixed-power bill

    forall R>=56, B_R <= C R^(4 beta_out).

By mertensPowerBound_of_corr4MixedTailBill in the source above, C>=0 and beta_out>=1/2 suffice for MertensPowerBound beta_out. This is an existing conditional consumer, not a theorem newly proved by this report.

W6 makes one useful ONE-SIDED reduction without a daughter-amplitude hypothesis. If an independently established incoming bound is

    |M(n)| <= C_in n^beta,  n>=1,  beta>=1/2,

then |G|<=2C_in R^(2 beta). For fixed 0<theta<1/2 and Q(R)=ceil(R^theta), the high-label contribution in W6 is

    B_R - B_<Q(R) = O_upper(R^(4 beta-theta)).

The constant is uniform in R, with finitely many small roots absorbed. The cutoff grows, and the factor 1/(Q-1) is retained before taking this asymptotic notation. This estimate spends the high-label -2d_q^2 terms exactly once.

If, IN ADDITION, there were a new independent low-label theorem

    B_<Q(R) <= C_low R^(4 beta-eta_low),  all R>=56,

with fixed eta_low>0, then setting delta=min(theta,eta_low)>0 would give the full mixed bill at beta_out=beta-delta/4, provided beta_out>=1/2. Every term in D-P remains present in B_<Q; omitting its high-label portion would change the stated reduction.

This is a conditional quantitative interface, NOT an achieved gain. The new high-label estimate alone does not improve beta. Existing input-dependent tail bounds can be stronger in Q than W6 when additional Mertens information is available; no best-known tail claim is made. The precise novelty is the integer cutoff, overlap gate, and reserve-preserving source reconstruction.

**Cross-route check.** Owner's mu*kappa_R kernel is a HYBRID physical-increment convolution. Coordinator C25 compares that increment's complete dyadic energy with a frozen shell covariance up to 65H^2. Our d_q instead sums every mu(n) for 1<=n<=floor((R^2-1)/q^2), and G is the entire tail R<=n<=R^2-1 at one root. The indexing intervals, occurrence labels and quadratic normalizers differ. No telescoping map retaining all anchors and cross-root terms has been proved here; the word "daughter" is not a bridge. Likewise today's NYMAN remote-tail estimate is a Hilbert-norm statement in a periodic basis, not a supplied bound for B_<Q. Neither result is imported as payment.

### H. Falsification And No-Circularity Review

**H1. Legal counterexample to universal per-daughter payment.** Take R=125 and q=11. Strict admission holds: 121<125. Exact values are

    X=15624, Y_11=129,
    M(15624)=-19, M(124)=-1, G=-18,
    d_11=M(129)=-1,
    V_11=2, supported exactly at n=127 and n=129.

Therefore

    J_11 = 2*(-18)*(-1)/11 - 2 = 14/11,
    T_11 = (2/11)(18-2)-2 = 10/11 > 0.

The sharp integer cap C_11(18)=14/11 is attained. The overlap diagonal is not missing.

The FULL source at this same root is

    S_R={3,5,7,11},
    (d_3,d_5,d_7,d_11)=(-8,-3,-5,-1),
    U=-4703/1155, E=99, V_0=9424,
    D-P=11818358/1155,
    sum_q T_q=-28372/33,
    B=-328672/33 < 0.

Thus the counterexample refutes ONLY universal per-daughter nonpositivity. It does not refute a global upper bound, and the negative full bill is not evidence for an all-scale theorem. The first positive corrected daughter in the frozen held-out range is R=306, q=17: G=-63, d=-3, V=12, T=48/17.

**H2. Exact regression design and scope.** The script's frozen design was discovery roots 56..256, held-out roots 257..2048, null T_q<=0 for every genuine daughter. The rejection rule was one exact positive T_q. Additional checks were fixed for the integer cap, full reconstruction, strict q^2=R boundaries and the inherited R=2002 witness. This is same-author finite validation, not an independent Referee or statistical-independence claim.

The executed final version uses exact integers and Fraction arithmetic. Results:

| Check | Result |
| --- | --- |
| Scalar integer cases | 1,075,963 triples: -80<=G<=80, 1<=q<=41, -81<=d<=81; cap and raw positivity equivalence passed |
| Genuine root range | 1,993 roots, 56<=R<=2048; linear Mobius sieve through 4,194,303 |
| Actual daughter slots | 18,289 |
| Positive raw J slots | 4,255 |
| Positive corrected T slots | 556 |
| Roots with some positive T | 11 discovery roots; 396 held-out roots |
| Exact full bill reconstruction | Passed at every tested root |
| Direct original mixed-pair reconstruction | Passed at R=56,57,121,122,125,317 |
| Strict admission boundaries | q=11 at R=121/122, q=13 at 169/170, q=17 at 289/290 |
| Independent arithmetic implementation | Trial-factor mu checked through 1000; independent trial sums reproduced all R=125 witness values |
| Cutoff reserve identity | W7 checked at fixed small Q and at A, A+1, and the full-owner endpoint |
| Required inherited adverse regression | R=2002 reproduced exactly |

The direct mixed check computes the literal unordered pair sum on the original common clock using integer-scaled reciprocal weights. It accumulates both prefix/tail orientations and the tail/tail term, separately from the endpoint formula; it also independently accumulates D and P. The first-owner/signature reassembly to these pairs uses the existing main theorem, not a newly implemented alternative owner classification.

At R=2002, the inherited data are

    G=208, E=8367,
    q=(3,5,7,11,13,17,19,23,29,31,37,41,43),
    d=(-52,-52,-32,4,-36,1,-4,2,7,-14,-17,-8,-2),
    U=-233438518043839321/6541380665835015,
    G*U<0.

That adverse sign is preserved; no universal sign of GU is inferred. For contrast, the actual R=125 example has G<0 and U<0, hence GU>0.

Execution environment: Linux x86_64; observed Python 3.12.14; standard library only. Full executed reproducer is included below. Its SHA256 is

    082d94da1ae13d2f5b25b27b1de77affd549d80d8af6f0e647d6aff0a864a3b3

The SHA256 of compact JSON rows [R,G,E,str(U),str(B)] in root order is

    f676180acb1f9ff1d9df26f75b20d2d3bfba889d74fd47ea03618ba36063b985

Finite tests disprove the universal sign claim and check implementation consistency; the all-scale cap and reconstruction are justified by the proof in E, not extrapolated from the census.

**H3. Why integrality alone does not remove the leading frame size.** Since e_q<=1/2,

    0 <= A^2/(2q^2)-C_q(A) <= 1/2.                     (W9)

Hence the total integer envelope differs from its real maximum by at most #S_R/2. Taking A=R as an envelope parameter gives

    (sum_(q in S_R) C_q(R))/R^2
      -> (1/2) sum_(q odd prime) 1/q^2 > 0.

Indeed #S_R<=sqrt(R), and the prime reciprocal-square tail tends to zero by comparison with the integer series. This is a theorem about the cap, NOT an assertion that the genuine parent G equals R or that all cap maximizers form genuine Mobius prefixes. It only rules out claiming a fixed proportional leading improvement from nearest-integer rounding alone. Squarefree diagonals and dependencies between actual prefixes could still matter; no such joint gain has been proved here.

**H4. Novelty and exact scope.** Scoped repository searches for lowOwnerPrefixTailMixedRawCellMass with "round"/"floor"/"nearest integer", and daughter-energy with "integer cap"/"quantized", found no equivalent integer-credit gate in the inspected sources. The relevant original declarations, prior Wheel continuations, scalar no-go, nested-square-reserve module and OAI78 owner-tail module were compared. Generic square completion, diagonal subtraction, prefix Fubini and the mixed consumer are established machinery and are NOT claimed as newly discovered theorems. This is a scoped repository-novel application and exact falsifier, not a claim of general mathematical priority.

No assumed admissibility condition is equivalent to B being small. No negative reserve is reused. No absolute survivor count is substituted for a signed estimate. No omitted U^2 term is silently discarded: the exact prefix/mixed source split has already assigned that term to the compiled reciprocal-prefix part. The present decomposition is of the mixed part only; the existing consumer restores the full coefficient accounting.

### I. Conceptual Interpretation

A positive corrected daughter is a specific integer alignment, not merely a populated incidence class: its signed prefix must align with the parent gap strongly enough to pay both its own square and its physical overlap diagonal. This yields a precise finite set of permitted magnitudes at each prime label. The R=125 example shows that genuine arithmetic does realize such an alignment, even at the edge of low-owner admission.

The surviving research question is about the JOINT organization of those alignments together with G^2-V_0 and all negative daughters. Treating each corrected daughter as automatically paid is false. Treating their integer caps as if they already contain an exponent saving is also unjustified.

### J. Competing Structural Hypotheses

| Hypothesis | Verdict from this invocation | Next mathematical question |
| --- | --- | --- |
| Every genuine corrected daughter has T_q<=0 | REFUTED at R=125,q=11 | Retain exact fixture; do not revive by omitting V_q or changing signs |
| Integrality plus the actual overlap provides a uniform positivity gate | PAPER_PROVED / SELF_AUDIT | Independent check of W1-W7 and the source dictionary |
| Integer rounding alone supplies a fixed fractional reduction of the leading cap | Unsupported; W9 shows the cap mechanism cannot supply it | Seek dependencies among actual prefixes, not arbitrary simultaneous maximizers |
| High-label square credit can be used before estimating individual daughters | PAPER_PROVED one-sided W6-W7 | Compare with existing stronger input-dependent tails; no duplicated credit |
| C25 shell covariance already pays original CORR4 | NO BRIDGE ESTABLISHED | Any future transfer must restore the different intervals, anchors and cross-root interactions |
| A joint low-label estimate survives | OPEN, not falsified by the local counterexample | Prove L's precise bound or identify a genuine joint arithmetic obstruction |

### K. Specialist Handoffs

These are asynchronous requests recorded in this authorized report, not launched agents or changes to anyone else's report.

| Recipient | Exact requested action | Dependencies and acceptance boundary |
| --- | --- | --- |
| Proof Architect / Coordinator | Register 20261103-wheel-1 as paper-level W1-W9 plus exact local falsifier; retain FINITE-AC as next Wheel turn | Do not alter PR1073's existing scoped VERIFIED_ETA verdict or count this as a new gain |
| Owner Payment / Arithmetic Structure | Check that W1 uses the literal original prefix/tail diagonal; investigate whether nested-prefix arithmetic couples the surviving positive T_q to negative original terms | Keep q daughter labels distinct from first-owner p and from the hybrid mu*kappa_R carrier; no second use of -2E |
| Analytic Type II | Assess the explicitly quantified B_<ceil(R^theta) bound in L on its full signed carrier; identify any genuinely new low-label supplier | A bound on |G|, an absolute U tail, NYMAN's remote tail or C25 alone does not settle this |
| Prime Census Laboratory | Independently reproduce the small R=125,q=11 fixture from trial factorization and the literal mixed-pair formula; optionally reproduce R=306,q=17 as a separate held-out fixture | No larger scan requested. Reject the local sign conjecture iff exact T>0; report full B so it is not confused with a global counterexample |
| Adversarial Referee | Audit W1-W9 claim-first where practicable, nearest-integer ties, G=0, q>=A, strict q^2<R, and complete diagonal retention in B_<Q | Author checks are SELF_AUDIT. Separate verdicts for exact identities, local falsifier and conditional consumer; no endpoint gain is submitted |
| Lean Verification | After independent acceptance and Coordinator prioritization, consider a small integer-cap/source-diagonal interface and the R=125 regression | Not an immediate implementation request; do not launch a competing speculative proof branch or displace active exact-head repair/audit work |

### L. First Independently Missing Theorem

For an independently supplied incoming Mertens exponent beta>=1/2, select fixed theta in (0,1/2). The first unpaid sufficient statement in the derivation is:

    exists eta_low>0 and C_low>=0 such that, for ALL integers R>=56,

    G_R^2
      + sum_(q in S_R, q<ceil(R^theta))
          [2 G_R M(floor((R^2-1)/q^2))/q
           -2 M(floor((R^2-1)/q^2))^2]
      -(D_R-P_R)
      <= C_low R^(4 beta-eta_low).                    (W10 OPEN)

The parameters must be independent of R; delta=min(theta,eta_low) must also satisfy beta-delta/4>=1/2 for the stated consumer. W6 would then pay the remaining high-label bill. W10 is a substantial signed, target-strength supplier, not a consequence of the integer cap or a new name for an already accepted theorem. No proof of W10 is offered, and no circular assumption is used to infer an output exponent.

A sharper source-specific relation between the genuine cap defects r_q, the overlap counts V_q and the parent G is a possible intermediate research direction. It must yield an independently proved numerical restriction on the full expression, not define "admissible" to mean W10 holds.

### M. Next-Run Resume Capsule

    ENGINE_VERSION: 20261101
    MAIN: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015
    POLICY_SHA: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55
    RUN: scheduled 2026-11-03 02:05:02 EST (-0500); RUN_ID_UNAVAILABLE
    CLAIM: 20261103-wheel-1
    TASK: NEXT-WHEEL / CORR4 original mixed source
    TRIGGER: Coordinator 20261102-coordinator-3 and protected rotation
    ORIGINAL_SOURCE: pinned main, exact file/blob table in E
    ESTABLISHED_INPUTS: W8 and compiled prefix/first-owner Fubini;
      Nov 1 scalar corridor (with its hypothesis), prior R=2002 fixture
    ACTUAL_RESULT: W1-W9 paper derivation; R=125 local sign counterexample
    NEW_ARITHMETIC_INPUT: integer Mobius daughter prefixes and literal
      squarefree overlap counts; no distribution assumption
    LAST_JUSTIFIED_STEP: W6 combined high-label truncation, full D-P retained
    FIRST_UNSUPPORTED_STEP: W10 uniform signed low-label power saving
    REVIEW_STATE: SELF_AUDIT; independent Referee PENDING; no Lean execution
    PROJECT_ETA_GATE: VERIFIED_ETA / PR_HEAD_ONLY on unchanged PR1073
    THIS_CLAIM_NET_ENDPOINT_GAIN: UNKNOWN / NOT ESTABLISHED
    DISTINCT_FAILURE: universal T_q<=0 false; integer cap alone retains
      leading reciprocal-square size; C25-to-CORR4 bridge not supplied
    ROUTE_COVERAGE: prior CORR4 -> FINITE-AC -> MU-LIFT; now CORR4
    NEXT_DISTINCT_ROUTE_DUE: FINITE-AC
    NEXT_FINITE_AC_RESUME: 20261102-wheel-2 accepted exact parity reassembly,
      main merged #1071; retain R=5 full 10-8-8+6 cancellation and original
      square clock; seek a genuinely signed cross-sector restriction
    NEXT_CORR4_RESUME: W4 actual cap-defect organization and W10,
      not another wheel, unchanged scalar scan, or re-proposal of T_q<=0
    MU_LIFT_CARRY: 20261102-wheel-3 sharp s^k radius and first defect,
      still no all-depth summatory cancellation or recurrence
    REPRODUCER_SHA256:
      082d94da1ae13d2f5b25b27b1de77affd549d80d8af6f0e647d6aff0a864a3b3
    ROOT_ROWS_SHA256:
      f676180acb1f9ff1d9df26f75b20d2d3bfba889d74fd47ea03618ba36063b985

**Execution limitations.** Repository reads used pinned GitHub content and API evidence; an attempted local checkout was unavailable through the environment's transport, so no local build or checkout-based CI claim is made. No Lean process was run. No Lean file, proof branch, PR, other role's report, shared registry, schedule or main branch was changed. No sub-agent was launched. This report is the only remote write. Independent review and any future formalization remain separate work.

**Publication trail.** The early checkpoint was published in commit 6508c722e129674c0d5dca5bd8c0cff4c6de9e82 with blob cd7e15aa989a86696344555acca571e806688857 and was fetched back with an exact content match. Its text is preserved above. Final publication verification is appended only after the completed report has been committed and read back.

### Executed Reproducer

The following is the complete final Python source. The code-fence contents, including its final newline, have the SHA256 recorded above. It emits exact rational witnesses and the deterministic root-row digest; finite output is not a proof of W10.

```python
"""Exact regression for the 2026-11-03 CORR4 integer-credit investigation.

Discovery roots: 56..256. Frozen holdout: 257..2048.
Null to falsify: every diagonal-corrected daughter contributes <= 0.
Also test the proved integer cap, full reconstruction, q^2=R boundaries,
and the mandatory R=2002 sign witness. No asymptotic inference from scans.
"""

from array import array
from fractions import Fraction
from math import isqrt, prod
import hashlib
import json


def sieve(limit):
    least = array("i", [0]) * (limit + 1)
    mu = array("b", [0]) * (limit + 1)
    mu[1] = 1
    primes = []
    for n in range(2, limit + 1):
        if not least[n]:
            least[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            m = n * p
            if m > limit:
                break
            least[m] = p
            if n % p == 0:
                break
            mu[m] = -mu[n]
    mertens = array("i", [0]) * (limit + 1)
    sqfree = array("i", [0]) * (limit + 1)
    m_total = s_total = 0
    for n in range(1, limit + 1):
        m_total += mu[n]
        s_total += mu[n] * mu[n]
        mertens[n] = m_total
        sqfree[n] = s_total
    return mu, mertens, sqfree, primes


def trial_mu(n):
    result = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result


def scalar_cap_numerator(a, q):
    k = (a + q) // (2 * q)
    return 2 * k * (a - q * k)


def direct_mixed(r, owners, mu):
    """Ordered-prefix accumulator of the actual unordered mixed pairs."""
    x = r * r - 1
    denominator = prod(owners)
    cutoffs = [(x // (q * q), denominator // q) for q in owners]
    prefix_sum = tail_sum = mixed_twice = diagonal = prefix_diagonal = 0
    for n in range(1, x + 1):
        a = sum(weight for cutoff, weight in cutoffs if n <= cutoff)
        prefix = a * mu[n]
        tail = denominator * mu[n] if n >= r else 0
        mixed_twice += 2 * (tail * tail_sum + tail * prefix_sum + prefix * tail_sum)
        diagonal += (prefix + tail) ** 2
        prefix_diagonal += prefix ** 2
        prefix_sum += prefix
        tail_sum += tail
    return (Fraction(mixed_twice, denominator ** 2),
            Fraction(diagonal - prefix_diagonal, denominator ** 2))


def main():
    mu, mertens, squarefree, primes = sieve(2048 ** 2 - 1)
    assert all(mu[n] == trial_mu(n) for n in range(1, 1001))
    scalar_checks = 0
    for g in range(-80, 81):
        for q in range(1, 42):
            cap_numerator = scalar_cap_numerator(abs(g), q)
            for d in range(-81, 82):
                numerator = 2 * d * (g - q * d)
                assert numerator <= cap_numerator
                assert (numerator > 0) == (g * d > 0 and q * abs(d) < abs(g))
                if q >= abs(g):
                    assert numerator <= 0
                scalar_checks += 1

    first_raw = {"discovery": None, "holdout": None}
    first_corrected = {"discovery": None, "holdout": None}
    roots_with_positive = {"discovery": 0, "holdout": 0}
    counts = {"owners": 0, "positive_raw": 0, "positive_corrected": 0}
    samples = {}
    near_boundary = []
    root_rows = []
    small_primes = [q for q in primes if 2 < q <= isqrt(2047)]
    for r in range(56, 2049):
        x = r * r - 1
        owners = [q for q in small_primes if q * q < r]
        g = mertens[x] - mertens[r - 1]
        a = abs(g)
        v0 = squarefree[x] - squarefree[r - 1]
        u = Fraction(0)
        energy = 0
        overlap = Fraction(0)
        corrected_total = Fraction(0)
        capped_total = Fraction(0)
        rows = []
        any_positive = False
        region = "discovery" if r <= 256 else "holdout"
        for q in owners:
            y = x // (q * q)
            assert y >= r
            d = mertens[y]
            v = squarefree[y] - squarefree[r - 1]
            raw_numerator = 2 * d * (g - q * d)
            corrected_numerator = raw_numerator - 2 * v
            cap_numerator = scalar_cap_numerator(a, q)
            assert corrected_numerator <= cap_numerator - 2 * v
            if a * a <= 4 * q * v:
                assert corrected_numerator <= 0
            if corrected_numerator > 0:
                assert g * d > 0 and q * abs(d) < a
                assert a * a > 4 * q * v
                any_positive = True
                counts["positive_corrected"] += 1
            if raw_numerator > 0:
                counts["positive_raw"] += 1
            if q >= a:
                assert raw_numerator <= 0
            row = {"R": r, "q": q, "X": x, "Y": y, "G": g,
                   "M_X": mertens[x], "M_Rm1": mertens[r - 1],
                   "d": d, "V": v, "V0": v0,
                   "J": str(Fraction(raw_numerator, q)),
                   "T": str(Fraction(corrected_numerator, q)),
                   "cap": str(Fraction(cap_numerator, q))}
            if raw_numerator > 0 and first_raw[region] is None:
                first_raw[region] = row
            if corrected_numerator > 0 and first_corrected[region] is None:
                first_corrected[region] = row
            rows.append(row)
            counts["owners"] += 1
            u += Fraction(d, q)
            energy += d * d
            overlap += Fraction(2 * v, q)
            corrected_total += Fraction(corrected_numerator, q)
            capped_total += Fraction(cap_numerator - 2 * v, q)

        diag_diff = v0 + overlap
        bill = g * g + 2 * g * u - 2 * energy - diag_diff
        assert bill == g * g - v0 + corrected_total
        assert bill <= g * g - v0 + capped_total
        if any_positive:
            roots_with_positive[region] += 1
        for cutoff in (2, 3, 5, 11, 17, 31, a, a + 1, isqrt(r - 1) + 1):
            tail = [row for row in rows if row["q"] >= cutoff]
            s = sum((Fraction(1, row["q"] ** 2) for row in tail), Fraction(0))
            raw = sum((Fraction(row["J"]) for row in tail), Fraction(0))
            reserve = sum((2 * (Fraction(row["d"]) - Fraction(g, 2 * row["q"])) ** 2
                           for row in tail), Fraction(0))
            assert raw == Fraction(g * g, 2) * s - reserve
            if cutoff >= a:
                assert raw <= 0
        if r in (56, 57, 121, 122, 125, 317):
            direct, direct_diag_diff = direct_mixed(r, owners, mu)
            assert direct - 2 * energy == bill
            assert direct_diag_diff == diag_diff
        if r in (56, 57, 121, 122, 125, 317, 1027, 2002, 2048):
            samples[str(r)] = {"G": g, "U": str(u), "E": energy,
                               "D_minus_P": str(diag_diff), "bill": str(bill),
                               "daughters": [[row["q"], row["d"]] for row in rows]}
        if r in (121, 122, 169, 170, 289, 290):
            near_boundary.append({"R": r, "owners": owners})
        root_rows.append([r, g, energy, str(u), str(bill)])

    assert sum(trial_mu(n) for n in range(1, 15625)) == -19
    assert sum(trial_mu(n) for n in range(1, 125)) == -1
    assert sum(trial_mu(n) for n in range(1, 130)) == -1
    assert [n for n in range(125, 130) if trial_mu(n)] == [127, 129]
    digest = hashlib.sha256(json.dumps(root_rows, separators=(",", ":")).encode()).hexdigest()
    print(json.dumps({"scalar_checks": scalar_checks,
                      "root_domain": [56, 2048], "counts": counts,
                      "positive_roots": roots_with_positive,
                      "first_raw": first_raw, "first_corrected": first_corrected,
                      "boundary_checks": near_boundary, "samples": samples,
                      "root_rows_sha256": digest}, indent=2))


if __name__ == "__main__":
    main()
```

## Publication Verification - 2026-11-03 02:39 EST (-0500)

The completed synthesis was published in commit f66a1a7ebc5e779afac72b2824779e077736263b at 2026-11-03T07:38:55Z. A pinned-commit readback returned blob c0473e3157c551a666aa3ab2f50409cc41bf142a and exactly matched all 47,620 submitted characters. Commit inspection confirmed that only research/agent_reports/2026-11-03/30-finite-wheel.md changed.

The prior checkpoint bytes were preserved. All A-M sections, the exact R=125 and R=2002 fixtures, W1-W10, source inventory, scope qualifications, specialist requests and resume capsule were present. All 20 source-inventory blob SHAs matched the pinned main tree. ASCII/control-character and code-fence checks passed. The embedded executable source exactly matched the tested script and its recorded SHA256. This receipt records verified publication only; it does not confer independent acceptance, formal verification, or a new endpoint gain.



## Scheduled Continuation Checkpoint - 2026-11-03 10:12 EST Invocation

**Mathematical question:** does jointly grouping the four odd-prime lifts of distinct prime-free odd cores give a useful restriction on the complete signed finite-C packet, once parity and every strict root admission are restored? This resumes `20261102-wheel-2` and Coordinator `20261103-coordinator-1`, section H; it does not repeat the proved parity partition.

**Execution:** PARTIAL / IN_PROGRESS; scheduled trigger 2026-11-03 10:12:01 EST (-0500); RUN_ID_UNAVAILABLE. The earlier completed CORR4 claim `20261103-wheel-1` and all preceding sections are preserved. This is the due FINITE-AC turn; MU-LIFT follows next.

**Authority:** main `3930d884282dd5315f0453e5dd88b356d187a8e0`; AGENTS blob `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; proof contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`. Canonical actual-prime VF von Koch remains open. Newer merged strict-Mertens evidence is inherited upstream progress, not a discovery of this run; its source/CI provenance is being refreshed.

**Continuity:** retrieved both November 2 and November 3 reports at reporting snapshot `e4589479667a8622aad1e3a703b4eac2190d7002`; TODAY=AVAILABLE for every named role, with relevant yesterday derivations carried forward. Consumed the accepted/merged parity obstruction, today's CORR4 integer-cap result, latest pair-positivity falsifier at R=376, Coordinator's explicit second-prime continuation, and the external inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` (no entry after October 18). Cross-carrier results are not treated as finite-C estimates.

**Original source:** `eulerSelfDualBilinear`, blob `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26`; endpoint theorem blob `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`; parity-sector module blob `168e58512054ecd3fd6518331b086b9cca7cf9ed`. Inspection shows #1071 formalizes the four original parity sectors and R=5 obstruction; the odd-core packet-weight formula remains the accepted paper representation, not a new compiled declaration.

**Preregistered tests:** derive the full joint {2,ell} lift kernel before estimating. Check nonnegativity and any proposed sector-to-complete homogeneous comparison on exact small roots, with ell=3,5,7 and strict admission transitions. Reject homogeneous payment upon an actual Q_R=0 with nonzero retained sector. Retain both index orientations, diagonal, all mixed terms, historical K_R and any omitted-lift corner. No new all-scale bound, finite-C theorem, or endpoint gain is claimed at this checkpoint.

**deployment_ack:** current persistent engine consumed; NEXT-WHEEL follows the protected FINITE-AC rotation and the exact latest committed continuation rather than restarting CORR4. No Lean execution, source edit, branch/PR action, merge, schedule change, or agent launch is authorized or performed.


## Scheduled Continuation Final Synthesis - Claim 20261103-wheel-2

**Most important result:** the second-prime extension of the nonnegative parity packet is NOT nonnegative on the actual root-truncated source. For the joint {2,3} packet, every negative kernel value is exactly -1, and it occurs only when BOTH cores admit 1,2,3 but exclude 6, in precisely five product ranges. These are genuine moving-admission effects, not inadmissible completed-wheel examples. Common-factor dilation preserves the exact floors and admissions; actual nonzero Mobius coefficients realize both signs of the resulting contribution at arbitrarily large roots. More strongly, two explicit, disjoint proper subfamilies have coherent signed mass of opposite signs and linear order at every sufficiently large root.

**Evidence:** PAPER_PROOF / SELF_AUDIT for F1-F4 and the all-scale localization; EXACT_FINITE_COUNTEREXAMPLE for F5, with a complete direct arithmetic proof. Independent Referee review: PENDING. New Lean declarations: NONE. No claim of external-literature novelty. New finite-C bound or endpoint gain: NOT ESTABLISHED / UNKNOWN.

**Invocation:** continuation of the scheduled 2026-11-03 10:12:01 EST (-0500) run, RUN_ID_UNAVAILABLE, not another execution. The earlier CORR4 claim and checkpoint remain unchanged. Programme-level VERIFIED_ETA is inherited from the separately accepted strict Mertens theorem now on main; it is not credited to this report. Canonical VF, RH, finite A/C, and sharp local shell control remain open.

### A. Most Important Structural Discovery

The previous parity packet has a nonnegative weight. The tempting next step was to group a second prime and keep that positivity. The exact obstruction is the missing combined lift: cores u,v with 3u<R<=6u and 3v<R<=6v have the partial divisor set {1,2,3}, not the completed set {1,2,3,6}. Their kernel can equal -1 even when every original occurrence in the packet is genuinely admitted and squarefree.

The uniform restriction proved below is stronger than a list of examples: negative weights are confined to N=floor((R^2-1)/(uv)) in {10,15,16,22,34}, and nowhere else. The exact examples (R,u,v)=(23,5,7) and (106,19,35) give signed packet contributions -1 and +1 respectively. Their common-factor families retain these signs. This rules out positivity-preserving iteration of the parity argument and sign cancellation along these common-factor families. It does NOT rule out cancellation among different families or a joint finite-C estimate.

### B. Current Authoritative Objective And Continuity

Main at intake and the 10:27 EST recheck: `3930d884282dd5315f0453e5dd88b356d187a8e0`. The canonical declaration remains `VFCanonicalSquareVonKochStatement`:

```text
exists C>=0, forall integer R>=2,
  |pi(R^2)-VF_can(R^2)| <= C R log R.
```

The original fixed sqrt(2) phase and classical von Koch interface are unchanged. This run attacks the distinct original FINITE-AC carrier, not prime-indicator VF, ideal-character moments, or the CORR4 daughter source.

Authority consumed: AGENTS `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; breadth `b5c063c51556ba57c4b25bcc380a606fa8daa207`; complete-return `16838f7f3c8724b970f8b8ece0bceaab9418066d`; engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`; role prompts `7366bb71e8a97fd11689a64311c7f590edeb1adf`; dynamic protocol `fe21d2824491fb001726311f736b9825a8f97eca`. Relevant retained finite-C safeguards were checked in the prior AGENTS and all-vector directive.

Reports were retrieved at `agent-reports@e4589479667a8622aad1e3a703b4eac2190d7002`; relevant claims, derivations, verdicts and resume sections were read. All named same-day stages are available. Yesterday is carry-forward evidence, not a claim of an additional execution.

| Role | November 2 blob | November 3 intake blob |
| --- | --- | --- |
| Coordinator 00/90 | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | f9c04a1099048cd0b02fd5264b753e916cbcd521 |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | 0688ba1d205ac2e846c3c3a55adfc267a6eb6a40 |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 79f5f11020d7038028f4ddfe92ff3f95d4bd0798 |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | ae0ce9040b145c8b2ee04418e02a363d10b5da38 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 09ecf82c4a8d5d36b10ed6d64167d695e096ce03 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | 226a5a6d971f347b45e016a046007bc4ceb368ee |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | 579d19654925823b5fa2ef849366da2925d2c1b0 |

Continuations consumed: `20261102-wheel-2`, accepted by `20261102-referee-2` and partly formalized in #1071; `20261102-wheel-3`, the sharp s^k coefficient radius, not a norm recurrence; today's `20261103-wheel-1`, still pending full independent review; and Coordinator `20261103-coordinator-1` section H, specifically the second-prime finite-C question. The preceding Wheel sequence was FINITE-AC, MU-LIFT, CORR4; this invocation supplies FINITE-AC and MU-LIFT is next.

Cross-route safeguards consumed, not transferred as estimates: Owner's common-cutoff SAT obstruction and once-only VF ancestry capacity; Analytic's NYMAN tail/middle split and today's genuine R=376 simultaneous positive daughters; Census's R=18988 historical-envelope burst falsifier and today's scalar/maximal-fragment separation; Referee's scoped maximal-field and formal endpoint verdicts. The R=376 pair result is a new paper/finite input for the next CORR4 turn, not a finite-C theorem. The external inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry after October 18. EXT-20261018-PNT-1/3 and EXT-20261017-XCOORD-1 remain source/endpoint safeguards; their old routing does not override today's protected rotation.

Material original source inspected on main:

| File | Blob SHA | Exact role |
| --- | --- | --- |
| research/EULER_HYBRID_ABEL_GRAM_20261027.lean | 2a94dd8fd56fc03e95f732fb44b778a8d4f83e26 | Literal Q_R and floor |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 | Exact coefficient/Fubini bridge |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 | Q_R=2M(R-1)-M(R^2-1), conditional finite-C consumer |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 | Strict historical envelope |
| RHLean/Proof/SquareRootMertensEndpointAmplification.lean | 7793d7bfd842348facf62a7ad856bc802ffcd15c | Finite-A endpoint interface |
| research/EULER_ASYMMETRIC_CORNER_SIGNED_GRAM_20261028.lean | e501613434bccdc6183763a8aec8f8e62a5ff26d | Existing omitted-strip/corner bookkeeping |
| research/FINITE_C_BINARY_PARITY_OBSTRUCTION_20261102.lean | 168e58512054ecd3fd6518331b086b9cca7cf9ed | Four parity sectors and R=5 no-go |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical statement, inspected excerpt |

**Formal-scope correction:** #1071 proves the original four-sector parity partition and R=5 witness. The stronger odd-core weight formula from `20261102-wheel-2` is accepted PAPER_PROOF, not a declaration in that file. This distinction corrects overly broad readings of "merged complete packet" without changing the accepted mathematics.

**Updated inherited formal frontier:** #1073 was human-merged at 13:14:29Z. Its exact tested head is `9cbfce5295343bcb411e6d2cb159b59995cd985b`; all 13 attached workflows succeed. This run inspected main's `VF919NativeStrictMertens.lean`, blob `b33a4883e1ddb0551b0f11f062bce46680d87450`, the unconditional `native_mertens_uniform_strict_gap` and fixed-power types, and actual run `41554561404` / job `125650160501` logs showing the permitted terminal axioms and successful audit. Comparing that tested head to current main shows only added proof modules and a workflow edit, no modified existing Lean dependency. Independent acceptance is carried forward from `20261102-referee-3` and today's Referee/Lean reports, not re-created by this SELF_AUDIT. Thus the accepted strict-Mertens result is now ON_MAIN; historical prose still calling every below-7/8 bound open is superseded at that scope.

#1075/#1076 were integrated through #1077 at 13:52:39Z. The #1076 head changed after the previously reviewed head, so this report does not silently extend that exact-head review to every later renamed declaration. #1078 merged at 14:37:17Z: its new moving-prime-window note, blob `c6b88c91b5d7b5a14e1c1c3d5a48ca1a60e7c839`, explicitly has IDENTITY_ONLY + FINITE_REGRESSION scope and an open uniform estimate. Current draft #1079 at `bdaf5c642b51c732a3e755b2e799c8c5ec628508` is unmerged and unused here.

For #1071, all 12 workflows succeed at `3706efbef1e20b2c54709f8e80ea55d3c1d1cea9`; run `41500748946`, job `125467273524`, was read and confirms warning-fatal compilation, exact types and standard axioms. No new main-head build, local Lean execution, or independent review of today's new claim is asserted.

### C. Structural Mechanism Investigated

Three moves were considered. A second-prime nonnegative-kernel extension is directly falsifiable; completing all lifts first is not source-faithful without the omitted-lift correction; and a joint signed estimate must retain the interaction between distinct prime-free cores. The first move was developed through exact source reconstruction, complete classification of its failure, and arithmetic dilation families. The R=9 full-source test then challenges homogeneous sector payment after BOTH small primes have been grouped.

No modulus was enlarged to improve a density count. The only small residue table below is an exact finite certificate for a quotient-period theorem, not a sieve approximation to primes or a claim of signed independence.

### D. Exact Theorem Statements

Throughout R>=2 is an integer, X=R^2-1, mu is the genuine Mobius function, M(t)=sum_(1<=n<=t)mu(n), and all core indices are positive. The actual historical quantity is

```text
K_R = max_(0<=y<R) (M(y)-1)^2/(y+1) >= 1.
Q_R = sum_(1<=a,b<R) mu(a)mu(b) floor(X/(ab)).
```

The compiled consumer quantifies over every K>=0 satisfying `(M(y)-1)^2<=K(y+1)` for all y<R. Using the least K_R does not change that quantifier by monotonicity. K_R is NOT an activation term or a running maximum through R^2.

**F1. Full two-prime packet, with partial admission.** For any odd prime ell, put P=2ell, D={1,2,ell,2ell}, and define

```text
D_R(u) = {d in D : d*u<R},
W_(R,ell)(u,v) = sum_(d in D_R(u), e in D_R(v))
                   mu(d)mu(e) floor(X/(d*e*u*v)).

Q_R = sum_(u,v<R, gcd(u,P)=gcd(v,P)=1)
        mu(u)mu(v) W_(R,ell)(u,v).                         (F1)
```

Equivalently, using the PREVIOUS accepted parity weight w_R,

```text
W_(R,ell)(u,v) = w_R(u,v)
 - 1_(ell*u<R) w_R(ell*u,v)
 - 1_(ell*v<R) w_R(u,ell*v)
 + 1_(ell*u<R,ell*v<R) w_R(ell*u,ell*v).                  (F1a)
```

Each w on the right uses its OWN actual parity-lift cutoff; the factor 2ell is never assumed admitted just because ell is admitted.

**F2. Complete negative-weight localization for ell=3.** For all u,v<R coprime to 6, let N=floor(X/(uv)). Then

```text
W_(R,3)(u,v) >= -1;
W_(R,3)(u,v) = -1
  iff 3u<R<=6u AND 3v<R<=6v
      AND N in {10,15,16,22,34}.                          (F2)
```

All other weights are nonnegative. No squarefree hypothesis is needed for this kernel statement; zero-Mobius cores are simply zero coefficients in F1. The theorem covers all roots, including strict-admission equalities.

**F3. Exact square-endpoint dilation.** For every integer s>=1,

```text
W_(sR,ell)(s*u,s*v) = W_(R,ell)(u,v).                    (F3)
```

For a nonzero source pair, if s is squarefree and gcd(s,2ell*u*v)=1, the two core coefficients also satisfy

```text
mu(su)mu(sv)=mu(u)mu(v).
```

Thus both the weight and the signed packet contribution are preserved. This maps a chosen original occurrence packet injectively into the larger source; it does NOT identify or exhaust the entire source at sR.

**F4. Proper coherent subfamilies of both signs.** For fixed m define

```text
delta_m = product_(p|m)(1-1/p) * product_(p not dividing m)(1-1/p^2) > 0.
```

At every integer R, the following are genuine distinct-core pairs in F1 with ell=3:

```text
Negative family:
  (u,v)=(5s,7s), mu(s)^2=1, gcd(s,210)=1,
  2R/47 <= s <= R/23.
  mu(u)mu(v) W_(R,3)(u,v) = -1.

Positive family:
  (u,v)=(19s,35s), mu(s)^2=1, gcd(s,3990)=1,
  R/106 <= s < R/105.
  mu(u)mu(v) W_(R,3)(u,v) = +1.                          (F4)
```

With ONE orientation u<v, their aggregate contributions are respectively

```text
 -delta_210 * R/1081 + O(sqrt(R)),
 +delta_3990 * R/11130 + O(sqrt(R)).                      (F4a)
```

The constants are absolute for these two FIXED moduli. In Q_R both orientations occur, so each displayed contribution is doubled. The families are disjoint and no occurrence is spent twice. This is not a statement about the sign or size of their full complement.

**F5. The fully grouped cross-core sector still cannot be paid homogeneously by Q_R.** Define

```text
Dcore_R = sum_(u<R, gcd(u,6)=1) mu(u)^2 W_(R,3)(u,u),
Ocore_R = 2 sum_(u<v<R, gcd(u,6)=gcd(v,6)=1)
                 mu(u)mu(v) W_(R,3)(u,v).
Q_R = Dcore_R + Ocore_R.
```

At R=9, `(Q_R,Dcore_R,Ocore_R)=(0,14,-14)`. Hence no finite constant C can satisfy `|Ocore_R|<=C|Q_R|` for every R>=2, or the analogous Dcore or squared comparison. This is a falsifier of the stated ALL-root homogeneous shortcut only; it does not disprove an eventual comparison, an additive-budget inequality, or finite C itself.

### E. Proof And Derivation

**F1: exact occurrence map.** Every original index a with mu(a)!=0 uniquely has a=d*u, where d|2ell and gcd(u,2ell)=1. Unique prime factorization gives mu(a)=mu(d)mu(u). Conversely, every admitted d*u with a nonzero core coefficient is exactly one original nonzero occurrence. Apply this independently to a and b, retaining both orientations. Squareful original indices have coefficient zero and require no fabricated replacement. Formula F1a is the same grouping performed first at 2 and then at ell. No floor, endpoint, diagonal or high-product corner is changed.

**F2: a finite-to-infinite proof, not extrapolation.** The only possible admitted divisor sets for ell=3 are the successive prefixes

```text
D1={1}, D2={1,2}, D3={1,2,3}, D4={1,2,3,6}.
```

For their corresponding lengths i,j let

```text
F_ij(N)=sum_(d in Di,e in Dj)mu(d)mu(e) floor(N/(de)).
c_i=sum_(d in Di)mu(d)/d = 1,1/2,1/6,1/3.
```

Floor nesting gives W=F_ij(N). Every de divides 36, so EXACTLY

```text
F_ij(N+36)=F_ij(N)+36*c_i*c_j.                           (F6)
```

The following exhaustive remainder certificate follows by substituting r=0,...,35 into the displayed formula. Symmetry supplies j<i. The last column lists EVERY negative remainder, not selected examples; all negatives equal -1.

| i,j | Increment in F6 | Minimum for 0<=r<36 | Negative r |
| --- | ---: | ---: | --- |
| 1,1 | 36 | 0 | none |
| 1,2 | 18 | 0 | none |
| 1,3 | 6 | 0 | none |
| 1,4 | 12 | 0 | none |
| 2,2 | 9 | 0 | none |
| 2,3 | 3 | 0 | none |
| 2,4 | 6 | 0 | none |
| 3,3 | 1 | -1 | 3,4,6,10,15,16,22,34 |
| 3,4 | 2 | -1 | 3,4 |
| 4,4 | 4 | -1 | 3,4 |

For example, the only potentially negative admitted case uses

```text
F_33(N)=N-2 floor(N/2)-2 floor(N/3)
          +floor(N/4)+2 floor(N/6)+floor(N/9).
```

All F6 increments are positive integers; therefore no new negative value can occur once N>=36. Genuine admission also gives N>=d_i*d_j: the largest admitted lifts obey `(d_i*u)(d_j*v)<R^2`, hence their integral product is <=X. This excludes the negative r=3,4 in cases (3,4),(4,4). In case (3,3), N>=9 excludes 3,4,6. Its mask is exactly 3u<R<=6u,3v<R<=6v, which also implies N<=35. Precisely the five claimed possibilities remain. This proves F2 at every scale from an exact recurrence and a finite elementary table. The table is reproduced by the appended code; the proof is not a numerical fit or a Lean certificate.

**F3: exact integer floor scaling.** For any positive integer m write R^2-1=k*m+r, 0<=r<m. Then

```text
(sR)^2-1 = k*s^2*m + [s^2*(r+1)-1],
0 <= s^2*(r+1)-1 < s^2*m.
```

Thus `floor(((sR)^2-1)/(s^2*m))=floor((R^2-1)/m)`. Use m=d*e*u*v in every admitted summand; strict inequalities dsu<sR are equivalent to du<R. The signed assertion follows from multiplicativity and mu(s)^2=1. This familiar Mobius product identity is NOT claimed as new; its exact preservation of this truncated floor packet is the source-specific consequence.

**F4: actual signs and counts.** At (23,5,7), both divisor masks are D3 and N=15. The four already-parity-completed weights in F1a are `4,3,3,1`, so W=4-3-3+1=-1. Both core signs are -1. At (106,19,35), both masks are again D3, N=16, and the same four weights occur; now mu(19)=-1 and mu(35)=+1, so the actual contribution is +1. All nine admitted original index pairs in either D3-by-D3 packet have their literal coefficients and floors retained.

For the negative family, 23s<=R<=47s/2 implies the D3 masks and
`15<=floor((R^2-1)/(35s^2))<16` (equivalently this floor equals 15). For the positive family, 105s<R<=106s implies the masks and floor((R^2-1)/(665s^2))=16. The coprimality conditions make all required Mobius values nonzero and preserve the displayed products. Distinct s give distinct core pairs and, by F1 uniqueness, disjoint original ordered-pair packets.

For completeness, the counting ingredient is the elementary fixed-modulus theorem

```text
Z_m(T)=sum_(1<=s<=T,gcd(s,m)=1)mu(s)^2
      =delta_m*T+O_m(sqrt(T)).
```

Indeed use mu(s)^2=sum_(d^2|s)mu(d) and count integers coprime to m by finite inclusion-exclusion. There are at most sqrt(T) small-square terms, each with O_m(1) error. Extending the absolutely convergent sum of mu(d)/d^2 costs O(sqrt(T)). Its Euler product is the displayed positive delta_m. No PNT, prime-in-short-interval theorem, or sign-distribution assumption is used. Subtract endpoint counts. The interval lengths are R*(1/23-2/47)=R/1081 and R*(1/105-1/106)=R/11130; endpoint rounding costs O(1). This proves F4a. The density lemma is existing elementary infrastructure, also recorded in the repository's October 11 multiplicative-Gram note, blob `25f96804928af68d3ca3506e8ea4c8f7685cedb7`; the new application is to these exact finite-C boundary packets.

In particular scaling the two base witnesses by any prime outside the finite excluded set gives unbounded-root examples without invoking even this density estimate.

**F5: entire source, not a selected model.** At R=9 the only cores coprime to 6 are 1,5,7. Their coefficient vector is (1,-1,-1), and the complete kernel matrix is

```text
      1  5  7
1    10  5  4
5     5  3  2
7     4  2  1
```

Its core diagonal gives 10+3+1=14; the off-diagonal is 2*(-5-4+2)=-14. Independently, M(8)=-2 and M(80)=-4, so Q_9=2*(-2)-(-4)=0. This is the complete actual root source, with every parity and 3-lift restored.

**Important diagonal distinction:** Dcore is NOT the original physical diagonal nor the historical Abel diagonal. In this example the physical diagonal sum mu(a)^2 floor(80/a^2) is 114. Same-core, distinct-lift interactions contribute -100, giving Dcore=14; the remaining distinct-core interactions contribute -14. Nothing is omitted or independently re-spent. At R=4, W(1,1)=-1 further shows that the grouped kernel need not be a positive-semidefinite Gram matrix; F3 propagates that negative diagonal to R=4s. This is an operator-structure obstruction, not an arbitrary-vector substitution for the actual Mobius source.

### F. Structural Consequence

The result confines every negative joint weight to the double partial-lift region R/6<=u,v<R/3 and five exact product bands. Completed lifts cannot be substituted there. Its sign after multiplication by mu(u)mu(v) is not predetermined: shared-factor dilation removes any hope of sign cancellation along the two explicit families. This extends the previous parity investigation rather than repeating its R=5 calculation.

For the ell=3 negative-support indicator B_R(u,v) from F2, define Wplus=max(W,0). There is the exact, full-source decomposition

```text
Q_R = A_R - Bsum_R,
A_R = sum_(u,v<R,coprime to 6) mu(u)mu(v) Wplus_R(u,v),
Bsum_R = sum_(u,v<R,coprime to 6) mu(u)mu(v) B_R(u,v).
```

Here A_R is still signed despite its nonnegative kernel. The identities
`Q_R^2=A_R^2+Bsum_R^2-2*A_R*Bsum_R` and
`Q_R^2=Dcore_R^2+Ocore_R^2+2*Dcore_R*Ocore_R`
retain every interaction. No separate smallness or favorable sign is asserted for any piece.

### G. Signed And Quantitative Relevance

F4a is an independent quantitative statement ONLY about two precisely specified proper subfamilies. Its O(R) amplitude is compatible with the finite-C budget R*sqrt(K_R), since K_R>=1. It cannot disprove that target, prove it, or establish a large full-source discrepancy. In particular, the negative family is not a reusable credit against every positive family.

The original binding inequality remains

```text
exists C>=0, forall R>=2,
 |sum_(u,v<R,coprime to 6) mu(u)mu(v)W_(R,3)(u,v)|
   <= C*R*sqrt(K_R).
```

F1 identifies this exactly with the compiled finite-C obligation; it is TARGET_EQUIVALENT, not an independently known supplier. There is no newly proved global improvement from F1-F5. The inherited strict Mertens theorem gives an absolute prefix-growth rate; it does not supply this inequality relative to the actual lower-scale K_R or local shell energy.

### H. Falsification, Novelty And Verification

Exploration used small actual packets and simple divisor-mask tests. Toy negatives at N=3,4 were explicitly rejected when their advertised completed masks would force N>=18 or 36; they are NOT counted as source counterexamples. The actual R=23 and R=106 packets were independently reconstructed by trial factorization of every original lifted index, separate from the sieve used for bulk source checks.

Frozen final validation: every R=2..256 for ell=3, R=2..80 for ell=5,7, and anchors R=317,1027 for ell=3. This is 415 root/prime cases. In every case the direct original double sum, endpoint formula, nested parity formula and joint-prime reconstruction agree. The classification F2 holds for every tested core pair, including zero-coefficient cores. Additional checks cover all ten 36-remainder tables, 8,715 exact dilation cases, 54 signed dilations, and 34 fixed-root coherent-interval cases. These are fixed-range validation checks after exploratory discovery, not a blinded experiment; the previously explored witnesses are not retroactively labeled held out. No statistical independence is claimed.

| R | Q_R | Dcore_R | Ocore_R | K_R |
| ---: | ---: | ---: | ---: | ---: |
| 4 | -1 | -1 | 0 | 1 |
| 5 | 0 | 0 | 0 | 1 |
| 9 | 0 | 14 | -14 | 3/2 |
| 14 | 0 | 28 | -28 | 3/2 |
| 23 | -1 | 63 | -64 | 3/2 |
| 106 | -9 | 1385 | -1394 | 3/2 |
| 317 | 22 | 12246 | -12224 | 3/2 |
| 1027 | -375 | 128355 | -128730 | 3/2 |

The Python runtime actually reported 3.12.14. Final reproducer SHA256: `c8658944a9b6c20a946061cf6d15959288a5771dd64c2031d09fa9b910b7176b`. Ordered root-row JSON SHA256: `287853397a65362df6a5e988c0bc1058499f05e0104c1308686407286bff52c2`. The appended source is self-contained and uses exact integer/rational arithmetic. These checks are not independent Referee acceptance and not Lean-certified numerics.

Novelty review inspected the live parity module, literal finite-C source/consumer, asymmetric-corner module, prior Wheel proof and Referee verdict, and the existing multiplicative-Gram note. Repository searches for `eulerSelfDualParitySector`, second-prime/packet candidates, `eulerSelfDual` with `dilation`, and the five-integer negative list found no equivalent stated localization or these packet witnesses. This was a scoped repository search, not a proof of literature novelty. Basic Mobius multiplicativity, squarefree density, finite Fubini and the quotient-period method are established inputs, not new discoveries claimed here.

No RH-scale supplier, finite-C bound, prime-distribution premise, independent-sign model, or unproved global cancellation is used in F1-F5. The only infinitary counting step has the elementary proof above with FIXED moduli. No growing-modulus uniformity is inferred.

### I. Conceptual Interpretation

Positivity of the parity packet is not stable under another prime. The issue is not a shortage of local residue information: the arithmetic cutoff admits both single-prime lifts but can exclude their product. That exact missing face changes the sign. Shared factors then preserve the signed effect under dilation rather than randomizing it. A useful next mechanism must control the full interaction between such boundary families and their admitted complements.

### J. Competing Hypotheses

| Mechanism | Disposition |
| --- | --- |
| Iterated prime grouping preserves nonnegative packet weights | REFUTED on actual source, at unbounded roots |
| The negative-kernel region always gives favorable signed contributions | REFUTED by (106,19,35) and F4's positive family |
| Common-factor dilation creates cancellation within these families | REFUTED; products and floors are preserved |
| Full cross-core sector is homogeneously bounded by complete Q_R for all R | REFUTED at R=9; eventual/additive variants not refuted |
| Joint signed finite-C bound after restoring every family | OPEN; no circular supplier introduced |

### K. Specialist Handoffs

**Coordinator:** register F2-F4 as a source-specific uniform restriction and scoped no-go, not a finite-C payment. Retain inherited VERIFIED_ETA_ON_MAIN separately. The second-prime ticket is resolved at its positivity/homogeneous-payment scope; the next protected Wheel turn is MU-LIFT.

**Owner Payment:** the dilation map is on two literal Mobius indices and their strict root cutoffs. It is not a prime-indicator or returned-cell map. Do not transfer either sign to the original VF weights without a new occurrence-preserving bridge.

**Analytic Type II:** the new difficulty is the coupled moving-product boundary, not cancellation in the common-factor variable of these fixed shapes. F4 supplies exact coherent subfamilies of both signs, but only O(R) partial mass. Any proposed two-variable cancellation must preserve their complement and the historical envelope; no new analytic task is launched.

**Prime Census:** a small independent audit should check the ten remainder rows, the N=15/16 physical packets, R=9's complete matrix, and strict equality at R=3u or 6u. Do not enlarge the previous R<=20000 scan; the all-scale claim rests on F6 and exact masks, not a large census.

**Adversarial Referee:** independently check F2's table-plus-admission argument; F3's `s^2*(r+1)-1` remainder; both F4 interval endpoints and fixed-modulus constants; and the distinction between core and physical diagonals. Separate verdicts on localization, coherent-family asymptotics, and absence of a global consequence. This is a published request, not completed independent review.

**Lean Verification:** only after independent acceptance and utility selection, F2's source-qualified finite classification or F3 plus the two physical witnesses are implementation-sized candidates. Reuse #1071 rather than duplicate its parity proof. Do not formalize an assumed finite-C supplier or open a proof task merely to increase theorem count. This report itself changes no Lean file or PR.

### L. First Independently Missing Theorem

The first unsupported inference in the attempted mechanism was that F1's second-prime packet remains nonnegative; F2-F4 disprove it. After removing that inference, the first quantitative gap is still a uniform estimate for the COMPLETE signed kernel at R*sqrt(K_R), with all mixed terms restored. This is the canonical finite-C input itself. No independently easier sufficient lemma was proved or identified by this run; renaming A_R-Bsum_R would not pay it.

A future proper-class estimate would need to state its exact class, prove its relation to original pairs, and show how the complementary mixed interaction is paid. The linear F4 families alone neither force nor exclude such a theorem. Do not restart the known parity telescope or infer a theorem from the finite anchor ratios.

### M. Next-Run Resume Capsule

```text
RUN: scheduled 2026-11-03 10:12:01 EST; RUN_ID_UNAVAILABLE.
CLAIM: 20261103-wheel-2, F1-F6.
MAIN: 3930d884282dd5315f0453e5dd88b356d187a8e0.
ENGINE: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
TASK: due FINITE-AC / Coordinator 20261103-coordinator-1 section H.
ORIGINAL_SOURCE: eulerSelfDualBilinear; strict a,b<R; X=R^2-1.
NEW: ell=3 negative-weight iff five product bands and both D3 masks;
     exact floor/admission dilation; actual coherent strata of both signs.
FAILURES: positivity under prime iteration; automatic favorable boundary sign;
          all-root homogeneous cross-core payment at R=9.
REVIEW: SELF_AUDIT only; independent Referee PENDING; no new Lean theorem.
TESTS: 415 source cases; 8715 dilations; 54 signed scalings;
       34 interval cases; ten complete residue tables; all passed.
PROGRAMME_GATE: inherited VERIFIED_ETA_ON_MAIN from unchanged #1073 proof.
NEW_ENDPOINT_GAIN: UNKNOWN / NONE ESTABLISHED.
COMPLETE_RETURN: F1 and A-B / Dcore+Ocore squares retain all cross terms.
FINITEC_OPEN: |Q_R|<=C R sqrt(K_R), every R and every valid historical K.
ROLLING_COVERAGE: MU-LIFT (Nov2 run3), CORR4 (Nov3 run1), FINITE-AC (this run).
NEXT_DISTINCT_ROUTE: MU-LIFT.
MU_LIFT_RESUME: 20261102-wheel-3 sharp first omitted support s^k and
  fresh-prime factorial coherence; next gap is the full signed summatory
  recurrence with fixed r<k, paid subpower loss and whole-prefix coverage,
  not another coefficient reconstruction radius.
CORR4_CARRY: 20261103-wheel-1 W10; consume Analytic 20261103-analytic-2
  R=376 and degree-normalized joint-credit interface after its review.
FINITE_AC_NEXT: do not redo F1 or scan more wheel residues. A new candidate
  must retain the missing product-lift face and exact coupled complement.
OPEN: canonical actual-prime VF, RH, finite A/C, full local sharp-shell gain,
      and subcritical MU-LIFT; strict below-7/8 Mertens itself is now inherited.
```

**Execution limitations and permissions:** direct terminal GitHub clone access returned a proxy 403; the authorized GitHub connector supplied all required source and publication access, so research was not blocked. No local Lean was run. No files outside this own-role report were written remotely. No proof branch, PR, issue, policy, workflow, schedule, merge, or other agent was changed or launched.

**Early publication verified:** checkpoint commit `ea2fb2f465468d478910d5cd8538162159c960bf`, blob `c1741f7fb064281b3bcba1481a36d5e373155716`; all 51,486 characters matched on pinned readback. The final synthesis publication receipt is appended only after actual commit/readback.

### Executed Exact Reproducer For 20261103-wheel-2

The following is the executed final source, including its final newline, with the SHA256 recorded above. It performs no network request, uses no external numeric table, and writes no repository source. Run it with Python; the tests are finite validation of the paper proof, not its unbounded-scale premise.

```python
"""Exact checks for 20261103-wheel-2; no Lean or asymptotic fit.

Exploration found the R=23 and R=106 packets. Validation below is frozen:
all R=2..256 for p=3; R=2..80 for p=5,7; anchors 317,1027 for p=3.
The all-scale theorem uses the displayed quotient-period and scaling proofs,
not extrapolation from these finite tests.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import gcd
import json
import platform


def mobius_trial(n):
    out, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            out = -out
            if n % p == 0:
                return 0
        p += 1
    return -out if n > 1 else out


def arithmetic(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                prime[n] = False
                mu[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    mertens = [0] * (limit + 1)
    for n in range(1, limit + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    for n in range(1, min(limit, 2048) + 1):
        assert mu[n] == mobius_trial(n)
    return mu, mertens


def lifts(p):
    return ((1, 1), (2, -1), (p, -1), (2 * p, 1))


def weight(R, u, v, p=3):
    return sum(a * b * ((R * R - 1) // (d * e * u * v))
               for d, a in lifts(p) for e, b in lifts(p)
               if d * u < R and e * v < R)


def parity_weight(R, a, b):
    n = (R * R - 1) // (a * b)
    ea, eb = int(2 * a < R), int(2 * b < R)
    return n - (ea + eb) * (n // 2) + ea * eb * (n // 4)


def nested_weight(R, u, v, p):
    out = parity_weight(R, u, v)
    if p * u < R:
        out -= parity_weight(R, p * u, v)
    if p * v < R:
        out -= parity_weight(R, u, p * v)
    if p * u < R and p * v < R:
        out += parity_weight(R, p * u, p * v)
    return out


def residue_weight(i, j, n):
    return sum(a * b * (n // (d * e))
               for d, a in lifts(3)[:i] for e, b in lifts(3)[:j])


def residue_certificate():
    result = []
    for i in range(1, 5):
        for j in range(i, 5):
            vals = [residue_weight(i, j, n) for n in range(36)]
            jump = sum(36 * a * b // (d * e)
                       for d, a in lifts(3)[:i] for e, b in lifts(3)[:j])
            assert jump > 0 and min(vals) >= -1
            assert all(residue_weight(i, j, n + 36) == vals[n] + jump
                       for n in range(36))
            result.append([i, j, jump, min(vals),
                           [n for n, w in enumerate(vals) if w < 0]])
    return result


def verify_root(R, p, mu, mertens):
    x = R * R - 1
    live = [a for a in range(1, R) if mu[a]]
    direct = sum(mu[a] * mu[b] * (x // (a * b)) for a in live for b in live)
    assert direct == 2 * mertens[R - 1] - mertens[x]
    cores = [u for u in range(1, R) if gcd(u, 2 * p) == 1]
    total = diagonal = neg_kernel_signed = neg_count = 0
    for u in cores:
        for v in cores:
            w = weight(R, u, v, p)
            assert w == nested_weight(R, u, v, p)
            c = mu[u] * mu[v]
            total += c * w
            diagonal += c * w if u == v else 0
            if p == 3:
                n = x // (u * v)
                bad = (3 * u < R <= 6 * u and 3 * v < R <= 6 * v
                       and n in (10, 15, 16, 22, 34))
                assert w >= -1 and (w < 0) == bad
                if bad:
                    assert w == -1
                    neg_kernel_signed += c
                    neg_count += 1
    assert total == direct
    k = max(Fraction((mertens[y] - 1) ** 2, y + 1) for y in range(R))
    return [R, p, direct, diagonal, direct - diagonal,
            neg_count, neg_kernel_signed, str(k)]


def main():
    mu, mertens = arithmetic(1027 * 1027 - 1)
    certificate = residue_certificate()
    rows = []
    for R in range(2, 257):
        rows.append(verify_root(R, 3, mu, mertens))
    for p in (5, 7):
        for R in range(2, 81):
            rows.append(verify_root(R, p, mu, mertens))
    for R in (317, 1027):
        rows.append(verify_root(R, 3, mu, mertens))

    r9 = [[weight(9, u, v) for v in (1, 5, 7)] for u in (1, 5, 7)]
    assert r9 == [[10, 5, 4], [5, 3, 2], [4, 2, 1]]
    # Trial factorization is independent of the sieve used above.
    witnesses = []
    for R, u, v, expected in ((23, 5, 7, -1), (106, 19, 35, 1)):
        physical = sum(mobius_trial(d * u) * mobius_trial(e * v)
                       * ((R * R - 1) // (d * e * u * v))
                       for d, _ in lifts(3) for e, _ in lifts(3)
                       if d * u < R and e * v < R)
        assert physical == expected and weight(R, u, v) == -1
        witnesses.append([R, u, v, physical])

    scaling_cases = 0
    for R, u, v, p, s in product(range(2, 18), range(1, 8), range(1, 8),
                                  (3, 5, 7), (1, 2, 3, 5, 11)):
        if u < R and v < R:
            assert weight(s * R, s * u, s * v, p) == weight(R, u, v, p)
            scaling_cases += 1
    signed_scalings = 0
    for s in range(1, 129):
        if mu[s] and gcd(s, 3990) == 1:
            for R, u, v, expected in ((23, 5, 7, -1), (106, 19, 35, 1)):
                actual = mobius_trial(s * u) * mobius_trial(s * v)
                actual *= weight(s * R, s * u, s * v)
                assert actual == expected
                signed_scalings += 1

    interval_cases = 0
    for R, s in product(range(2, 513), range(1, 129)):
        if mu[s] and gcd(s, 210) == 1 and 23 * s <= R and 2 * R <= 47 * s:
            assert weight(R, 5 * s, 7 * s) == -1
            assert mobius_trial(5 * s) * mobius_trial(7 * s) == 1
            interval_cases += 1
        if mu[s] and gcd(s, 3990) == 1 and 105 * s < R <= 106 * s:
            assert weight(R, 19 * s, 35 * s) == -1
            assert mobius_trial(19 * s) * mobius_trial(35 * s) == -1
            interval_cases += 1

    payload = json.dumps(rows, separators=(",", ":"))
    print(json.dumps({
        "python": platform.python_version(), "root_prime_cases": len(rows),
        "rows_sha256": sha256(payload.encode()).hexdigest(),
        "period_certificate": certificate, "R9_matrix": r9,
        "witnesses_trial_factored": witnesses,
        "scaling_cases": scaling_cases, "signed_scalings": signed_scalings,
        "coherent_interval_cases": interval_cases,
        "selected_rows": [r for r in rows if r[1] == 3
                          and r[0] in (4, 5, 9, 14, 23, 106, 317, 1027)],
    }, indent=2))


if __name__ == "__main__":
    main()
```


### Verified Publication Receipt for This Invocation

- Final research synthesis and complete executed reproducer committed at `7bb29444d3c93f9440394fb0625d6e12ac6b19de` on `agent-reports`; GitHub commit timestamp `2026-11-03T15:33:36Z` (`2026-11-03 10:33:36 EST`).
- Resulting report blob: `5376e5e0d1c85dad0e13416d38eb50b0c3a08ccf`. A fresh readback matched all 89,437 submitted characters exactly.
- The fetched commit metadata records exactly one changed file, `research/agent_reports/2026-11-03/30-finite-wheel.md`, with 575 additions and zero deletions. All preceding report content was retained.
- Main was rechecked at closeout and remained `3930d884282dd5315f0453e5dd88b356d187a8e0`. No Lean files, other reports, branches, PRs, issues, policies, or schedules were changed. The branch named above already existed; this invocation only updated the authorized report.
- This receipt records the already verified synthesis commit, not its own future commit. New claim `20261103-wheel-2` remains `PAPER_PROOF / SELF_AUDIT`, with independent review and any Lean formalization pending. No new global bound or endpoint gain is claimed.


## Scheduled Continuation Checkpoint - 2026-11-03 18:06 EST Invocation

**PARTIAL / IN_PROGRESS. RUN_ID_UNAVAILABLE.** This is the actual scheduled invocation begun at 18:06:00 EST (-0500), not an extra launched agent. Claim identifier reserved for this invocation: 20261103-wheel-3.

**Mathematical question:** resume the due MU-LIFT full signed hyperbola-norm question from 20261102-wheel-3, equations (54)-(64), as requested by 20261103-coordinator-2. The sharp first-omitted-support radius and fresh-prime factorial coefficient are existing paper results, not new work or a norm contraction. Investigate a genuine signed cancellation mechanism with its complete reconstruction and identify the first unsupported inequality.

**Live authority changed during intake.** Entry main was 69aac0441b4df011cf7df3ba115169c3b66d72f5. Human merge #1084 at 2026-11-03T23:07:58Z advanced main to 25127ac796a1d2ace7a8b3ddb27a02154cc48ef2. Latest AGENTS blob b878d396c387a57bd0b5165fecf10d15ef3732cd; contract 63f7553bf6e5f2a16e37808116c643dc0dcc50e1; source-first contract b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6; engine 495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4. Updated policy bytes were fetched and compared with the entry versions.

SOURCE_FIRST_VERSION: 2026-11-03. The new contract explicitly permits a due protected route to replace its default packet. This run retains MU-LIFT after CORR4 and FINITE-AC, while checking a bounded original OAI collision/occurrence comparison. No Mobius-to-Hecke or CORR4-to-LOW identity is assumed. The original OAI source and exact live PR checks are still IN_PROGRESS. #1083 was fetched as OPEN/DRAFT at d8cdb9fa1c90fb1383b7dc79745e466f2b0f4d56; it is not main.

**Continuity:** all seven role reports for November 2 and November 3 were retrieved at reporting snapshot 621566df959d02c34542bc6c0d73a87654416acd, with applicable mathematical sections inspected and remaining relevant source checks continuing. TODAY=AVAILABLE for each role; this is not a claim that every stage or review is complete. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry newer than October 18; its historical routing is superseded. The native shared-offset, partial-prime-packet and sharp MU-LIFT radius claims remain at their recorded scopes.

**Scope:** canonical actual-prime VF, RH and the full subcritical MU-LIFT recurrence are unresolved. Existing reported strict OAI-derived gain is inherited evidence, not this run's new result or a reusable recurrence. No new global gain, formal theorem or independent review is claimed. No local Lean, proof edit, branch/PR/issue mutation, other-report write, policy change or agent launch is authorized or performed.

This checkpoint is published before substantive research; the final derivation, falsification, exact source/CI scope and next-run capsule will be appended here.

## Scheduled Continuation Final Synthesis - Claim 20261103-wheel-3

Actual invocation: 2026-11-03 18:06:00 EST (-0500), America/New_York. Platform run ID unavailable. This continues the verified early checkpoint, preserves the preceding CORR4 and FINITE-AC work, and supplies the due MU-LIFT turn plus the newly authorized original-LOW comparison.

### A. Most Important Structural Discovery

**Original LOW:** on the actual pairwise-disjoint canonical prime-ideal slots, an unselected tuple's product norm determines its prime-ideal depth and hence its compensation parity. For fixed J, equal norm profiles give exactly equal original complex atoms. At the terminal source's nonnegative slot weights, even different profiles with the same product norm have nonnegative Hermitian pair interaction. Their multiplicity is at most `2^|J|`, uniformly in the scale. Thus same-product-norm collisions are a bounded coherent contribution, not a sign-reversing cancellation mechanism. Every interaction between different norms, subsets J, dyads, and returned branches remains present.

**MU-LIFT:** after summing all alternating Heath-Brown families, the actual top-half-prime packet is exactly `-[pi(X)-pi(floor(X/2))]`. At `X=B^k-1`, it cannot be separately bounded by `G(B) E(B)^r sqrt(X)` for any fixed `1<=r<k` and subpower G. This rejects separate payment of that retained packet, not the complete signed recurrence. Its complement is retained explicitly, with the mixed term.

Classification: `PAPER_PROOF / SELF_AUDIT`, source-specific deductions from established algebra and factorization; exact finite controls below. Independent Referee review and any new Lean formalization are **PENDING**. No new Mertens exponent, LOW power saving, canonical VF bound, or RH proof is claimed. Generic fiber reindexing, the lift identity, prime isolation, and quadratic ideal splitting are not claimed as new mathematics.

### B. Current Authoritative Objective And Continuity

Entry main was `69aac0441b4df011cf7df3ba115169c3b66d72f5`. Human merge #1084 during intake advanced it to `25127ac796a1d2ace7a8b3ddb27a02154cc48ef2`, rechecked unchanged at **2026-11-03 23:25:22 UTC / 18:25:22 EST**. The actual canonical target remains `VFCanonicalSquareVonKochStatement`: a constant C>=0 controlling `|pi(R^2)-VF_can(R^2)| <= C R log R` for every integer R>=2. RH, that actual-prime bound, the sharp local shell benchmark, and the full subcritical MU-LIFT recurrence remain open.

Authority blobs: AGENTS `b878d396c387a57bd0b5165fecf10d15ef3732cd`; proof contract `63f7553bf6e5f2a16e37808116c643dc0dcc50e1`; source-first contract `b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6`; research engine `495fa9ee2067ccf5db9dc3c48ffaaadcd6485aa4`. The source-first contract expressly permits the due protected route to replace its default packet. This run therefore resumes MU-LIFT from `20261102-wheel-3`, equations (54)-(64), and `20261103-coordinator-2`, while also completing a bounded NEXT-WHEEL source comparison. No routing override was invented.

All November 2 and November 3 named role reports were retrieved at the intake reporting snapshot `621566df959d02c34542bc6c0d73a87654416acd`. Their applicable mathematical sections, claim IDs, counterexamples, and scope corrections were consumed. All seven roles had `TODAY=AVAILABLE`; this does not mean their reviews or formalization stages were complete. The following are intake blob identities, not a claim that their branches cannot subsequently change:

| Role file | November 2 blob | November 3 intake blob |
| --- | --- | --- |
| 00-coordinator-am.md | `1e932d4ce0eb0fd2c5f4507f6b111194d633eb32` | `8f22479e602b919c00ad5539a7442371c2ee6076` |
| 10-owner-payment.md | `abfe546d72b151f4cd200fc61de3197efe23a65c` | `d52c74b76c2914c3be694f39cd7afe9b122a4834` |
| 20-analytic-type-ii.md | `8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73` | `2b9c3dbab6039e3c30a5ece3e473290af5dbbf0b` |
| 30-finite-wheel.md | `abf8ac8c22a708886183849552c90dd62787ac8d` | `15802d31f6b7abf3ffff97a5a57942baf3bc2d07` |
| 40-prime-census.md | `2cd84c57ab18d923e97368764f29f4ccd2ec3bb3` | `5b564235ba20bf4a53c13dac0cc91d210d665a84` |
| 50-adversarial-referee.md | `814af1684df66e6ac99b8df1f102cb592b316f89` | `dff2382a732be1829ad7583e046ebbc64c61e4c9` |
| 60-lean-verification.md | `02d19d792e26f072004cb5909f149538752626e9` | `a9c65a6809323216f8a876845538b6af0fae393e` |


Continuity used, rather than recomputed:

- `20261102-wheel-3`: sharp first-omitted-squarefree radius and fresh-prime factorial coherence, paper/self-audit; not a norm recurrence. Today's question is inside the valid reconstruction interval and after the full alternating sum.
- `20261103-wheel-1/2`: CORR4 one-use credit and partial-prime FINITE-AC masks. The partial packet's negative and positive examples remain native integer examples, not Hecke-source evidence. The accepted parity partition in #1071 does not formalize every stronger paper formula.
- `20261103-analytic-2` and `20261103-census-3/4`: simultaneous adverse daughters, PAIR-HALF refutation at R=57, the R=59 reserve, and common-offset correction. These are next CORR4 inputs, not credits available to this LOW source.
- `20261103-analytic-3` CD1-CD6: source-specific short-average smoothing and its logarithmic, not fixed-power, improvement; the complete triangular correlation remains unpaid.
- `20261103-owner-3`: phase-sensitive excursion restrictions do not identify a native chronological owner with an ideal-tuple label.
- `20261103-referee-5`: scoped acceptance of C27-C30 and Nyman N4/N5; NR1-NR7 are its new self-audit claims. Its correction withdraws the alleged error in Analytic's original `1/(3 sqrt(3))` integral. Do not propagate the superseded objection.
- `20261103-lean-2`: an uncompiled Nyman proof attempt, not a kernel theorem. Publication/access limitations there do not certify its elaboration.

External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` was read; its newest dated entries are October 18, including EXT-20261018-PNT1 through PNT3. They are historical source/payment constraints, not a new November assignment or proof of a new signed bound. Today's upstream review of this claim is PENDING, not inferred from a schedule.

Inherited strict OAI-derived Mertens gain from the merged #1073/#1079 line remains at its previously independently reviewed scope. `VF919ActualSlotMinRetighten.lean` on this main has the unconditional existential true-slot-minimum theorem. This run inspected its type and the original-source interfaces; it did not perform a fresh independent semantic audit of the entire endpoint. No repeated expenditure of the finite slot tilt is credited.

**Live #1083 correction:** still OPEN/DRAFT, head `d8cdb9fa1c90fb1383b7dc79745e466f2b0f4d56`. At the final status check, 13 of 14 check runs succeeded and `low-first-slot-proof` failed. [Run 41736212654, job 126265977582](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41736212654/job/126265977582) failed at 23:15:35 UTC in the new `VF919OriginalLowTupleSignedGram.lean`: smoothness-type mismatch at line 83, heartbeat timeout at line 118, unqualified `stableFarComplexToRealPair` at lines 137/141/158/162, and unresolved PUnit universes near lines 180-190. Error-generated declarations print `sorryAx`; they are not acceptable formal evidence. The earlier gain-ledger declarations in that same log print standard axioms, but the complete required gate failed and the later terminal audit is not established. This supersedes the checkpoint's honest IN_PROGRESS observation. No PR or workflow was changed or rerun.

### C. Structural Mechanism Investigated

Two carriers are deliberately separate.

For MU-LIFT, the intended recurrence must control all coefficients of the fully alternating convolution, not its support radius alone. The proposed smaller move was to pay a structurally isolated, genuinely arithmetic packet after combining its alternating families. The top-half primes decisively reject that move.

For OAI LOW, the source itself makes the unselected dependence much more rigid than an arbitrary complex graph: apart from slot weights, the complete selected inverse integral depends on the unselected tuple only through its product norm. Unique ideal factorization and disjoint slot admission then control norm multiplicity and compensation parity. This provides an exact, bounded resonance class with a sign restriction, without claiming control of the distinct-norm interaction.

### D. Exact Statements And Carriers

#### O1. Literal Unselected Source Normal Form

Use `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`, `Detector/LowSlotPolynomial.lean::compensation_tuple_low_polynomial`. Fix every parameter of that theorem, including its Hecke character eta, exclusions S, calibration, W0/W1, original cutoff, X,Y,T,t, slot scales P_i, and subset J. **In the code, J indexes unselected slots; its complement is `SelectedSlot J`.** A physical original occurrence is `(J,a,b)`, not just its integer norm. `lowSlotJoin` gives the exact bijection from the full tuple to the unselected tuple a and selected tuple b. U_a is an already-summed selected-b contribution.

Write A_J for the exact Cartesian carrier `LowUnselectedTuple slots J`. For a in A_J put

```text
nu(a) = (elementNorm(a_i))_(i in J),
L_a = elementNorm(product_(i in J) a_i) = product_(i in J) nu_i(a),
w_a = (-1)^|J| L_a^(-3/2) product_(i in J) W_i(nu_i(a)/P_i).

H_J(L) = (sqrt(lowPhysicalScale(C,X/L,Y/L)))^(-1)/(2*pi)
         * integral_v lowSeparatedIntegrand(C,W0,W1,Omega,X/L,Y/L,R_J,v),

R_J = lowSelectedInverseRow Finset.univ
        (lowSelectedWeight eta slots J W P t)
        eta S hS (lowSelectedIdeal slots J) T t.

U_a = w_a H_J(L_a),                 P_J = sum_(a in A_J) U_a.       (O1)
```

H_J is notation for that literal function, not an arbitrary replacement. All selected Hecke conjugates, selected Fourier phases, ideal divisibility marks, inverse rows, ray sums, W0/W1, cutoff, and physical normalizers remain inside it. For any original complex W_i, `nu(a)=nu(a')` implies `U_a=U_a'`. Equal product norms alone need not imply equality of the slot weights.

#### O2. Arithmetic Depth And Uniform Collision Multiplicity

Now impose the actual physical assumptions of `LowCentralTuple`: `slots i=canonicalSlotSupport(T_i)`, T_i finite sets of supported prime ideals outside S, and the T_i pairwise disjoint. For every J and every a in A_J, the product ideal I_a is squarefree. The map a -> I_a is injective for this fixed J.

For a positive integer L, let v_p(L) be its rational prime exponents. A squarefree Eisenstein ideal of norm L can exist only if

```text
v_3(L) in {0,1};
v_p(L) in {0,1,2} for p == 1 mod 3;
v_p(L) in {0,2}   for p == 2 mod 3.
```

On these allowed norms define

```text
d_E(L) = v_3(L) + sum_(p==1 mod 3) v_p(L)
                   + (1/2) sum_(p==2 mod 3) v_p(L),
s_1(L) = #{p : p==1 mod 3 and v_p(L)=1}.
```

There are exactly `2^s_1(L)` squarefree ideals of norm L in the ambient Eisenstein ring. Each has exactly d_E(L) prime-ideal factors. Consequently, for the actual source norm fiber `A_J(L)={a:L_a=L}`,

```text
A_J(L) nonempty  =>  d_E(L)=|J|,
m_J(L):=|A_J(L)| <= 2^s_1(L) <= 2^omega(L) <= 2^|J|,
(-1)^|J| = (-1)^d_E(L).                                      (O2)
```

The final `2^omega(L)<=2^|J|` is asserted for nonempty source fibers; empty fibers satisfy the direct `m_J(L)<=2^|J|` bound trivially. In particular, changing J while preserving an admitted unselected product norm cannot reverse its compensation parity by changing |J|. This is not an identification of its full complex atom across J.

#### O3. Exact Coherent Energy And Full Return

For an attained norm profile nu define

```text
m_i(nu_i) = #{x in slots_i : elementNorm(x)=nu_i},
m_nu = product_(i in J) m_i(nu_i),
u_nu = U_a for any a with nu(a)=nu.
```

The exact profile-fiber sum, diagonal, and ordered off-diagonal are respectively

```text
m_nu u_nu,       m_nu |u_nu|^2,       m_nu(m_nu-1)|u_nu|^2.     (O3a)
```

For product-norm fibers let `V_L=sum_(a in A_J(L)) U_a`, and let `D_J=sum_a |U_a|^2`. With arbitrary complex W_i,

```text
sum_L |V_L|^2 <= sum_L m_J(L) sum_(a in A_J(L)) |U_a|^2
              <= 2^|J| D_J.                                  (O3b)
```

At the **terminal** `LowNormalized` source, W_i are real nonnegative functions. Put `b_a=product_i W_i(nu_i(a)/P_i)>=0`. Then

```text
U_a = (-1)^|J| L^(-3/2) b_a H_J(L)               (a in A_J(L)),
C_same(L) = L^(-3)|H_J(L)|^2
             * [(sum_(a in A_J(L)) b_a)^2 - sum_(a in A_J(L)) b_a^2]
          >= 0,
D_J <= sum_L |V_L|^2 <= 2^|J| D_J,
|P_J|^2 = sum_L |V_L|^2
          + sum_(L != M) Re(V_L conjugate(V_M)).               (O3c)
```

Both double sums are ordered. No lower bound on the **whole** `|P_J|^2` by D_J follows, because the displayed distinct-norm term can have either sign. No assertion that an actual nonzero collision integral has been numerically exhibited is made.

#### O4. Overlap, Masks, And Ownership Accounting

For two tuples in one fixed norm-profile fiber, let H be exactly their set of equal coordinates. The number of ordered pairs with that overlap is

```text
N_nu(H) = product_(i in H) m_i
          * product_(i in J\H) m_i(m_i-1).                    (O4a)
```

H=J is the diagonal; summing over all H gives m_nu^2. In the inherited order on Fin K, pairs with first differing coordinate j have cardinality

```text
product_(i<j, i in J) m_i * m_j(m_j-1)
  * product_(i>j, i in J) m_i^2.                              (O4b)
```

Every ordered off-diagonal has exactly one such first differing coordinate. This is **an address convention, not the native chronological first owner**. Disjoint T_i imply that a shared prime ideal between tuples must appear at the same slot; no selected and unselected slots in a fixed J can share an ideal.

For a pure outer-tuple admission subset Omega_A of A_J, retain the same literal U_a and use actual fiber counts `m_nu(Omega_A)`, not the Cartesian product formula. The fiber equality and upper multiplicity bound survive restriction. For a genuinely coupled additional mask `Omega(a,b)` on selected/unselected pairs, the selected row can depend on a: (O1)'s common H_J(L) is then **not justified** without proving equality of those admitted selected rows. The original theorem itself has the stated full Cartesian outer carrier and its literal internal masks; no added joint mask is silently imposed.

For two scales z,z' and their actual moving outer carriers, using the same ambient tuple labels only on their intersection,

```text
P(z')-P(z) = sum_(A(z') intersection A(z)) [U_a(z')-U_a(z)]
             + sum_(A(z')\A(z)) U_a(z') - sum_(A(z)\A(z')) U_a(z). (O4c)
```

Interior weights change along with entries and exits. If P=P_kept+P_return, always restore `|P_kept|^2+|P_return|^2+2 Re(P_kept conjugate(P_return))`. All J and Gaussian dyad recombinations keep their actual coefficients and cross terms. None is paid by (O2).

#### M1-M3. Due MU-LIFT Packet Test

Fix integers B>=2, k>=2. Let a(n)=mu(n) for `1<=n<B`, zero otherwise; zeta(n)=1 for positive n; and * denote Dirichlet convolution. Use the existing genuine k-lift

```text
H_(B,k) = sum_(j=1..k) (-1)^(j-1) binom(k,j)
                         a^{*j} * zeta^{*(j-1)}.
```

It equals mu at every `1<=n<B^k`, by the existing defect identity, with all original convolution occurrence multiplicities. Let X=B^k-1 and

```text
P_X = {p prime : X/2 < p <= X},
A(X) = |P_X| = pi(X)-pi(floor(X/2)),
E(B) = max_(1<=n<B) |M(n)|/sqrt(n).
```

Every p in P_X exceeds B-1. For every j>=1,

```text
(a^{*j}*zeta^{*(j-1)})(p)=j-1,
sum_(j=1..k) (-1)^(j-1) binom(k,j)(j-1)=-1,
sum_(p in P_X) H_(B,k)(p)=-A(X).                              (M1)
```

For every fixed real `1<=r<k` and every positive function G(B)>=1 with `log G(B)/log B -> 0`,

```text
A(B^k-1) / [G(B) E(B)^r sqrt(B^k-1)] -> infinity.              (M2)
```

Thus no uniform constant can pay this packet alone at that scale. More generally, if `G(B)=B^(g+o(1))`, such separate payment requires `g>=(k-r)/2` by the unconditional trivial prefix bound. This is a necessary lower constraint, not a sufficient payment or a restriction on the signed recurrence itself.

Define the literal retained complement

```text
C_(B,k)(X) = sum_(1<=n<=X, n not in P_X) H_(B,k)(n).
M(X) = C_(B,k)(X)-A(X),
M(X)^2 = C_(B,k)(X)^2 + A(X)^2 - 2 A(X) C_(B,k)(X).           (M3)
```

The complement includes composites, prime powers, small primes, units, and every alternating convolution family, not an unsigned replacement. For endpoints elsewhere in `B<=X<B^k`, the same occurrence partition is available but (M2) is the specified top-end asymptotic obstruction. Whole-interval coverage and scale-chain iteration remain unproved.

### E. Proofs

**O1.** Inspect the displayed source definition: `lowUnselectedWeight` contains exactly the compensation parity, product-norm power and norm-only W_i arguments. The remaining integral in `compensation_tuple_low_polynomial` refers to a only through `elementNorm(product a_i)` in X/L, Y/L and Q. `lowSelectedInverseRow` is the same finite selected-b sum for every a. Multiplicativity of `elementNorm` yields (O1). This uses actual source equality, not arbitrary-vector replacement. The character is unrestricted within the original theorem's hypotheses.

**O2.** `canonicalSlotEquiv` identifies each generator with exactly one admitted prime ideal, preserving its norm. Pairwise slot disjointness makes all selected factors in I_a distinct. Unique factorization of ideals then recovers, from I_a, the unique prime factor belonging to each slot T_i. This proves squarefreeness and injectivity; there is no permutation factorial because one ideal cannot belong to two slots.

The ring is the full ring of integers of `CyclotomicField 3 Q`, identified by the original Eisenstein source, with integral basis 1,omega and polynomial `omega^2+omega+1`. Modulo a rational prime p this polynomial has two distinct linear factors when p=1 mod 3, is irreducible when p=2 mod 3, and has a repeated linear factor at p=3. Equivalently, there are two norm-p primes in the split case, one norm-p^2 prime in the inert case, and one norm-3 prime in the ramified case. This follows from the nontrivial cube roots of unity in the finite field for p!=3; at 3 the polynomial is `(x-1)^2`.

A squarefree ideal may choose each of these prime ideals once. At a split prime, exponent 1 permits exactly two choices and exponent 2 forces both primes. An inert prime can contribute exponent 2 only, in exactly one way. At 3 only exponent 1 is possible. Independent unique factorizations across rational primes give the exact ambient count and depth in (O2). Masks only remove ideals from this ambient population. For nonempty A_J(L), omega(L)<=|J| because each of its |J| factors lies above one rational prime. The unit ideal L=1 has depth 0 and exactly one ambient choice. No prime-distribution theorem is used in this argument.

**O3.** Each norm-profile fiber is a Cartesian product of its coordinate fibers, and (O1) makes its atoms identical. Multiplying one common value by m_nu proves (O3a). Apply finite Cauchy-Schwarz separately inside each product-norm fiber, then (O2), to get (O3b). At the terminal nonnegative W_i, two atoms with product norm L have product `L^(-3) b_a b_b |H_J(L)|^2`, a nonnegative real number. Expanding the finite square proves (O3c), including its ordered cross-norm term. Positivity of W0/W1 or of H_J is not needed for this pair argument; H_J may be complex or zero.

**O4.** Choose equal coordinates in m_i ways and unequal ordered coordinates in m_i(m_i-1) ways; multiply independent choices. For the first differing coordinate, earlier coordinates are equal, that coordinate is unequal, and later coordinates are unrestricted. These cases partition rather than duplicate ordered pairs. Restricting the outer carrier requires actual restricted counts. A coupled selected mask changes the selected sum and therefore requires a new source proof. The moving identity is the exact intersection/new/exit decomposition, with changing values retained. The full square formula is ordinary algebra, already available in the repository and not a new estimate.

**M1.** A factorization of a prime p into j a-slots and j-1 zeta-slots has precisely one nonunit coordinate. Since p>=B, placing it in any a-slot contributes zero. There are j-1 unit-weight zeta placements, including zero placements when j=1. For k>=2, the zeroth and first binomial alternating moments vanish; subtracting the missing j=0 term gives the displayed sum -1. Thus internal alternating-family cancellation is completed before the packet is assessed.

**M2.** The already available ordinary PNT yields `A(X)~X/(2 log X)`. Hence at X=B^k-1 it is asymptotic to `B^k/(2k log B)`. Since `|M(n)|<=n`, `1<=E(B)<=sqrt(B-1)`. The ratio in (M2) is therefore bounded below, for all sufficiently large B, by a positive k-dependent constant times

```text
B^((k-r)/2) / [G(B) log B],
```

which diverges for subpower G and r<k. The same calculation proves the necessary g threshold. This uses only PNT and the trivial bound, not the sought recurrence, the strict OAI gain, or RH. PNT is inspected in `RHLean/Analysis/NativePNTTransfer.lean::nativePrimeNumberTheorem`; no new PNT proof is claimed.

**M3.** The coefficient identity holds throughout the strict interval. Partition the summation range into the actual top primes and their exact complement, use (M1), and expand the square. No compensating mixed term is discarded.

### F. Structural Consequence

Equal norm profiles cannot provide a nonzero sign-reversing pair in a fixed-J original LOW source: their atoms are equal. Under the terminal weights, all same-product-norm pairs reinforce rather than cancel. Equal norms across different J also force equal compensation parity, although their inverse rows can differ. A proposed cross-J sign reversal must therefore come from the actual selected row or other changing data, not from asserting that the common norm has opposite factor parity.

Norm collisions cost at most `2^|J|` in squared grouped energy. This is a genuine all-scale arithmetic restriction on this outer tuple carrier, stronger than assuming arbitrary fiber cardinalities. It does not bound the number of distinct product norms or their mutual Gram sum, and it does not bound the selected inverse family's internal multiplicities.

The MU-LIFT obstruction shows that even a packet which respects all j-family signs can be too large for separate subcritical payment. A successful full lift proof must exploit its interaction with the arithmetic complement, or use a different invariant that does not require this packet separately small.

### G. Signed And Quantitative Relevance

Original checked source trail: selected squared inverse energy has exponent `5/6-2d+507 epsilon`; actual sqrt(Q) normalization leaves `507 epsilon/2`, not a spare fixed power. `LowSlotPolynomial` is exact. The first explicit cross-unselected sign loss **in this local trail** is `norm_sum_le` in `LowTupleGram::compensation_tuple_actual_gram`. `LowCentralTuple` combines the scalar Gram `3/16+(23/96) epsilon` with normalized inverse mass to give `3/16+254 epsilon`. Gaussian central/remote recombination gives `3/16+256 epsilon`; final normalizer handling yields arbitrary positive loss above 3/16. Source signatures and relevant proofs were inspected; this is not a fresh terminal semantic or axiom audit of every imported dependency.

The terminal `LowNormalized` hypotheses explicitly make W_i real nonnegative, which is why (O3c) is legitimate there but not for every arbitrary complex weight allowed by the broader central-tuple theorem. No existential calibration has been universalized. Constants in the original theorems retain their actual dependence and quantifier order; our algebraic identities add no asymptotic uniformity premise.

For fixed K, the collision payment is a constant, at most `2^K` in energy. If K grows with Z, that is a real growing cost and cannot be suppressed. The standard alternative `2^omega(L)<=C_delta L^delta` is unnecessary for the fixed-K result and is not booked as a saving. All principal, exceptional, nonprincipal, height, ray, cutoff and zero cases are preserved by (O1) because H_J is left intact; they have **not** received a new quantitative estimate.

Power ledger for this run:

| Quantity | Proved contribution | New fixed-power gain |
| --- | --- | --- |
| Outer same-norm collision multiplicity | At most 2^|J| | 0 |
| Within-norm ordered cross term, terminal weights | Nonnegative, exact formula | 0 |
| Distinct-norm and different-J interactions | Retained, no new bound | UNKNOWN |
| Fully normalized LOW squared source | No improved bound | No nu established |
| LOW amplitude / final Mertens exponent | No new gain; HIGH/principal/remote unpaid for any proposed change | 0 credited |
| MU-LIFT k | Every fixed integer k>=2 in the obstruction | Not a recurrence |
| MU-LIFT r,G,g | Separate packet fails for 1<=r<k, subpower G; necessary g>=(k-r)/2 for power G | Full recurrence OPEN |

For context only, a proved saving nu in the **fully normalized squared** LOW source would yield at most nu/2 in amplitude before other costs. This run supplies no such nu. The existing true physical slot minimum is a one-time geometric input, not a renewable gain. Marked-HIGH half-t improvements and NNS Co-minus-Div isometry are not new LOW savings.

### H. Falsification, Novelty, And Verification

**Frozen test question:** can separate top-prime payment survive a complete alternating k-lift, and do the proposed norm-fiber counts preserve all finite occurrences? The competing explanation is that the whole source can be small only through complement/cross-fiber interaction. No large wheel or prime scan was requested or run.

The exact standard-library verifier below tests five fixed lift instances, checks every coefficient through each strict upper endpoint against both a sieve and trial factorization, keeps all j-parts, and checks (M3) exactly. The binomial identity was checked for k=2,...,8. These tests validate the implementation and give finite witnesses; they do not prove the asymptotic result.

| B | k | X=B^k-1 | A(X) | Signed j-parts of top packet | C | M(X) | E(B)^2 |
| ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: |
| 9 | 2 | 80 | 10 | 0,-10 | 6 | -4 | 1 |
| 17 | 2 | 288 | 27 | 0,-27 | 20 | -7 | 1 |
| 6 | 3 | 215 | 19 | 0,-57,38 | 20 | 1 | 1 |
| 4 | 4 | 255 | 23 | 0,-138,184,-69 | 22 | -1 | 1 |
| 13 | 3 | 2196 | 143 | 0,-429,286 | 152 | 9 | 1 |

At B=9,k=2,r=1,G=1 the separate packet has squared ratio `100/80=5/4>1`, while the whole source has squared ratio `16/80=1/5`. It is a witness against that separate unit payment, not against the full recurrence. The general no-constant obstruction is the paper PNT argument (M2), not an extrapolated finite fit.

For collision bookkeeping, every J subset in a fixed three-slot split-prime label model was checked: 75 outer tuples, 32 norm profiles, 147 same-profile overlap-mask checks, and maximum product-norm fiber size 8. An ambient model with split pairs plus inert norm 25 and ramified norm 3 checked 4096 squarefree-ideal subsets, including depth, norm collisions and the unit case. The added bad-prime labels are ambient counting controls, not asserted admitted by the original source exclusions. Exact integer complex arithmetic checks arbitrary-complex and nonnegative weight versions, all ordered cross terms, and retained/excluded mixed terms.

**UNSUPPORTED_DIRECT_OAI_NUMERICS:** no actual OAI integral, nontrivial Hecke mode, or physical positive-cross-term witness was evaluated. Formal common H(L) values in the test are only algebra controls. The paper proof, rather than these labels, establishes the original-source correspondence. The false Cartesian-mask shortcut is tested by keeping only `(0,0),(1,1)` from a two-by-two carrier: actual cardinality 2, not 4. Overlapping slots containing the same two ideals make `(P,Q)` and `(Q,P)` share a product, showing why disjointness is essential. These negative controls intentionally violate or change the stated hypotheses and are not advertised as legal-source counterexamples.

**Novelty audit.** Inspected the existing norm-fiber boundary and resonant-NNS Lean modules, `TopPrimeReplacementIsolation`, the truncated prime-wheel kernel, global Mobius reassembly, the finite-prefix lift notes/Lean, Heath-Brown notes/Lean, and earlier Gaussian resonant-collision and high-J notes. Existing generic fiber reindexing and Cauchy inequalities already cover the algebraic framework; existing prime isolation and residual absolute-l1 divergence already obstruct several unsigned approaches. No novelty is claimed for those results. The additional content here is their explicit original-unselected-source specialization, quadratic norm-depth/parity constraint, fixed-slot multiplicity and coherent-sign formula, plus the normalized top-prime budget test after **all** lift-family cancellations. Repository search found no equivalent source-specific declaration in the inspected material; this is a scoped novelty check, not a claim to have proved literature originality.

No desired global estimate is assumed. The OAI result is an independent structural restriction, not an endpoint inequality. The remaining full source norm bound is still target-strength; naming it a cross-fiber bound does not solve it. Similarly (M3) is not an easier estimate just because C and A have names. No complete-LOW or MU-LIFT impossibility is asserted.

**Formal evidence:** no Lean file was created, edited, compiled, or submitted by this role. The new claims remain paper/self-audit. #1083's failed exact-head gate is not used as a theorem. Original pinned source declarations and current main declarations are the formal inputs at their existing scopes. No independent review of this run is claimed.

### I. Conceptual Interpretation

The arithmetic norm map loses ideal labels but, on squarefree Eisenstein products, does not lose factor depth or compensation parity. It also loses only boundedly many actual outer tuple labels at fixed K. This separates two issues: bounded same-norm coherence is explicit, while any useful cancellation must involve genuinely changing norms, selected rows, or returned components. The source cannot be modeled by freely choosing signs for those same-norm collisions.

The top-prime calculation gives a parallel caution on a different carrier: completing internal signed reassembly does not make every meaningful subpopulation independently small. This comparison is structural only. There is no proved occurrence/weight map from rational mu values to Hecke U_a, and none was invented.

### J. Competing Structural Hypotheses

1. Equal-norm compensation-parity reversal: rejected under the precise squarefree/disjoint canonical-slot hypotheses by (O2). Equal-profile atom reversal is also impossible unless both atoms are zero. This does not reject all factor-exchange involutions that change norms or selected rows.
2. Distinct-norm signed restriction of the actual H_J(L): viable but open. It must derive from the literal common selected inverse row and physical scale dependence, retain the coherent norm blocks, and survive the complete returned source.
3. Full MU-LIFT joint invariant: viable but open. Paying the top-prime packet separately at subcritical scale is rejected; paying its signed combination with its complement is not. Do not replace this by another coefficient-radius theorem on the next MU-LIFT turn.

### K. Specialist Handoffs

These are published requests for the specialists' next actual configured invocations, not agent launches or claims of completed relay work.

| Recipient | Implementation-Sized Request And First Gate |
| --- | --- |
| Adversarial Referee | Reconstruct O2 first from the quadratic factorization and canonical slot injectivity; independently test O1/O3 against arbitrary complex central weights versus real nonnegative terminal weights. Audit M2's r,G quantifiers and strict endpoint. Verdict requested on the paper statements only. |
| Analytic Type II | Use O1's exact `H_J(L)` and O3's coherent block as retained inputs. Seek a genuine restriction on the distinct-L Hermitian sum or a selected-row estimate; do not assign random phases or a negative within-norm credit. First missing estimate is stated in L. |
| Prime Census Laboratory | A future direct OAI test should choose truly admitted conjugate/split norm collisions, with original ray/exclusion masks and a rigorous nonzero enclosure for H_J(L); test empty/full/partial J, principal and nontrivial characters. Predicted result: within-L pair products are nonnegative under terminal W. Reject any observed negative value only after validating all source inputs and interval errors. If certification is unavailable, retain UNSUPPORTED_DIRECT_OAI; do not enlarge this algebra scan. |
| Owner Payment | Any native-to-OAI map must retain occurrence `(J,a,b)`, the selected Hecke phase and row, and the norm-depth sign restriction. A first differing slot is not a chronological owner. Compare the exact moving intersection/new/exit identity with the actual native source; no credit is transferred here. |
| Lean Verification | First record the diagnosed #1083 errors at the exact head without treating error-generated sorryAx as a theorem or editing another author's branch. Any permitted repair must preserve original `ContDiff` type/notation, qualify the realification namespace and fix finite-row universe inference before a fresh warning-fatal exact-head audit. Only after independent acceptance, consider a narrow O1/O2 interface if it is needed by an active quantitative proof; do not create a generic fiber-sum filler or formalize this claim merely for theorem volume. |
| Coordinator / Proof Architect | Record MU-LIFT coverage, the scoped separate-payment rejection, and O2/O3 as source-specific pending-review restrictions. Deduplicate generic Fubini/Gram results from #1083 and older main modules. Preserve the next CORR4 turn and the full LOW/Hecke versus native-carrier distinction. No campaign change is proposed. |

### L. First Independently Missing Theorem

**MU-LIFT continuation:** for some fixed k>=2 and 1<=r<k, prove a genuine complete-prefix estimate on the original lift, with subpower G or an independently useful quantified power budget,

```text
sup_(B<=X<B^k) |sum_(n<=X) H_(B,k)(n)|/sqrt(X)
    <= G(B) E(B)^r,
```

and the actual whole-prefix/scale-chain closure. At X=B^k-1 the unpaid expression is the **joint** `C_(B,k)(X)-A(X)`, not either term separately. This is the registered hard estimate, not a new assumed invariant. No recurrence parameters have been supplied by this run.

**OAI continuation:** on the original admitted source, derive an independent arithmetic estimate for

```text
sum_L |V_L|^2 + sum_(L!=M) Re(V_L conjugate(V_M)),
```

or for its fully returned multi-J/dyad aggregate, sufficient to improve the normalized LOW bound after every normalizer, HIGH, principal, exceptional and remote term. O2 bounds only collision multiplicity; O3 identifies the unavoidable nonnegative same-norm part. A hypothesis asserting the desired improved full expression would be a conditional restatement, not the missing new arithmetic input. No source-to-endpoint net gain is established.

### M. Source Ledger And Next-Run Resume Capsule

The following blobs were fetched in this invocation. OAI paths are at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`; RH_Lean main paths are at `25127ac796a1d2ace7a8b3ddb27a02154cc48ef2`. The PR-only signed-Gram file is separately labeled. Declaration inspection is not a fresh compiler run.

| Source | Blob SHA |
| --- | --- |
| [OAI/Detector/LowSlotPolynomial.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSlotPolynomial.lean) | `b1dcb5a1e51afad1d39ccd91fa58a764e39629ba` |
| [OAI/Detector/LowSlotSplit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSlotSplit.lean) | `8c8fe01a1b3fffe3b06839c2befc2ddae39a2c9b` |
| [OAI/Detector/LowSelectedSum.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSelectedSum.lean) | `a54eb9ec6a5beb0db57ce9baa658718aab808af1` |
| [OAI/Detector/CanonicalSlots.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/CanonicalSlots.lean) | `0ae88f818a6c8f6b2c8dd4d5254ce34a14b026cf` |
| [OAI/Detector/PhysicalNorms.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/PhysicalNorms.lean) | `36f6fd2f2b11ec0954bb7cf56c5c1d3484b99897` |
| [OAI/Detector/LowSlotMarks.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSlotMarks.lean) | `4dbdd321565d5bc171f5766608a367d2ee1da15a` |
| [OAI/Arithmetic/EisensteinEmbedding.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean) | `00fc7c168e5aff185607d219e34461c47994284d` |
| [OAI/Arithmetic/EisensteinIdeals.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean) | `cc49e3d0babdd98b025220c0ce8513e794eba521` |
| [OAI/Detector/LowSelectedBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSelectedBound.lean) | `695d81de46038693b9c701d55e81fe43d18d52d2` |
| [OAI/Detector/LowNominalEnergy.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowNominalEnergy.lean) | `55b1a3abfb7fa07da3f9ac8c393b375d1c86329b` |
| [OAI/Detector/LowPhysicalInverseBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowPhysicalInverseBound.lean) | `58bc871a18d9baa43d1684209027b8a2ebed87d6` |
| [OAI/Detector/LowTupleGram.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowTupleGram.lean) | `710598c8bef4d1a1ec98aa7e68b00369962c3d17` |
| [OAI/Detector/LowCentralTuple.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowCentralTuple.lean) | `bb7c4eaf4dc3ec5a1467d76e4a3c576e32a433c9` |
| [OAI/Detector/LowSlotScales.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowSlotScales.lean) | `f8ebfef6a7efe1ecb63a61975f240999afe2f0eb` |
| [OAI/Detector/LowUnselectedMass.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowUnselectedMass.lean) | `4233ef473b8a71d4a331d0eb5ddc0c6cd7dacb4f` |
| [OAI/Detector/LowGaussianDyad.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowGaussianDyad.lean) | `d890d50dcfdb510ef4dda3bcbccf946173e4537e` |
| [OAI/Detector/LowGaussianCentral.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowGaussianCentral.lean) | `46d68f3c6e684984312b3b5603643c826cec5be4` |
| [OAI/Detector/LowGaussianSum.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowGaussianSum.lean) | `1bfd335a4db0973b7b5a9342a03eab82eddfe60d` |
| [OAI/Detector/LowCommonBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowCommonBound.lean) | `328f8ae217343c8766a6fead1f7d0d4abdfba3fc` |
| [OAI/Detector/LowNormalized.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowNormalized.lean) | `3a9f0257cdbde8fce7cc026ac62ef672c3e9820c` |
| [OAI/Detector/FinalAssemblySource.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblySource.lean) | `93c4852b1fae505afd77a4e6b800613fcf253667` |
| [research/MERTENS_FINITE_PREFIX_EXTENSION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MERTENS_FINITE_PREFIX_EXTENSION.lean) | `131e9af86207a42d4bf6488e3f64c9ce4f97e5df` |
| [research/MERTENS_HEATH_BROWN_SIGNED.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MERTENS_HEATH_BROWN_SIGNED.lean) | `af69b4811cf9f523eb7c96fb0ca836b2cdbd1180` |
| [research/MERTENS_SIGNED_HYPERBOLA.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MERTENS_SIGNED_HYPERBOLA.lean) | `d199571f19346797229a25b0fa53c6e80499999f` |
| [RHLean/Arithmetic/TopPrimeReplacementIsolation.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/RHLean/Arithmetic/TopPrimeReplacementIsolation.lean) | `950173fc3e5271f3eeed8cc6f7831ca89bb11a90` |
| [RHLean/Analysis/NativePNTTransfer.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/RHLean/Analysis/NativePNTTransfer.lean) | `8b981fe2bd212b2e21e7cc1961e5b2d7f083a906` |
| [research/PRIME_WHEEL_TRUNCATED_MOBIUS_KERNEL.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/PRIME_WHEEL_TRUNCATED_MOBIUS_KERNEL.lean) | `58e266fe45cbd7f46c1613f3a5eeda6af22bfe48` |
| [research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean) | `11bc35cfd07c6dac83785b32bbd9be92def03f95` |
| [research/VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022.lean) | `b96967e2f8f81e37f80b7212662bc363897c63b7` |
| [research/VF_919_NNS_NORM_FIBER_BOUNDARY_CORRESPONDENCE_20261021.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/VF_919_NNS_NORM_FIBER_BOUNDARY_CORRESPONDENCE_20261021.lean) | `5b3cdf68b5b00c69cca86d26d8c873a29033e21b` |
| [research/MERTENS_FINITE_PREFIX_EXTENSION.md](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MERTENS_FINITE_PREFIX_EXTENSION.md) | `b0b311e3281a2957ed513d66d59b86e401796ae2` |
| [research/MERTENS_HEATH_BROWN_SIGNED.md](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/MERTENS_HEATH_BROWN_SIGNED.md) | `f3a4cc1f73cce00983137328481e3cb41f446180` |
| [docs/MERTENS_AMPLIFICATION_BUDGET.md](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/docs/MERTENS_AMPLIFICATION_BUDGET.md) | `62bbe73c4755eaa64772ec2cc2731936c01b49cd` |
| [research/OAI_LOW_GAUSSIAN_RESONANT_COLLISION_GLOBAL_A_GATE_20261025.md](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/OAI_LOW_GAUSSIAN_RESONANT_COLLISION_GLOBAL_A_GATE_20261025.md) | `59ba23f768b78b4917e72d34cee69f2801f6e0a8` |
| [research/OAI_LOW_GAUSSIAN_COMPENSATED_TOP_J_ATTACK_20261025.md](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/OAI_LOW_GAUSSIAN_COMPENSATED_TOP_J_ATTACK_20261025.md) | `913e4ac70716882cfe82e11b306f2c997ec408f9` |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919NativeSevenEighthsReplay.lean) | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| [research/oai_434/VF919NativeEnergyInduction.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919NativeEnergyInduction.lean) | `350eec60b5ed1fd5fda7b3313654c1bbe5ac4e7e` |
| [research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean) | `1ead3888a1f59cacc71f482f6d4ce9c9ad31903a` |
| [research/oai_434/VF919NativeSourceMoments.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919NativeSourceMoments.lean) | `4e5326b983f5110f7138d222f7b1be71c5694dfc` |
| [research/oai_434/VF919TiltedLowReflection.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919TiltedLowReflection.lean) | `88293c915d67eefee2e1e989082248b8a52f2ae7` |
| [research/oai_434/VF919ActualSlotMinRetighten.lean](https://github.com/OVVO-Financial/RH_Lean/blob/25127ac796a1d2ace7a8b3ddb27a02154cc48ef2/research/oai_434/VF919ActualSlotMinRetighten.lean) | `138c4726085995b966204406805f70082402bec4` |
| [research/oai_434/VF919OriginalLowTupleSignedGram.lean](https://github.com/OVVO-Financial/RH_Lean/blob/d8cdb9fa1c90fb1383b7dc79745e466f2b0f4d56/research/oai_434/VF919OriginalLowTupleSignedGram.lean) (PR ONLY, FAILED GATE) | `3701d2f1bc9211e6aa63b6215bba3b6f56f8a7d3` |


```text
ENGINE_VERSION: 2026-11-01 with source-first update 2026-11-03
RUN: actual 2026-11-03 18:06:00 EST scheduled invocation; RUN_ID_UNAVAILABLE
CLAIM: 20261103-wheel-3, O1-O4 and M1-M3
TASK: due MU-LIFT; bounded NEXT-WHEEL original physical norm-collision comparison
MAIN: 25127ac796a1d2ace7a8b3ddb27a02154cc48ef2
POLICY_BLOB: b6980c30e63bb8c9ddfc8d6fa86a2bb401707fa6
OAI_PIN: 1581d4cbdd69a0faf34b2089614fe2a814316a6a
RESUMED: 20261102-wheel-3 equations 54-64; 20261103-coordinator-2
ACTUAL_RESULT: source-specific finite structural PAPER_PROOF;
  scoped MU-LIFT separate-payment obstruction; exact finite controls PASS
REVIEW: SELF_AUDIT; independent review PENDING
FORMAL_STATE: no new Lean; PR1083 failed required gate at stated exact head
ETA_GATE: inherited accepted strict main gain only; THIS_RUN_NEW_GAIN=NONE
LAST_JUSTIFIED: O3 complete norm-fiber Gram; M3 complete prime/complement square
FIRST_UNSUPPORTED: distinct-norm returned signed estimate;
  subcritical full lift recurrence and chain, not separate prime payment
PROTECTED_COVERAGE: CORR4 wheel-1; FINITE-AC wheel-2; MU-LIFT wheel-3
NEXT_DISTINCT_ROUTE_DUE: CORR4 unless an actual review repair supersedes it
NEXT_CORR4_RESUME: wheel-1 W10, analytic-2 difference-conditioned credit,
  census-3/4 common-offset obstruction; preserve R=2002 source regression
NEXT_MU_LIFT_RESUME: do not repeat support-radius/factorial or top-prime scans;
  derive an independent joint invariant for the retained complement
DEPLOYMENT_ACK: consumed new main/source-first policy during this invocation;
  O1-O4 are actual source-qualified proof steps, not a read-only acknowledgement

SOURCE_FIRST_VERSION: 2026-11-03
PR1083_LIVE_HEAD_STATE: d8cdb9fa1c90fb1383b7dc79745e466f2b0f4d56,
  OPEN DRAFT; 13 success, 1 failure; no complete axiom acceptance
ORIGINAL_DECLARATION: compensation_tuple_low_polynomial
CHARACTER_J_MASK_ADMISSION: arbitrary original eta; every J including empty,
  full and partial; actual disjoint canonical prime-ideal pools outside S;
  all original selected masks and inverse rows retained
U_A_OCCURRENCE_MAP: full tuple <-> (a,b); U_a already includes full selected sum
LOW_INVERSE_SQRT_Q_GAUSSIAN_TRIANGLE: 5/6-2d+507eps -> 507eps/2;
  scalar Gram 3/16+23eps/96; norm_sum_le is the local sign loss
NNS_CO_DIV_GRAM: exact isometry only; ordered distinct-fiber terms retained
NEW_RESTRICTION: squarefree norm depth fixes compensation parity;
  m_J(L)<=2^|J|; terminal same-norm cross interaction nonnegative
SOURCE_SQUARED_GAIN: NONE; AMPLITUDE_GAIN: NONE; NET_BETA_GAIN: NONE
PRINCIPAL_HIGH_REMOTE_EXCEPTIONS_TAILS: unchanged and not newly paid
STRESS_TEST: native exact lift and labeled algebra controls PASS;
  UNSUPPORTED_DIRECT_OAI_NUMERICS; no source integral sign witness claimed
NEXT_DECISIVE_ACTION: independent O1-O3 scope review, then an actual
  distinct-norm/selected-row arithmetic estimate with complete return
```

**Execution limits and publication:** direct git transport was unavailable through the environment proxy, so authorized GitHub read/write tools were used. No local Lean, proof-branch/PR/issue edit, main/policy write, other-role write, schedule change, merge, or agent launch occurred. Only the existing dated own-role report is the remote write target. Early checkpoint commit `509ce9787993c83cc271c153cb4434627843c638`, blob `5ed23d2c51f2f7fe5b9b35bf19f7f8f77968297c`, was already read back exactly. Final publication is claimed only by the subsequent verified receipt, not by this prepared text.

### Executed Reproducer For 20261103-wheel-3

Python standard library only. Script SHA-256: `59ec13997fd42152560fc4a309e4df9ea4d4621fdae0b57d6236abcd11b84b3b`. Execute with Python 3; no dependency on a Lean runtime or floating-point sign test. This code is part of the own-role report, not a repository proof-module edit.

```python
"""Exact finite controls, not Lean or a numerical evaluation of OAI integrals."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod
import json


def primes_and_mu(limit):
    prime = [True] * (limit + 1)
    prime[0:2] = [False, False]
    mu = [1] * (limit + 1)
    mu[0] = 0
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p * 2, limit + 1, p):
                prime[n] = False
            for n in range(p, limit + 1, p):
                mu[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    return prime, mu


def trial_mu(n):
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def convolution(a, b):
    limit = len(a) - 1
    out = [0] * (limit + 1)
    for i in range(1, limit + 1):
        if a[i]:
            for j in range(1, limit // i + 1):
                out[i * j] += a[i] * b[j]
    return out


def lift_case(B, k):
    X = B**k - 1
    prime, mu = primes_and_mu(X)
    assert all(mu[n] == trial_mu(n) for n in range(1, X + 1))
    a = [mu[n] if n < B else 0 for n in range(X + 1)]
    unit = [0] * (X + 1)
    unit[1] = 1
    zeta = [0] + [1] * X
    a_power, zeta_power = unit, unit
    lift = [0] * (X + 1)
    top = [p for p in range(X // 2 + 1, X + 1) if prime[p]]
    assert all(p >= B for p in top)
    packet_parts = []
    for j in range(1, k + 1):
        a_power = convolution(a_power, a)
        if j > 1:
            zeta_power = convolution(zeta_power, zeta)
        term = convolution(a_power, zeta_power)
        assert all(term[p] == j - 1 for p in top)
        coefficient = (-1) ** (j - 1) * comb(k, j)
        packet_parts.append(coefficient * sum(term[p] for p in top))
        for n in range(1, X + 1):
            lift[n] += coefficient * term[n]
    assert lift == mu
    A = len(top)
    assert sum(packet_parts) == -A
    prefix, E2 = 0, Fraction(0)
    for n in range(1, B):
        prefix += mu[n]
        E2 = max(E2, Fraction(prefix * prefix, n))
    total = sum(lift)
    complement = total + A
    assert total * total == complement**2 + A**2 - 2 * A * complement
    return {"B": B, "k": k, "X": X, "top_prime_count": A,
            "signed_packet_parts": packet_parts, "M_X": total,
            "complement": complement, "E_squared": str(E2),
            "packet_squared_over_X_E_squared": str(Fraction(A * A, X) / E2)}


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def csum(values):
    out = (0, 0)
    for value in values:
        out = cadd(out, value)
    return out


def energy(a):
    return a[0] ** 2 + a[1] ** 2


def real_pair(a, b):
    return a[0] * b[0] + a[1] * b[1]


def subsets(items):
    for r in range(len(items) + 1):
        yield from combinations(items, r)


def omega(n):
    count, p = 0, 2
    while p * p <= n:
        if n % p == 0:
            count += 1
            while n % p == 0:
                n //= p
        p += 1
    return count + (n > 1)


def eisenstein_squarefree_depth(n):
    depth, p = 0, 2
    while p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            if p == 3:
                assert exponent == 1
                depth += 1
            elif p % 3 == 1:
                assert exponent <= 2
                depth += exponent
            else:
                assert exponent == 2
                depth += 1
        p += 1
    return depth


def collision_checks():
    # Distinct labels model the two ideals above each split rational prime.
    # The common H(L) below is formal algebraic data, not an OAI integral.
    slots = (((7, 0), (13, 0), (19, 0), (19, 1)),
             ((7, 1), (13, 1), (31, 0), (31, 1)),
             ((37, 0), (37, 1)))
    labels = sum(slots, ())
    assert len(set(labels)) == len(labels)
    profile_count = tuple_count = mask_count = 0
    maximum_norm_fiber = 0
    for J in subsets(tuple(range(len(slots)))):
        tuples = list(product(*(slots[i] for i in J)))
        tuple_count += len(tuples)
        profiles, norms = defaultdict(list), defaultdict(list)
        products = set()
        for a in tuples:
            nu = tuple(label[0] for label in a)
            L = prod(nu)
            assert eisenstein_squarefree_depth(L) == len(J)
            profiles[nu].append(a)
            norms[L].append(a)
            products.add(frozenset(a))
        assert len(products) == len(tuples)
        for nu, fiber in profiles.items():
            profile_count += 1
            ms = [sum(label[0] == n for label in slots[i]) for i, n in zip(J, nu)]
            m = prod(ms)
            assert len(fiber) == m
            overlaps = Counter(tuple(i for i in range(len(J)) if a[i] == b[i])
                               for a in fiber for b in fiber)
            for mask in subsets(tuple(range(len(J)))):
                predicted = prod(ms[i] if i in mask else ms[i] * (ms[i] - 1)
                                 for i in range(len(J)))
                assert overlaps[mask] == predicted
                mask_count += 1
            for j in range(len(J)):
                actual = sum(a[:j] == b[:j] and a[j] != b[j]
                             for a in fiber for b in fiber)
                expected = prod(ms[:j]) * ms[j] * (ms[j] - 1) * prod(x*x for x in ms[j+1:])
                assert actual == expected
        for L, fiber in norms.items():
            maximum_norm_fiber = max(maximum_norm_fiber, len(fiber))
            assert len(fiber) <= 2**omega(L) <= 2**len(J)
        for positive in (False, True):
            atoms = {}
            for a in tuples:
                nu = tuple(label[0] for label in a)
                L = prod(nu)
                weight = (1, 0)
                for i, n in zip(J, nu):
                    w = ((i + n) % 3, 0) if positive else ((n + i) % 5 - 2, (n - i) % 3 - 1)
                    weight = cmul(weight, w)
                # Absorb the common L^(-3/2) and sign into formal H.
                H = ((-1)**len(J) * (L % 7 - 3), (-1)**len(J) * (L % 5 - 2))
                atoms[a] = cmul(weight, H)
            for fiber in profiles.values():
                assert len({atoms[a] for a in fiber}) == 1
                u, m = atoms[fiber[0]], len(fiber)
                assert energy(csum(atoms[a] for a in fiber)) == m*m*energy(u)
                assert sum(real_pair(atoms[a], atoms[b]) for a in fiber for b in fiber if a != b) == m*(m-1)*energy(u)
            grouped = {L: csum(atoms[a] for a in fiber) for L, fiber in norms.items()}
            D = sum(energy(atoms[a]) for a in tuples)
            grouped_energy = sum(energy(value) for value in grouped.values())
            assert grouped_energy <= 2**len(J) * D
            if positive:
                assert all(real_pair(atoms[a], atoms[b]) >= 0
                           for fiber in norms.values() for a in fiber for b in fiber)
                assert D <= grouped_energy
            cross = sum(real_pair(grouped[L], grouped[M]) for L in grouped for M in grouped if L != M)
            assert energy(csum(atoms.values())) == grouped_energy + cross
            admitted = [a for a in tuples if sum(v[1] for v in a) % 2 == 0]
            excluded = [a for a in tuples if a not in admitted]
            U, V = csum(atoms[a] for a in admitted), csum(atoms[a] for a in excluded)
            assert energy(csum(atoms.values())) == energy(U) + energy(V) + 2*real_pair(U, V)
    # Ambient squarefree-ideal model also includes inert norm 25 and ramified 3.
    # These extra labels are not asserted admitted by the physical bad-prime mask.
    ambient_labels = labels + ((25, 0), (3, 0))
    ideal_norms = Counter()
    for subset in subsets(ambient_labels):
        L = prod(label[0] for label in subset)
        assert eisenstein_squarefree_depth(L) == len(subset)
        ideal_norms[L] += 1
    assert all(count <= 2**omega(L) for L, count in ideal_norms.items())
    # Negative controls for unjustified Cartesian admission and overlapping slots.
    square = list(product((0, 1), repeat=2))
    admitted = [a for a in square if a[0] == a[1]]
    assert len(admitted) == 2 and len(square) == 4
    overlap = list(product(((7, 0), (13, 0)), repeat=2))
    distinct = [a for a in overlap if a[0] != a[1]]
    assert len(distinct) == 2 and len({frozenset(a) for a in distinct}) == 1
    assert list(product(*())) == [()]
    assert list(product(())) == []
    return {"subsets_J": 8, "unselected_tuples": tuple_count,
            "norm_profiles": profile_count, "overlap_mask_checks": mask_count,
            "maximum_product_norm_fiber": maximum_norm_fiber,
            "squarefree_ideal_model_subsets": 2**len(ambient_labels),
            "scope": "exact algebra; UNSUPPORTED_DIRECT_OAI_NUMERICS"}


def main():
    for k in range(2, 9):
        assert sum((-1)**(j-1) * comb(k, j) * (j-1) for j in range(1, k+1)) == -1
    cases = [lift_case(B, k) for B, k in ((9, 2), (17, 2), (6, 3), (4, 4), (13, 3))]
    assert Fraction(cases[0]["packet_squared_over_X_E_squared"]) > 1
    print(json.dumps({"lift": cases, "collision": collision_checks(),
                      "status": "PASS"}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
```

### Exact Reproducer Output

```json
{
  "collision": {
    "maximum_product_norm_fiber": 8,
    "norm_profiles": 32,
    "overlap_mask_checks": 147,
    "scope": "exact algebra; UNSUPPORTED_DIRECT_OAI_NUMERICS",
    "squarefree_ideal_model_subsets": 4096,
    "subsets_J": 8,
    "unselected_tuples": 75
  },
  "lift": [
    {
      "B": 9,
      "E_squared": "1",
      "M_X": -4,
      "X": 80,
      "complement": 6,
      "k": 2,
      "packet_squared_over_X_E_squared": "5/4",
      "signed_packet_parts": [
        0,
        -10
      ],
      "top_prime_count": 10
    },
    {
      "B": 17,
      "E_squared": "1",
      "M_X": -7,
      "X": 288,
      "complement": 20,
      "k": 2,
      "packet_squared_over_X_E_squared": "81/32",
      "signed_packet_parts": [
        0,
        -27
      ],
      "top_prime_count": 27
    },
    {
      "B": 6,
      "E_squared": "1",
      "M_X": 1,
      "X": 215,
      "complement": 20,
      "k": 3,
      "packet_squared_over_X_E_squared": "361/215",
      "signed_packet_parts": [
        0,
        -57,
        38
      ],
      "top_prime_count": 19
    },
    {
      "B": 4,
      "E_squared": "1",
      "M_X": -1,
      "X": 255,
      "complement": 22,
      "k": 4,
      "packet_squared_over_X_E_squared": "529/255",
      "signed_packet_parts": [
        0,
        -138,
        184,
        -69
      ],
      "top_prime_count": 23
    },
    {
      "B": 13,
      "E_squared": "1",
      "M_X": 9,
      "X": 2196,
      "complement": 152,
      "k": 3,
      "packet_squared_over_X_E_squared": "20449/2196",
      "signed_packet_parts": [
        0,
        -429,
        286
      ],
      "top_prime_count": 143
    }
  ],
  "status": "PASS"
}
```


### Verified Publication Receipt - 2026-11-03 18:31:37 EST (-0500)

- Final synthesis commit: `ab96791e6aa8aabc5ecc4ed4eb87cc3592c5fb66`; report blob: `95067a781d5166a65a1bbdb51c311540b4c2ff0e`.
- Pinned-commit readback matched all 154,203 characters exactly and preserved the preceding 93,433 characters. The commit changed only `research/agent_reports/2026-11-03/30-finite-wheel.md`, with 800 added lines and zero deleted lines.
- Verified content includes claim `20261103-wheel-3`, O1-O4, M1-M3, all A-M sections, exact reproduction source/output, source and continuity hashes, the failed exact-head #1083 gate, specialist requests and both continuation capsules.
- Research execution is COMPLETE for this invocation. New mathematics remains PAPER_PROOF / SELF_AUDIT, independent review PENDING, no new Lean declaration and no new global exponent or RH claim. Direct OAI numerical integration remains UNSUPPORTED_DIRECT_OAI_NUMERICS.
- This receipt records the already verified synthesis commit, not its own future commit. Publication does not imply that another agent has read the handoff or executed.
