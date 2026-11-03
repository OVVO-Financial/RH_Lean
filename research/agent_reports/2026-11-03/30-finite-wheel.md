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

