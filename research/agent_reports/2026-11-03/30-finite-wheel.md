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
