# RH_Lean agent daily report - 2026-10-28 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Pinned main:** `904f056ea039e7938587a8254125b18eab45cfd0`  
**Authority:** `AGENTS.md` blob `d11dea7ea8f2206ed5147f0231846d0a4652f8e9`; `CURRENT_PROOF_CONTRACT.md` blob `24bd727096001b68c76b28fe70c99b8d548d7bfe`.  
**New claim:** `20261028-wheel-1`  
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW / NEW UNIFORM INCIDENCE SPARSITY`, `FINITE_COMPUTATION`, `NO_FIXED_ETA_GAIN`, `NO_RH`.  
**Registry disposition:** informs `OPEN-FINITE-AC` and the new Euler mechanism downstream of merged #1035; propose `MECH-EULER-CARRY-PHASE-INCIDENCE` only after independent review. It does not change the DAG today.

## A. Main result

### Claim `20261028-wheel-1`: simultaneous zero carry and zero modular phase are divisor-sparse

Put
[
 N=R-1,qquad L=R+1,qquad
 I_q=(lfloor N/(q+1)floor,lfloor N/qfloor].
]
For (q>0), (ain I_q), (a
mid N), and (b>0), define the two exact Euclidean residues
[
 t_a=Nmod a,qquad ho_{q,b}=Lqmod b.
]
The green stacked theorem `eulerBucketCarry_eq_euclidean` gives the literal original carry
[
 C_{q,b}(a)=
 leftlfloorrac{aho_{q,b}+Lt_a}{ab}ightfloor.
 	ag{1}
]

Then:

1. **Zero-carry triangular exclusion.**
   [
   C_{q,b}(a)=0 quadLongrightarrowquad b>q.
   	ag{2}
   ]
2. **Zero-phase divisor sparsity.** If additionally (ho_{q,b}=0), then
   [
   q<b,qquad bmid Lq.
   	ag{3}
   ]
   Hence, for every fixed quotient (q) and every fixed row (ain I_q), the simultaneous-zero columns are contained in
   [
   {b:q<b, bmid Lq};
   ]
   there are at most (	au(Lq)) of them, uniformly in the physical cutoff.
3. **Growing-carrier count.** Let (Z(R,Q,B)) be the number of triples
   [
   1le q<Q,quad ain I_q,quad a
mid N,quad 1le ble B
   ]
   satisfying both (C_{q,b}(a)=0) and (ho_{q,b}=0). Then the exact finite incidence bound is
   [
   Z(R,Q,B)le
   sum_{q=1}^{Q-1}
   left(leftlfloorrac Nqightfloor-
         leftlfloorrac N{q+1}ightflooright)	au(Lq).
   	ag{4}
   ]
   Using only divisor pairing (	au(m)le2sqrt m), bucket width
   [
   |I_q|le rac{N}{q(q+1)}+1,
   ]
   and (sum_{qge1}q^{-3/2}le3), one obtains
   [
   Z(R,Q,B)le2sqrt L,(3N+Q^{3/2}).
   	ag{5}
   ]
   In particular, if (Qlesqrt N), then
   [
   Z(R,Q,B)le8sqrt3,N^{3/2}.
   	ag{6}
   ]
   The full unpunctured ((a,b)) incidence carrier for (Qasympsqrt N) and (B=N-lfloorsqrt Rfloor) has order (N^2). Thus the simultaneous-zero locus has elementary relative density (O(N^{-1/2})). Standard divisor estimates would sharpen this to (N^{1+o(1)}), but no such external theorem is needed for (5)-(6).
4. **Sharp nonemptiness warning.** The locus is not uniformly finite. For every odd (Rge9), set
   [
   b=L/2,qquad q=1.
   ]
   This column is inside the unpaid cutoff (ble N-lfloorsqrt Rfloor). Every integer
   [
   2N/3<a<N
   ]
   belongs to (I_1), is a nondivisor of (N), has (ho_{1,b}=0), and has (C_{1,b}(a)=0). There are exactly
   [
   N-1-lfloor2N/3floor=lceil N/3ceil-1
   	ag{7}
   ]
   such rows. The theorem therefore proves two-dimensional sparsity, not disappearance.

This is a new source-specific incidence restriction on the literal carry. It is not another unsigned wheel-capacity constant.

## B. Proof

Because (a
mid N), (t_a=Nmod a) is a positive integer. If (C_{q,b}(a)=0), equation (1) implies
[
 aho_{q,b}+Lt_a<ab.
]
Dropping the first nonnegative term and using (t_age1) gives (L<ab), hence (b>L/a). Membership (ain I_q) gives (ale N/q), so (aqle N<L). Therefore (q<L/a<b), proving (2).

If (ho_{q,b}=0), its definition is exactly (bmid Lq). Combining with (2) proves (3). For each (q), there are (|I_q|) possible rows before the divisor punch and at most (	au(Lq)) phase-zero columns; removing divisor rows and imposing (ble B) can only reduce this count. This proves (4).

For (5),
[
 |I_q|	au(Lq)
 le2sqrt Lleft(Nq^{-3/2}+q^{1/2}ight).
]
Summing (q<Q), bounding the first series by (3), and the second by (Q^{3/2}), gives (5). When (Qlesqrt N), (Q^{3/2}le N) and (L=N+2le3N), which gives (6).

For the family (7), odd (R) makes (b=L/2) integral. The inequality (2lfloorsqrt Rfloorle R-3), valid for (Rge9), is equivalent to (ble N-lfloorsqrt Rfloor). If (2N/3<a<N), then (ain I_1=(lfloor N/2floor,N]). A proper divisor of (N) cannot exceed (N/2), so (a
mid N). Also (bmid L), hence (ho_{1,b}=0), and (1) becomes
[
 C_{1,b}(a)=leftlfloorrac{L(N-a)}{a(L/2)}ightfloor
 =leftlfloorrac{2(N-a)}aightfloor=0.
]
The interval count is (7).

## C. What the theorem does and does not pay

The result rules out a proposed strategy in which exact zero modular phase supplies a positive-density portion of the two-dimensional unpaid Euler interior. At square-root quotient depth, the phase-zero/carry-zero cells occupy at most (O(N^{3/2})) of an order-(N^2) carrier by elementary arithmetic.

It does **not** bound:

- zero carry with nonzero phase;
- nonzero carry levels and their signed Mertens increments;
- the complete four-term (U_R) isolated in PR #1041;
- the terminal indexed (E_Q) mode, complementary (T_Q), or small-(a) punctured tail;
- any signed sum after Möbius weights are restored.

The linear family (7) is the decisive falsifier against the stronger false statement that simultaneous zeros are (O(1)) per quotient. Its concentration on one column also explains why row counts alone do not supply a global signed estimate.

The first independently missing lemma remains a signed estimate on the full coupled complement, or a new arithmetic relation coupling the divisor-sparse zero-phase columns to the nonzero-phase remainder. No estimate may spend the family (7) once as a zero-carry row and again as an endpoint or historical occurrence.

## D. Exact source and formal evidence

Current main is `904f056ea039e7938587a8254125b18eab45cfd0`, the merge of #1035. Relevant merged blobs:

- `research/EULER_SELF_DUAL_POINTWISE_20261027.lean`: `c327c556f39ee7014fd774b24d0f95a1ece050e0`;
- `research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean`: `e97561ef330a9996fd807d8910369f0698147b01`;
- `research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean`: `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`.

The exact Euclidean carrier is on the green stacked Euler PR chain:

- #1036 head `c3ef5e99be34ae05db60b10ee71cbe011cf86754`, rank-one source blob `e482711a3f55c1f59fc771f108671477f51732f2`;
- #1037 head `eb4c7fef136b696c773a5b5c685118cd3fc89a44`, carry source blob `4a25d5ea0edca51dd91e718cb209f9a8e18b048a`;
- #1038 head `71559bd1bc4ad03d3f2bced1dc2dbde4876f92e1`, clipped-interior blob `5593d5822507baef5796e2ef8c12ff3b88300ea0`;
- #1039 head `676602ad73c99992706c86f198d28ab3e688bb3c`, endpoint sparsity blob `c4bc5bcf50f641b0d24902e6a5c49003b4e659ed`;
- #1040 head `05f11a53bccc304727b341d9573bb7ed839da316`, no-drift blob `75a3eef5a2967b28686d0e5bab0f9c4198b54dbd`;
- #1041 head `2f7d1607c2ca3d57919c9a60479b9772ec05018d`, coupled Abel blob `7852d08fb2488c869067d2ea57244edd83377256`, double-inversion blob `59258e7c0c252f2c8602fb8337e3da180e4197e4`.

All attached workflow runs on each exact head were completed successfully at verification. These PRs remain open drafts and stacked; green CI certifies their stated Lean declarations, not claim `20261028-wheel-1`, which is a paper theorem pending independent review.

## E. Finite falsification

A standard-library exact-integer check exhaustively verified (2) for every
[
2le R<120,quad q,quad ain I_q, a
mid N,quad1le ble N.
]
It also verified the family (7) for every odd (9le R<80), with sample counts:

| R | simultaneous-zero rows |
|---:|---:|
| 9 | 2 |
| 11 | 3 |
| 101 | 33 |
| 1001 | 333 |

This is `FINITE_COMPUTATION`, used only to detect endpoint or inequality mistakes. The universal proof is Section B.

## F. Novelty and no-circularity audit

Repository search found the exact carry formula, divisor-row vanishing, clipped endpoint decomposition, large-(q) singleton theorem, and coupled Abel identities. It did not find the implication (C=0, a
mid NRightarrow b>q), the divisor-sparse simultaneous-zero count, or family (7).

The proof uses only Euclidean division, quotient-bucket membership, divisor pairing, and elementary summation. It assumes no Mertens bound, finite-C inequality, favorable sign, prime distribution, imported (7/8) estimate, or RH. Conversely it supplies no signed cancellation. This is new structural information, not a reformulation of `OPEN-FINITE-AC`.

No wheel modulus was enlarged and no accepted wheel or daughter census was rerun.

## G. Continuity and handoffs

At intake the `2026-10-28` report directory was absent, so all upstream roles were recorded as `TODAY=PENDING`. The complete 2026-10-27 set was consumed as `YESTERDAY=CARRY_FORWARD`:

- Coordinator blob `b12989910667ec44b7cb5cb9e7395a6a5602f560`, claim `20261027-coordinator-1`;
- Owner blob `a559d88d6974ba3b9bd8f9a026058b15f2879309`, claim `20261027-owner-1`;
- Analytic blob `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e`, claim `20261027-analytic-1`;
- Wheel blob `8318a17434501b49d5a948c6dc750790dcdb0183`, claim `20261027-wheel-1`;
- Census blob `842d50e673d5b6967b79835807a05b2d7bef49f8`, claim `20261027-census-1`;
- Referee blob `f7e86621f16ef102520c133287717b0b1aec79e0`, claims `20261027-referee-1..2`;
- Lean Verification blob `2e1c4f807055c964f07b3e6c344d156d803bbc7f`, claim `20261027-lean-1`.

The Wheel/Census/Referee/Lean chain permanently blocks the old zero-cost native-to-OAI owner transfer: split packets need four terms and equal-norm slots are excluded by the existing normalized-low carrier; inert diagonal coefficient matching costs the unbounded factor (q^2). The current result therefore follows the Coordinator's reassignment to the Euler interior rather than reopening that bridge.

`research/agent_reports/EXTERNAL_HANDOFFS.md` remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no handoff newer than 2026-10-18. `EXT-20261018-PNT-1/2/3` remain an exact direct-VF identity, finite falsifiers, and source no-gos; they do not pay this Euler carry incidence.

## H. Mechanism decision and next step

**CONTINUE, with scope:** use (2)-(6) as a falsification gate for any Euler proposal relying on exact modular-phase zeros. Such zeros cannot occupy positive density at square-root quotient depth by elementary incidence alone.

**REJECT:** treating exact phase zero as the main uniform payment for the coupled interior.

**RETAIN:** nonzero-phase cross-column cancellation and full four-term coupling. The next valuable theorem must keep the exact Möbius signs across all columns, or prove an inverse statement showing that failure of the desired estimate forces concentration outside the divisor-sparse zero-phase set.

**Referee handoff:** check the exact meaning of modular phase (ho_{q,b}=0) against the #1037 Euclidean theorem, the (b>q) inequality, count (5), and the odd-root family.

**Census handoff:** no larger scan is needed. If independently testing, enumerate only the exact (Z(R,Q,B)) count at a few held-out roots and compare it to (4); one violation falsifies the theorem.

**Lean handoff:** formalization is optional after referee acceptance. The most useful declarations would be the pointwise (b>q) theorem and the exact finite injection into divisors of (Lq), not an asymptotic wrapper.

## I. Final status

**Independent structural progress:** YES, uniform divisor-sparse simultaneous-zero incidence theorem plus sharp growing family.  
**Independent quantitative signed progress:** NONE.  
**Canonical theorem:** `VFCanonicalSquareVonKochStatement` remains open.  
**Finite-C / fixed eta:** remains open.  
**RH:** not claimed.

## J. Publication verification

The required `IN_PROGRESS` checkpoint was created by commit `d634ddad946bab6f6e6196a1bc9af9e1165f43b9` and read back as blob `f4a81060d41a2f1a9246a7712e272283890277cc`. Final completed-publication commit and blob readback are recorded by the verification-only follow-up.
