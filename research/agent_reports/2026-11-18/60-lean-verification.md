# RH | Lean Verification - 2026-11-18

## IN_PROGRESS Checkpoint - 20261118-lean-0510-EST/DUAL

Actual scheduled trigger: 2026-11-18 05:10:01 EST (10:10:01 UTC), America/New_York. PLATFORM_RUN_ID=UNAVAILABLE. DUAL labels this investigation, not a platform identifier.

### A. Most Important Result And Current Status

Existing PR #1145 remains open, non-draft and unmerged at 43cbf9310516f26a440b5527ce6dc22a62856248. Direct check-run retrieval confirms all 13 checks passed on that exact head. No repair or redundant CI rerun is required. Latest main is 13b31c6313e274a073d82a01175201185e59e37e, containing merged #1144; its proof head abd9bb34c8fac459e67c63009961b6c26548d7e9 also has 13 successful checks.

The new formalization candidate is 20261117-coordinator-2309-EST/DUAL1-DUAL2, independently ACCEPT_WITH_SCOPE on paper in 20261118-referee-0413-EST/DP. It supplies a uniform finite-profile lower bound for every finite head count, with arbitrary restoration retained. It is not a complete Nyman upper estimate or an RH proof. Original-source review and implementation feasibility are in progress; no new Lean certification is asserted.

### B. Authority And Continuity

Read main AGENTS blob c4f36b772f8a4b0c24fe566b90fafb646073c60f and CURRENT_PROOF_CONTRACT blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038. Governing half-continuation directive blob 96ad4439ec458af6168f7d9cb3eef5dde291d37c takes precedence over older task banners. The canonical actual-prime VF bound remains OPEN.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

The complete nontruncated report tree at 4263f232cd998ab633388698bc07343d402a0a04 was enumerated without a calendar limit. Latest own PROFILE watermark and all available November 17/18 role files were retrieved. Relevant new material is DUAL, AI, PAIR, FD, PN and DP, in that order. Coordinator's 00/90 mirrors have identical blob 125e55aa191083d9c0a982b6dc5a66267e4e4256. Coordinator TODAY=PENDING / NO_VERIFIED_REPORT, YESTERDAY=CARRY_FORWARD; the other five upstream roles have current publications. External inbox remains 7d63d434690d00dffce9c90335d41c4f62d85798 with no new entry after October 18. Detailed scoped continuity and source receipts will be preserved in the final synthesis.

### C. Candidate And Named Consumer

Original profiles are the two complete floor bands (N_i/2,2N_i/3] minus (5N_i/6,N_i], N_i=4^i N. DUAL observes both 2k and 3k on the exact accepted windows. Its lower bound feeds DUAL3's genuine restored necessary condition for the proposed sparse complete-residual construction. The terminal paper consumer excludes offcritical zeros from one common unbounded exact-head sequence with complete subpower energy. That independent upper supplier remains OPEN. PAIR and DP explicitly prevent crediting transform-only iteration as an upper improvement.

Implementation planning is testing an exact four-phase floor-carry bound before introducing any norm estimate. Any strengthened statement will be labeled SELF_AUDIT until actually kernel-verified, not misattributed to the Referee.

### D. Verification And Remaining Work

Pinned Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; PNT+ c39a751132c88b6e8080b74c74023fd95b3d8be0. GitHub Actions is the only Lean execution environment. Direct repository clone failed CONNECT 403; authorized connector reads succeeded. No local Lean, main write, merge, auto-merge, other-agent report edit or agent launch occurred.

EXECUTION=IN_PROGRESS; MATHEMATICS=accepted paper candidate under independent source audit; IMPLEMENTATION=NOT_STARTED; PUBLICATION=READBACK_PENDING. NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN.

## Implementation Checkpoint - DUAL

The intake checkpoint was committed at d80d427c133a882d02cbb5b20789c39e82d02b45, blob 077ad8c5034daf5ca73acf5e855fbeb947568ce1, and read back with exact content equality.

[Draft PR #1146](https://github.com/OVVO-Financial/RH_Lean/pull/1146) now contains the complete all-head proof attempt and focused validation. Branch agent/lean-verification/20261118-all-profile-coercivity originates from main 13b31c6313e274a073d82a01175201185e59e37e. Initial head 6709bc28eb0ea7fa6758df337db681a4b938c932 triggered all 12 relevant workflows. The first dedicated run 44285371982, job 134736539874, failed warning-fatal compilation. Focused repair head 09de408a4f3633107f4cf5ec7b3b07da1d2bf8c5 is awaiting hosted verification.

The repaired issues were source-definition unfolding, explicit nonnegative remainders in the floor quotient argument, exact rewrite targets and quotient types, beta reduction for image injectivity, an overloaded order lemma, and warning-fatal style requirements. No theorem statement, numerical constant, arithmetic carrier, endpoint, hypothesis or checker requirement changed. Failure-generated internal metavariable placeholders were not source proofs or accepted certification.

### Exact Candidate And Independent Proof Plan

For K>=40, every natural n, every t:Nat->Real, q_i=4^i K, define p_q by the existing nymanCorrectionFloor at N=12q with coefficients +1 on (6q,8q] and -1 on (10q,12q]. Let A_q=(3q,3q+floor(q/20)], W be the union of all {2k,3k:k in A_q}, Z=sum_(i<n)t_i p_(q_i), and E_W(f)=sum_(m in W)f(m)^2/[m(m+1)]. The intended result is

```text
(21/10240000)*K*sum_(i<n)t_i^2 <= E_W(Z).
(21/20480000)*K*sum_(i<n)t_i^2-E_W(r) <= E_W(Z+r).
```

The stronger constant is 7N/40960000 at N=12K. It implies the original accepted DUAL1 constant, included as an exact-type consumer. The empty family n=0 is included without a new hypothesis.

New SELF_AUDIT strengthening: the exact integer carry 2*floor(3m/k)-3*floor(2m/k) lies between -1 and 2. Both bands have 2q terms, so |p_q(3m)-(3/2)p_q(2m)|<=3q=N/4, improving the paper's 5N/12. On the exact current window the paired profile is at least (9/5)q; later profiles vanish. A low-energy sample costs at most 18720qE. With c=sqrt(E/(12K)), strong induction gives |t_i|<=1600c(3/4)^i. Summing the squares gives sum t_i^2 <=(40960000/7)c^2, proving the displayed bound. The restoration follows pointwise from (Z+r)^2>=Z^2/2-r^2. These are complete paper arguments; hosted kernel verification is not yet asserted.

Local NON-Lean checks passed 13,342 exact assertions on 20 preregistered (K,n) supports, including K=40,41,59,60, n=0,...,4, exact shifted-Gram elimination, all sample endpoints, literal source reconstruction and three omission controls. Both Python files passed syntax compilation. Finite checks do not establish the universal theorem.

IMPLEMENTATION=DRAFT_PR / CI_PENDING_AFTER_REPAIR. MATHEMATICS=accepted original theorem plus SELF_AUDIT strengthening. The actual complete residual upper supplier remains OPEN; PAIR/DP no-gain and restoration safeguards are unchanged. No local Lean, main write, merge or auto-merge occurred.

## Final Synthesis - 20261118-lean-0510-EST/DUAL

Final synthesis time: 2026-11-18 05:43 EST. This is the same actual scheduled invocation, not a second launch. The earlier checkpoints and failure history above are preserved. The implementation checkpoint was committed at e3c6bb222b71d8047c991f3558dbaf5847c6a738, blob 047961e9b4eae8be3dd2dc880899eeda4e90c3c5, and independently read back with exact byte equality. Final certification below supersedes checkpoint status. This final section is prepared for commit/readback; the resulting publication receipt will be recorded separately after that succeeds.

### A. Most Important Formal Mathematical Result

**PROVED_IN_LEAN / CI_GREEN / REVIEW_READY / UNMERGED.** The complete implementation of DUAL1-DUAL2 is in [PR #1146](https://github.com/OVVO-Financial/RH_Lean/pull/1146) at **146384fe459bd39a7b3d864e2a5c86a270d05dc8**. Its strengthened uniform bound is **7N/40960000**, compared with the accepted paper bound 121N/808704000, on the SAME original two-band profiles and paired observation set, for every finite head count. The arbitrary remainder is retained with its full energy penalty. All 13 checks across 12 workflows passed at that exact head. This is a finite quantitative theorem, not a complete upper estimate or an RH proof.

Existing [PR #1145](https://github.com/OVVO-Financial/RH_Lean/pull/1145) remains CI_GREEN / REVIEW_READY / UNMERGED at 43cbf9310516f26a440b5527ce6dc22a62856248, with all 13 checks passed. Its three-profile theorem on a different observation set is preserved, not duplicated or represented as part of main. No unnecessary rerun was requested.

### B. Current Authoritative Objective And Source Receipts

Main was refreshed again during final preparation and remains **13b31c6313e274a073d82a01175201185e59e37e**, tree bb52099f74d5f8be61ef39fd0d52b00948eb9b26. Live AGENTS and CURRENT_PROOF_CONTRACT blobs remain c4f36b772f8a4b0c24fe566b90fafb646073c60f and 95566e37c8eaeb99ee680660df4f9d2e06ea5038. The actual-prime canonical VF endpoint remains OPEN. The theorem `riemannHypothesis_of_vfCanonicalSquare` retains its explicit `ClassicalVonKochRHCriterion`; it is not an unconditional source supplier.

| Source at inspected main | Blob SHA / scope |
| --- | --- |
| docs/RHLEAN_BOOTSTRAP_TO_HALF_20261116.md | 96ad4439ec458af6168f7d9cb3eef5dde291d37c; current continuation priority |
| docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md | 3e71820a4af722eae7098da6945bb5bcba50dd0d; uncapped actual-publication continuity |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e3ae4280438f591f1ffaddd754a1c3a6d35d0691; original-source/loss/consumer audit |
| research/NYMAN_FLAT_TAPER_RETURN_20261104.lean | 2d23721027ecc44e85b7add02fc632b482f03352; literal correction-floor source |
| research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean | 2da630c1d5fb9302e2097ec1e170cf41c2b40609; imported original coefficient infrastructure |
| research/NYMAN_CORRECTION_ENERGY_20261105.lean | e5453cd32c3c4ebf9ebf41927bcb92e534b2ece7; existing component energy, not all-head coercivity |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb; explicit canonical consumer |
| research/oai_434/VF919WindowErrorClosure.lean | f629db1b2b65d6ec042ac9432397d4b6316200c6; native unconditional baseline |
| research/HISTORICAL_DENSITY_MASK_OBSTRUCTION.lean | 7bf4433fc1f2e70226df211550829057b024dad2; merged #1144 |
| lean-toolchain | ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5; leanprover/lean4:v4.34.1 |
| lakefile.lean | 6ef95e9ebf184d5846fee88a9cdf2db3a38afc97; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, PNT+ c39a751132c88b6e8080b74c74023fd95b3d8be0 |

The strongest reused native theorem is `native_mertens_near_uniform_window_error_closed : MertensGrowthAtMost (7/8-7/(64*nearUniformSlotCount))`, with every-positive-loss semantics, not an exact fixed-power endpoint. The direct [#1119 hosted audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) at 77ee815846d6d534c866f0752aa33b84c385610a was fetched: five closure counts 35358, 35375, 35736, 35737, 35753; only standard axioms. All 14 checks passed there. Nontruncated tree comparison against current main found only RHLean.lean changed among 2,508 preexisting Lean, pin and scripts/lean entries; relevant source/dependencies are unchanged. This is scoped reuse of valid evidence, not a fresh all-main baseline compilation claim.

Latest merged supporting work #1144 was verified at its tested head abd9bb34c8fac459e67c63009961b6c26548d7e9: 13 successful checks. Its [dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44149489941/job/134273552309) reports cached=1, compiled=0, followed by five live theorem audits with closures 262, 312, 336, 399, 104 and only standard axioms. Its obstruction concerns the density-balanced ABSOLUTE error budget below exponent one, not a signed-discrepancy lower bound.

### C. Formalization Queue And Actual Handoff Continuity

The nontruncated agent-reports tree at 4263f232cd998ab633388698bc07343d402a0a04 was enumerated without a date cap. Every available November 17/18 role file was retrieved. Backfill is complete for relevant newly unconsumed sections after the latest own PROFILE watermark, not a claim to have re-audited every historical appendix. Older November 13/14 historical execution gaps remain unverified; no missing launch is invented.

| Role | Latest consumed publication / blob | Prior-day source / disposition |
| --- | --- | --- |
| Coordinator / Architect | Nov 17 DUAL 23:09 EST; 00/90 both 125e55aa191083d9c0a982b6dc5a66267e4e4256, byte-identical mirrors | TODAY=PENDING / NO_VERIFIED_REPORT; YESTERDAY=CARRY_FORWARD; TAIL -> DUAL |
| Owner Payment | Nov 18 AI 00:09; 039fb276df7257e1bb5e3f76eb00e5fd1eb85bb6 | Nov 17 PC 16:15, 6516bf78b096471ccfd2fb8c215e94002544a594 |
| Analytic Type II | Nov 18 PAIR 01:04; a04f961d080aef270fc4fa8fa8933221d51f2d46 | Nov 17 CP 17:11, d4bc53ac1b68f6dadabc4a04a2f5fc8c74f6625f |
| Finite Wheel & Incidence | Nov 18 FD 02:05; 838e4c5b87c1c196ca18f5ae0981069a91dc2760 | Nov 17 PP 18:06, 5c26771c0a266d5112e0b4a4b28aba0132e35ef7 |
| Prime Census | Nov 18 PN 03:11; a62cba06a7fe73975746cf37cb2850615979788a | Nov 17 MR 19:00, 587b0bb3dd66834a18610ab86174f285f81c4b04 |
| Adversarial Referee | Nov 18 DP 04:13; c054e8b37c1580abc42fbac23852c62dfe433e5f | Nov 17 PR 20:13, 103ee17307ac799e20bd4ce17d97ff96101a9e5b |
| Lean Verification | Nov 17 PROFILE 21:08; ee9ed0ace763bf99fea5812490f9541653917938; receipt c4ab95cdebd6a4c2d62d506ae713290b115a6c49 | Previous consumed chain TAIL, PC, CP, PP, MR, PR; resumed #1145 exact-head verification before new work |

New relevant sections were consumed chronologically DUAL -> AI -> PAIR -> FD -> PN -> DP. EXTERNAL_HANDOFFS.md remains blob 7d63d434690d00dffce9c90335d41c4f62d85798, with no new entry after October 18. Cofactor-weighted prime-error, root-prime boundary, and all-root versus conditional-first-bad distinctions remain in force.

Queue: Priority A #1145 has no failure needing repair. Priority B DUAL1-DUAL2 has independent ACCEPT_WITH_SCOPE / PAPER_PROOF in 20261118-referee-0413-EST/DP and a named downstream consumer, so it is selected. PAIR1-4 has scoped paper acceptance but no missing implementation required by this work. AI, FD, and new DP claims retain their paper/self-audit scopes; none was silently certified. PN1's H=6 refutation of P<=E is a finite complete-tail counterexample independently reproduced by DP; the H=24 sign remains unresolved. No speculative global-upper wrapper was added.

### D. Selection And Named Necessary Use

The accepted finite theorem removes a head-count loss in the necessary correction-profile test for the prescribed sparse signed Nyman family. It is consumed by DUAL3's restored full-source lower restriction. This meets the explicit Coordinator gate: independent acceptance AND a necessary downstream role must precede implementation. It is not isolated constant optimization. The direct terminal consumer is the paper zero-functional contradiction from one common unbounded exact-head sequence with complete subpower energy; its new arithmetic upper input remains OPEN.

The old #1145 theorem only controls three profiles on its different observation union. The new result is all-finite-n and uses exact paired observations. Existing correction-energy declarations were searched and their actual types inspected; no equivalent all-n theorem was found. No duplicate root status or generated proof obligation was created.

### E. Exact Statement, Quantifiers And Arithmetic Carrier

For natural K>=40 and every natural n (including zero), set N=12K, q_i=4^i*K. For every real sequence t and arbitrary real remainder r on the natural numbers, use

```text
p_q(m) = sum_(6q<d<=8q) floor(m/d) - sum_(10q<d<=12q) floor(m/d),
A_q = {k in Nat : 3q<k<=3q+floor(q/20)},
W = union_(0<=i<n) ({2k:k in A_(q_i)} union {3k:k in A_(q_i)}),
Z(m) = sum_(0<=i<n) t_i*p_(q_i)(m),
E_W(f) = sum_(m in W) f(m)^2 / (m*(m+1)).
```

`nymanDualProfile q m` is DEFINITIONALLY `nymanCorrectionFloor (12*q)` with +1 and -1 on those exact two bands. The proof `profile_source` verifies the band-sum equality. The source's Icc(2,12q), both signs, natural floor division, strict lower/inclusive upper endpoints, weights, and real casts are retained.

Three public declarations in namespace RHLean.Analysis, [source at the tested-candidate revision](https://github.com/OVVO-Financial/RH_Lean/blob/146384fe459bd39a7b3d864e2a5c86a270d05dc8/research/NYMAN_ALL_PROFILE_COERCIVITY.lean):

```lean
nyman_dual_profile_leakage (K m : Nat) (hK : 1 <= K) :
  |nymanDualPair (nymanDualProfile K) m| <= 3 * K

nyman_all_profile_coercivity (K n : Nat) (hK : 40 <= K) (t : Nat -> Real) :
  (21 / 10240000 : Real) * K * (Finset.sum (range n) (fun i => t i ^ 2)) <=
    nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t)

nyman_all_profile_restored_lower (K n : Nat) (hK : 40 <= K)
    (t r : Nat -> Real) :
  (21 / 20480000 : Real) * K * (Finset.sum (range n) (fun i => t i ^ 2)) -
      nymanDualEnergy (nymanDualWindows K n) r <=
    nymanDualEnergy (nymanDualWindows K n) (fun m => nymanDualSum K n t m + r m)
```

The authoritative elaborated types were printed and directly inspected in ExactTypes.lean's hosted output. The first theorem uses `nymanDualPair f k = f(3k)-(3/2)f(2k)`. The all-head constant in N coordinates is 7N/40960000; restored coefficient is 7N/81920000. No assertion is made for K<40. N need not be a square; the genuine DUAL3 instance H=6*2^j, j>=2 gives N=H^2 and K>=48, hence is included. The paper's K_i=N_i/6 is NOT this file's q_i=N_i/12.

### F. Independent Mathematical And No-Circularity Audit

The floor-pair proof establishes -1<=2*floor(3m/d)-3*floor(2m/d)<=2 by Euclidean division, including d=0 under Lean's convention. Equal band cardinalities then give |D p_q|<=3q. On A_q, p_q(2k)=2k-6q and p_q(3k)=2q; consequently D p_q>=9q/5. Every later profile vanishes there. There are at least q/40 samples, the 2k and 3k images within each window are disjoint, and every observed denominator is positive and <=144q^2.

A pointwise quadratic inequality gives a low-energy sample whenever 18720qE<=d^2. Taking c=sqrt(E/(12K)), strong induction recovers |t_i|<=1600c(3/4)^i. The finite geometric square sum gives sum t_i^2<=40960000c^2/7, yielding the asserted lower bound. The proof does not require windows from DIFFERENT scales to be disjoint and does not add copies of their energies: each coefficient is recovered using the same complete finite union energy, followed by a convergent geometric bound.

The full square of Z is used, so every ordered inter-profile cross term is retained. The restored inequality follows from (Z+r)^2>=Z^2/2-r^2 and does not assume favorable cross signs. In particular r=-Z is permitted, and the negative remainder cost prevents false positive domination. The known MR3 negative cross term is therefore not contradicted. No empirical positive-definite Gram, Mobius bound, good-vector premise, desired upper bound, zeta-zero hypothesis, or target-equivalent admissibility occurs in these types. This is independent finite QUANTITATIVE_CONTROL, not a reduction proving its own premise.

### G. Implementation And Validation Design

Six focused new files are in the proof PR: research/NYMAN_ALL_PROFILE_COERCIVITY.lean; scripts/lean/nyman_all_profile/ExactTypes.lean; Audit.lean; check_inventory.py; scripts/nyman_all_profile_regression.py; .github/workflows/nyman-all-profile.yml. No preexisting policy, workflow requirement, root source, arithmetic definition or other author's file was changed.

The new module imports the original flat-taper return and is reachable through the repository research import-closure build and targeted iteration workflow. Native library prerequisites are built; this research-support theorem is not inserted as a terminal RH root assumption. ExactTypes supplies five consumers, including the original accepted constant and literal original correction source. The live audit recursively checks all axioms, traverses original/private declaration dependencies, and requires floor-pair, source transport, sample, future-zero, prefix and geometric-sum proofs. Inventory fails if any of the three public declarations, five exact-type consumers, or three live audit lines is absent. All original repository gates remain enabled.

The NON-Lean exact regression passed 13,342 assertions on K=40,41,59,60 and n=0,...,4, with floor-carry checks, literal source reconstruction, endpoint/sample checks, exact rational shifted-Gram elimination, and omission controls for the second band, observation geometry and restoration. Both Python files passed syntax checks. These finite computations support debugging and are not the universal proof. No local Lean invocation occurred.

### H. Proof Branch, Commits And Review State

Branch: agent/lean-verification/20261118-all-profile-coercivity. Base: main 13b31c6313e274a073d82a01175201185e59e37e. PR: [#1146](https://github.com/OVVO-Financial/RH_Lean/pull/1146), created draft and marked READY_FOR_REVIEW only after all exact-head checks passed at 05:43 EST. Latest certified head: **146384fe459bd39a7b3d864e2a5c86a270d05dc8**. Source blob: **f287e70a500ce5dddf8f0ccf6f2d1da6ecc179ba**. The returned PR snapshot confirms draft=false and merged=false.

Additive commit sequence, without history rewriting:

1. 6709bc28eb0ea7fa6758df337db681a4b938c932: complete proof attempt and validation.
2. 09de408a4f3633107f4cf5ec7b3b07da1d2bf8c5: source unfolding, Euclidean-remainder details, rewrite targeting and elaboration repairs.
3. c90e29dd9d52d54d46bf2b15417222d6963fa18f: pinned interval cardinality API, unnecessary private-hypothesis removal, explicit positive-factor cancellation.
4. 146384fe459bd39a7b3d864e2a5c86a270d05dc8: warning-fatal tactic-sequencing repair.

The public hypotheses, source, observation set and constants were unchanged by every repair. No main write, merge, auto-merge, independent role launch, schedule change or other-role report edit occurred. Human review controls merging.

### I. GitHub Actions Evidence

**13/13 check runs and 12/12 workflows: SUCCESS**, directly fetched for head 146384fe459bd39a7b3d864e2a5c86a270d05dc8. Every workflow reports that exact head; PR base remains the inspected main. The [dedicated proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164/job/134743097073) actually ran pinned warning-fatal compilation: compiled=1, cached=2. Three exact theorem types were printed; all five consumers passed. The live transitive axiom/dependency results are:

```text
nyman_dual_profile_leakage:       [propext, Classical.choice, Quot.sound], closure=428
nyman_all_profile_coercivity:     [propext, Classical.choice, Quot.sound], closure=798
nyman_all_profile_restored_lower: [propext, Classical.choice, Quot.sound], closure=809
PASS: three public statements, five exact types, live dependencies and axioms
```

The audit used actual compiled declarations, not a source-token substitute for axiom inspection. No sorryAx, admitAx, unexpected axiom or hidden target hypothesis was accepted. The inventory and 13,342 exact regression assertions passed. The [targeted iteration job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285606/job/134743101100) independently emitted the new module (compiled=1, cached=2) and then validated cached reuse. The [hosted root job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285825/job/134743096332) ran `lake build RHLean` successfully (9,786 jobs), with its normal warning gate. Action-runtime deprecation notices are distinct from Lean warnings and did not change proof-check policy.

| Workflow at the certified head | Run | Conclusion |
| --- | --- | --- |
| Nyman all-profile coercivity | [44287286164](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164) | SUCCESS |
| Targeted Lean iteration | [44287285606](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285606) | SUCCESS |
| Lean source audits, including hosted root build | [44287285825](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285825) | SUCCESS, both jobs |
| Proof inventory | [44287285587](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285587) | SUCCESS |
| Public export verification | [44287285548](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285548) | SUCCESS |
| Coordinate atlas and static search corpus | [44287285687](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285687) | SUCCESS |
| Prevent new cold-only Lean and OpenAI CI | [44287285537](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285537) | SUCCESS |
| VF pre-914 consolidation | [44287285595](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285595) | SUCCESS |
| VF first-bad normalized infrastructure | [44287285580](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285580) | SUCCESS |
| VF recursive child population and complement capacity | [44287285572](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285572) | SUCCESS |
| VF first-bad source to sector-six inlet | [44287285652](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285652) | SUCCESS |
| VF first-bad final aggregate contraction | [44287285645](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287285645) | SUCCESS |

The [proof evidence artifact](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164/artifacts/14419593567) is 22,375 bytes, ID 14419593567, SHA-256 e77cb5f6efa3c8594eeffb231b6ffa6611751aa038cf06e1b203a8e35a0e104a. Its API metadata independently confirms the certified workflow head. Artifact metadata and direct job logs were inspected; no binary download is claimed.

The reused #1145 [dedicated proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44224055868/job/134532755650) was fetched, not inferred from a report: compiled=1, cached=2, four exact-type checks and three live audits with closure counts 229, 617, 645; only propext, Classical.choice, Quot.sound. Its exact latest head has 13 successful checks. Its proof module blob 24addcf432cc12314d8e71dfc617770f8f303dca is a PR-only source, not main.

### J. Failures, Diagnosis And Repairs

| Tested head | Dedicated workflow / job | Actual finding and response |
| --- | --- | --- |
| 6709bc28eb0ea7fa6758df337db681a4b938c932 | [44285371982 / 134736539874](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44285371982/job/134736539874) | FAILED: source definition not unfolded for sum_congr; nonnegative remainder facts missing in the proof tactic; ambiguous band-zero rewrites; uninferred quotient; beta reduction for image injectivity; order cancellation API; warning-fatal unused argument/sequencing. Focused first repair, no mathematical weakening. |
| 09de408a4f3633107f4cf5ec7b3b07da1d2bf8c5 | [44286140770 / 134739188009](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44286140770/job/134739188009) | FAILED: interval-cardinality simplification did not fire, resulting arithmetic failures and unused-simp errors; private hK unused; cancellation lemma not an iff in this version. Verified pinned Mathlib Nat.card_Ioc, removed unnecessary private premise, used explicit positivity contradiction. |
| c90e29dd9d52d54d46bf2b15417222d6963fa18f | [44286710778 / 134741129785](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44286710778/job/134741129785) | FAILED: only unnecessary gcongr tactic sequencing at line 426. Targeted job 134741130235 independently showed the same diagnostic. Replaced sequencing with ordinary successive tactics; linter stayed enabled. |
| 146384fe459bd39a7b3d864e2a5c86a270d05dc8 | [44287286164 / 134743097073](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164/job/134743097073) | SUCCESS: actual compilation, exact types, live axioms/dependencies, regression and inventory; all 13 PR checks green. |

The failures were proof elaboration/library compatibility/lint failures, not discovered counterexamples to the proposed mathematics. No unproved placeholder was added. Compiler-generated metavariables in failed diagnostic states never constituted accepted proof evidence.

### K. Mathematical Conclusions

The new kernel-certified content is an all-finite-head lower bound on the original finite correction profile energy, its arbitrary-remainder inequality, and the stronger uniform floor-pair leakage bound. This is quantitative information about a necessary component, not an identity promoted to an upper estimate. The result is certified on the PR head, NOT merged main. No complete residual upper bound, new global Mertens exponent, finite amplification constant, all-character conclusion or RH theorem has been obtained. VERIFIED_ETA=NONE; NO_NEW_GLOBAL_GAIN; RH=OPEN.

### L. Formalization-Driven Discoveries

The exact floor carry improves the elementary leakage constant from 5N/12 to N/4. Geometric coefficient recovery then avoids a new operator-norm abstraction and improves the accepted coercivity constant while preserving the original set. The n=0 case needs no additional hypothesis. Positivity of a future scale follows from nonempty sample membership, making a private K>=1 premise unnecessary. These strengthened constants and implementation choices were developed by SELF_AUDIT and are now kernel-certified at the stated head; the separate Referee endorsement applies to the original DUAL1-DUAL2 statement, not retroactively to every strengthening.

### M. Significance And Source-Loss-Recovery-To-Half Capsule

```text
half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1
cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack=CANCELLATION_CHAIN_REUSE_V1
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1
MAIN=13b31c6313e274a073d82a01175201185e59e37e
POLICY=96ad4439ec458af6168f7d9cb3eef5dde291d37c
SOURCE=2d23721027ecc44e85b7add02fc632b482f03352
WATERMARKS=PROFILE -> DUAL,AI,PAIR,FD,PN,DP
ROUTE=NYMAN / ACTIVE_SUPPORT for complete sparse signed residual feasibility
CURRENT_INPUT=native every-positive-loss Mertens baseline; choose a fixed b above it
ORIGINAL=r_mix=sum_i a_i*log(B_i)*r_(B_i), with exact common head H
MOMENTS=sum a_i*log(B_i)=1; sum a_i=0; sum a_i*delta(B_i)=0
LOSS=triangle/magnitude treatment of old profiles propagates a head-count loss;
     dropping R or its cross terms would falsely turn profile cost into full domination
RECOVERY=exact 3k/2k pairing cancels linear drift; Euclidean carry retains both bands;
         all-n lower theorem and arbitrary-R penalty retain required interactions
PRESENT_WORK -> DUAL3 necessary restored complete-source restriction
DIRECT_TERMINAL=one COMMON unbounded exact-head sequence with complete E(H)=H^o(1)
RANGE=finite theorem K>=40,n>=0; actual family H=6*2^j,j>=2,n>=3
ENDPOINT=for each fixed zero rho with Re(rho)>1/2, localized zero functional gives
         E(H)>=c_rho*H^(2Re(rho)-1), contradicting complete subpower energy
SUPREMUM=at actual h=Theta-1/2>0, complete kappa(h)<2h contradicts a sufficiently
         close actual zero; no attained supremum or h-uniform positive gap required
RETURNS=all U_N, F_B, second-band T_i, correction transitions, ordered cross terms,
        after-support output, infinite tail; no unproved sign or n-cost removal
CONSTANT_ORDER=fix b,C and target loss before growing H; expose n dependence
FIRST_OPEN=genuine-coefficient estimate of COMPLETE restored signed residual
FALSIFIER=restored cross term overwhelms profile-only inference; r=-Z is legal;
          PN/DP already refute unqualified P<=E, not the new remainder-bearing theorem
NO_CARRIER_TRANSFER=not actual-prime first-bad NNS, full Euler, or all-character control
MATHEMATICS=independent finite quantitative restriction; complete upper supplier OPEN
```

The nine independent routes VF-LOW, SAT, CODIV, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT and NYMAN remain available with their distinct carriers. This session does not claim new mathematical coverage for each route or force them through Nyman. PAIR and DP prohibit calling cheap repeated pairing a new energy exponent; the present lower bound does not evade that obstruction.

### N. Specialist Handoffs

- **Coordinator / Proof Architect:** retain DUAL1-DUAL2's exact finite scope and consume #1146 only at its verified head. DUAL3 is the named next source restriction; no further head-count/constant optimization is assigned. Preserve #1145 independently until human disposition.
- **Analytic Type II:** for B_i=2^i H use Z=sum a_i*alpha_i*p_i and the COMPLETE R=-1-sum a_i*F_(B_i)+sum a_i*U_(N_i)+sum a_i*(v_i/K_i)*T_i. The formal remainder is arbitrary, so the required arithmetic R estimate is not supplied. PAIR/DP norm equivalence does not pay it. Distinguish paper K_i=N_i/6 from formal q_i=N_i/12.
- **Adversarial Referee:** original DUAL acceptance is acknowledged. Review the stronger -1/2<=floor(3x)-(3/2)floor(2x)<=1 carry route, all-n geometric recovery and 7/40960000 constant on the same W. Hosted verification certifies the exact Lean types; it does not independently endorse the claimed research relevance or prove DUAL3's remaining arithmetic bounds.
- **Owner Payment / Arithmetic Structure:** AI's finite-ancestry and bounded-truncation limits remain paper self-audit items, not a new first-bad supplier. Nothing in this Nyman theorem transfers coefficients, masks or chronology to VF-LOW/SAT/JOH. Require an original-source bridge before reuse there.
- **Finite Wheel & Incidence:** FD's fixed-degree log-divisor zero-mode obstruction remains on its own carrier and status. Preserve strict-history/unit/powerful/cross-product terms in FINITE-AC/CORR4/MU-LIFT. This profile inequality is not finite amplification or centered-wheel cancellation.
- **Prime Census Laboratory:** preserve PN1 and DP's full-tail P<=E counterexample. The registered new checks cover geometric endpoints and omission controls only. Do not extend a routine grid as global evidence; wait for a specific independently derived complete-upper assertion and preregister its smallest falsifier.

### O. First Unresolved Mathematical Theorem

For the prescribed genuine-Mobius sparse-head family with its exact moment constraints, establish one COMMON unbounded sequence H_l of legal heads such that, for EVERY epsilon>0, a constant C_epsilon fixed before l bounds

```text
sum_(m>=1) [sum_i a_i(H_l)*log(B_i)*r_(B_i)(m)]^2/[m(m+1)]
  <= C_epsilon * H_l^epsilon.
```

All source coefficients, exact head, corrections, second bands, mixed terms and infinite tail must be included. Alternatively, at an actual positive zero-supremum gap h, a complete energy exponent kappa(h)<2h with the necessary closed-boundary source hypotheses would supply the terminal contradiction. Neither is proved here. No converse from RH to this prescribed family is asserted; the unrestricted free-coefficient existence criterion is target-equivalent. Merely naming either upper estimate is not new arithmetic.

### P. Resume Capsule

PR #1146 head 146384fe459bd39a7b3d864e2a5c86a270d05dc8; source f287e70a500ce5dddf8f0ccf6f2d1da6ecc179ba; [certified dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164/job/134743097073); 13/13 checks and 12/12 workflows green; REVIEW_READY / UNMERGED. All three public theorems above are PROVED_IN_LEAN at that head; the original DUAL1 constant is a compiled exact-type corollary. No unresolved compiler failure remains. Preserve all three failed revision histories above; do not rerun an unchanged green head.

Refresh main and actual PR state before any further write. Existing #1145 is also green and unmerged, not a repair task. Next substantive mathematics is the complete restored genuine source, not a duplicate coercivity proof or conditional upper wrapper. Report path remains research/agent_reports/2026-11-18/60-lean-verification.md on agent-reports. Execution=COMPLETED_FORMALIZATION_AND_VERIFICATION; full-source research objective=OPEN. Final publication remains READBACK_PENDING until the immutable final commit is retrieved.

## Verified Publication Receipt

The complete A-P synthesis was committed to the authorized report branch at **eac990e374776e023bcae1baeb71e98f4557972d**, report blob **3d9030ade192c103b748866d24c6ee29426bd27c**. The report was fetched at that immutable commit and verified byte-for-byte against all 36,214 characters submitted, preserving the earlier 7,027-character checkpoint history. This receipt supersedes the preparation-only READBACK_PENDING status above.

**EXECUTION=COMPLETED; SUBSTANTIVE_PUBLICATION=VERIFIED; FORMALIZATION=PROVED_IN_LEAN_AT_PR_HEAD; CI=GREEN; PR=REVIEW_READY_UNMERGED; RH=OPEN.** Certified proof head remains 146384fe459bd39a7b3d864e2a5c86a270d05dc8. The source at that immutable head was separately re-fetched and matched blob f287e70a500ce5dddf8f0ccf6f2d1da6ecc179ba and the exact submitted proof bytes. No main write, merge, auto-merge, local Lean, schedule change or agent launch occurred.


## In-Progress Checkpoint - 20261118-lean-1314-EST/PV-AUDIT

Actual scheduled trigger: 2026-11-18 13:14:01 EST / 18:14:01 UTC. PLATFORM_RUN_ID=UNAVAILABLE. This is a new actual invocation, not a revision of the earlier DUAL execution.

Main is 935840aec9b1fcbc66fe4e0164061d661a8ca3b1. Live AGENTS c4f36b772f8a4b0c24fe566b90fafb646073c60f and contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038 are unchanged. BOOTSTRAP_TO_HALF_V1, CROSS_ROUTE_SIGNED_RECOVERY_V1 and LAST_ACTUAL_REPORT_CONTINUITY_V1 were read and acknowledged. Latest-real tree discovery was nontruncated and uncapped. Both days' role files and complete Coordinator mirrors were retrieved; current mirrors agree at ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5. Relevant post-DUAL handoffs are DAMP -> HC -> PV -> PM -> PS -> FC. All roles have current publications. The external inbox remains 7d63d434690d00dffce9c90335d41c4f62d85798, unchanged.

PRs #1145 and #1146 have been human-merged, at 15:13:06Z and 15:13:26Z respectively. There are no open/draft PRs. Exact proof heads retain 13/13 successful checks each; current main has 10/10. Actual dedicated proof logs and main hosted-root log were retrieved. Existing all-profile and three-profile lower bounds and standard-axiom audits are reusable; no repair or unchanged rerun is needed.

Candidate queue: accepted DAMP1-4 are a bounded negative feasibility result without a paid signed inverse; PV1 explicit bound/PV2 repair/PV3 highest-head restriction now have independent ACCEPT_WITH_SCOPE in 20261118-referee-1203-EST/FC. HC, PM, FC's new obstruction, and PS's new numerical certificates retain their actual pending-review scopes. I am independently checking PV's finite complete-covariance repair lemma against original source and the pinned library, and testing whether a useful nonduplicate formal increment meets the current continuation gate. No new theorem, branch or CI certification is yet claimed.

Pinned Lean v4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and PNT+ c39a751132c88b6e8080b74c74023fd95b3d8be0 are unchanged. GitHub Actions remains the sole Lean execution environment. Direct clone returned CONNECT 403; authorized connector source and CI reads succeeded. No local Lean, main write, merge, auto-merge or agent launch occurred.

EXECUTION=IN_PROGRESS; IMPLEMENTATION=NOT_STARTED; MATHEMATICS=INDEPENDENT_CANDIDATE_AUDIT; PUBLICATION=READBACK_PENDING; NO_NEW_GLOBAL_GAIN; RH=OPEN.


## Implementation Checkpoint - 20261118-lean-1314-EST/VR - 18:36 UTC

IN_PROGRESS / NOT_YET_PROVED_IN_LEAN. [Draft PR #1147](https://github.com/OVVO-Financial/RH_Lean/pull/1147) implements five complete proof attempts for the accepted finite PV2 covariance-repair core, on branch `agent/lean-verification/20261118-variance-repair`, based on main `935840aec9b1fcbc66fe4e0164061d661a8ca3b1`. Initial head `67329cc284da431ab0caab406e247ffe1d84adc7` failed hosted proof elaboration/warning checks. Repair `7f000022e281479dd31f6076762fbd0e03629c68` reduced the actual diagnostics to a solved tactic and unused private premise. Both are repaired at current head `e77d049ff83809c13c52e3d90922f34ed032efac`; [dedicated run 44371410914](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410914) and the other exact-head checks are running. Public theorem types are unchanged across repairs. Local exact non-Lean regression again passed all 1,896 assertions. No local Lean execution, endpoint claim, merge, auto-merge or main modification. Final full A-P synthesis and exact-source certification remain PENDING.

---

## Completed Synthesis - 20261118-lean-1314-EST/VR - 2026-11-18 13:42:28 EST

### A. Most Important Formal Mathematical Result

**PROVED_IN_LEAN at unmerged PR head `e77d049ff83809c13c52e3d90922f34ed032efac`: the accepted finite same-support repair inequality for the original two-band Nyman coefficients.** [PR #1147](https://github.com/OVVO-Financial/RH_Lean/pull/1147) now contains five verified theorems, 13/13 successful checks, six exact-type consumers, and live standard-axiom/dependency audits. It is READY_FOR_REVIEW, open and unmerged, after two actual CI repair commits. The principal result is the squared-distance restriction in E; it preserves the complete ordered covariance, all signed repair cross terms and the literal existing coefficient source.

This is a finite quantitative necessary condition, **not** a complete weighted-norm bound, a new global exponent, or RH. Both failed revisions remain documented in J. The initial and implementation checkpoints above are preserved as accurate historical states, superseded by this exact-head certificate.

### B. Current Authoritative Objective And Continuity

Scheduled invocation: 2026-11-18 13:14:01 EST (18:14:01 UTC), America/New_York; RUN_ID_UNAVAILABLE. Authority at intake and implementation baseline: main `935840aec9b1fcbc66fe4e0164061d661a8ca3b1`. Main AGENTS blob `c4f36b772f8a4b0c24fe566b90fafb646073c60f`; CURRENT_PROOF_CONTRACT blob `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; half directive `96ad4439ec458af6168f7d9cb3eef5dde291d37c`; last-actual continuity directive `3e71820a4af722eae7098da6945bb5bcba50dd0d`; cross-route directive `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`.

`half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1`; `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`; `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`; existing complete-HIGH and cancellation-chain acknowledgments are carried forward without claiming a new baseline proof.

Canonical actual-prime `VFCanonicalSquareVonKochStatement` remains OPEN. The terminal VF implication still has its explicit `ClassicalVonKochRHCriterion` argument. The strongest relevant inspected native baseline remains
`native_mertens_near_uniform_window_error_closed : MertensGrowthAtMost (7/8 - 7/(64*nearUniformSlotCount))`,
with the every-positive-loss convention. Its source blob is `f629db1b2b65d6ec042ac9432397d4b6316200c6`. Exact tested #1119 head `77ee815846d6d534c866f0752aa33b84c385610a`: 14/14 checks successful; [closure/axiom job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) re-read. Comparing 2,508 old Lean/pin/script entries to current main found only the root import file changed; this reuses the tested baseline dependency evidence, not a claim that the entire old campaign was rebuilt today.

All roles' latest actual reports were discovered without a calendar cap; today and yesterday are both present, so no TODAY=PENDING substitution is needed. Coordinator mirrors were byte-equal on both dates. Intake report tree `6c947662c9de74873d74b1873ba6c8ca0af58a6c`. The previous own DUAL synthesis was preserved; newly unconsumed sections are DAMP 07:10, HC 08:09, PV 09:09, PM 10:12, PS 11:00, FC 12:03 Eastern. Nov 17 remains YESTERDAY=CARRY_FORWARD at its recorded scopes, not a new certification of every historical claim.

| Role | Nov 17 blob | Nov 18 intake blob |
| --- | --- | --- |
| Coordinator, both mirrors | 125e55aa191083d9c0a982b6dc5a66267e4e4256 | ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5 |
| Owner | 6516bf78b096471ccfd2fb8c215e94002544a594 | 9ee34b6e9daa3cbbac24826f8fc96d65f1fe36ff |
| Analytic | d4bc53ac1b68f6dadabc4a04a2f5fc8c74f6625f | 804f68e0163cbf6836a060a552256d1746d51242 |
| Wheel | 5c26771c0a266d5112e0b4a4b28aba0132e35ef7 | d7c5014b34183b6a377c0438cb6cae27ba35e401 |
| Census | 587b0bb3dd66834a18610ab86174f285f81c4b04 | 5d76c950c517712bbba138d7240d21ac4ccd6b93 |
| Referee | 103ee17307ac799e20bd4ce17d97ff96101a9e5b | 91b57ce6a46693403cd8a5751c63aaf8335ab305 |
| Lean | ee9ed0ace763bf99fea5812490f9541653917938 | c3ded05265d7ac5e065e4a4e645e2e96069ca8fa |

External handoff blob `7d63d434690d00dffce9c90335d41c4f62d85798` is unchanged, with no entry after October 18; its existing source-restoration warnings are carried forward, not presented as new acceptance.

### C. Formalization Queue

Priority A: no open proof PR at intake. Relevant #1145 and #1146 had already been human-merged, so their earlier report labels OPEN were stale. Both tested heads had 13/13 successful checks: #1145 `43cbf9310516f26a440b5527ce6dc22a62856248`, #1146 `146384fe459bd39a7b3d864e2a5c86a270d05dc8`. Relevant [#1145 audit job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44224055868/job/134532755650), [#1146 audit job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44287286164/job/134743097073), and [current main build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44333123355/job/134902562807) were inspected. Main had 10/10 successful checks; its root build completed 9,786 jobs. This does not certify the new PR.

Priority B/C: implement only the accepted finite core of `20261118-analytic-0909-EST/PV2`, independently accepted with scope by `20261118-referee-1203-EST/FC`. PV1's squarefree-density threshold and PV3's highest-dyadic restriction remain paper results, not this implementation. The historical mechanism is `20261106-coordinator-1513/NS1`, accepted by `20261106-referee-12`; original reports were recovered at blobs `8812a90540fb511279b5f4ce08e108ef717d5ef1` and `da3265467c799e9d21832ab25245617ba3b15a54`. Jordan diagonalization and singleton positivity are inherited mathematics, not new discoveries credited here.

Parked: DAMP1-4 now have FC scoped paper acceptance, but unsigned inverse costs and target-equivalent signed-prefix control do not provide a new upper supplier. HC's compressed historical payment, PM's routed top-prime capacity, PS's new finite sign certificates, and FC's self-authored growing-cell extension retain their distinct stated review states. No new unconditional arithmetic theorem is inferred from those reports. No duplicate, conditional-small-norm wrapper or speculative endpoint PR was opened.

### D. Candidate Selection And Continuation Capsule

ROUTE=NYMAN; MODE=BOUNDED_FEASIBILITY_AUDIT / NECESSARY_REPAIR_LEMMA, not a newly admitted half-bootstrap. The original complete residual has genuine Mobius signs, the two correction bands, reciprocal and total moments for its intended exact-head family, all output locations, and the infinite weighted tail. The attempted shortcut was to reduce the complete period covariance cheaply while keeping the same final coefficient support. The finite inequality below is the necessary arithmetic restriction on such a repair, not a period-average substitute for the complete energy.

START=the reused native baseline and accepted exact-head/remote-tail infrastructure. PROPOSED_ADVANCE=certify the accepted squared-distance restriction that every same-support variance repair must satisfy. DIRECT_TERMINAL=the existing independently reviewed PAPER Mellin consumer: one common unbounded legal exact-head sequence with complete weighted energy E(H)=O_epsilon(H^epsilon) for every epsilon>0 excludes each fixed nontrivial zero with real part >1/2. This terminal and the period-average interpretation are NOT newly Lean-certified here. FIRST_OPEN=an independent upper estimate for the complete genuine signed residual. RENEWAL=none supplied. All middle, correction, after-support and infinite-tail returns remain mandatory. The new lemma is useful to the bounded feasibility test; it does not pay that open input.

### E. Exact Theorems

All functions below have real values; all finite cutoffs and indices are natural numbers. The actual source definition is

~~~text
J2(n) = n^2 product_(p in n.primeFactors) (1 - 1/p^2), n != 0;
J2(0) = 0.
V_N(a) = (1/12) sum_(2<=k<=N) sum_(2<=l<=N)
              (a(k)/k)(a(l)/l)(gcd(k,l)^2 - 1).
~~~

New formalization IDs have prefix `20261118-lean-1314-EST`:

| ID | Public declaration in RHLean.Analysis | Exact scope |
| --- | --- | --- |
| VR1 | nyman_jordan_two_divisor_sum | For every n, sum_(d divides n) J2(d)=n^2, including n=0 with Lean's empty zero-divisor set. |
| VR2 | nyman_jordan_two_lower | For every n, n^2/2 <= J2(n). |
| VR3 | nyman_covariance_divisor_squares | For every N and a, 12 V_N(a)=sum_(2<=d<=N) J2(d) (sum_(2<=k<=N, d divides k) a(k)/k)^2. |
| VR4 | nyman_covariance_singleton_lower | For every N,a and finite s subset [2,N] with N<2q for each q in s, sum_s a(q)^2 <= 24 V_N(a). |
| VR5 | nyman_flat_same_support_repair | For every K>=1, H>=1, H<=4K, A,Z in R and e:Nat->R, the gap squared-distance inequality below. |

Set N=6K, L=nymanFlatScale(N,H)=log(N)-log(H)=log(N/H) under these positive inputs, and
h(j)=A on (3K,4K], Z on (5K,6K], zero elsewhere.
Use the existing literal `nymanFlatCoefficient N H h`, not a parallel arithmetic model. Then

~~~text
sum_(4K<q<=5K) (e(q) - mu(q) log(6K/q)/L)^2
  <= 24 V_(6K)(fun k => nymanFlatCoefficient (6K) H h k + e(k)).
~~~

No moment, cancellation, small-energy or RH hypothesis is assumed. The covariance definition truncates every coefficient to [2,N]; arbitrary values of e outside that interval are irrelevant. Therefore this is a same-final-support result, not a license to enlarge the support and keep the old singleton band. When support is enlarged, the final cutoff and singleton condition must be recomputed.

### F. Independent Mathematical And No-Circularity Audit

VR1 follows from multiplicativity and the prime-power telescope
J2(p^(i+1))=p^(2(i+1))-p^(2i). VR2 uses the exact finite product
product_(k=2..n)(1-1/k^2)=(n+1)/(2n)>=1/2;
removing nonprime factors only increases that positive product. No zeta lower estimate or unproved density hypothesis enters.

For VR3, sum_(d divides gcd(k,l),d>=2)J2(d)=gcd(k,l)^2-1. Finite Fubini gives the full divisor squares. Both ordered off-diagonal orientations remain present; coefficients are grouped before squaring. For VR4, 2q>N means q has exactly one multiple in the final support. Thus its coordinate contributes at least a(q)^2/2 to 12V, and every unselected Jordan coordinate is nonnegative. VR5 uses the exact zero of both correction bands on (4K,5K] and `nymanFlatKernel_eq_original`, yielding c(q)=-mu(q)log(N/q)/L there.

This is not an assumption of its own conclusion and is not target-equivalent. It uses no baseline exponent, full-response upper bound or unjustified cross-sign. It proves a finite lower restriction on a complete centered quadratic kernel, not an upper bound on E. The equality between that kernel and an actual complete-period average is accepted paper background but is not proved in this module; no short physical-window transfer is asserted.

Source -> loss -> recovery -> consumer: period averaging loses location relative to the actual 1/[m(m+1)] weight; Jordan coordinates retain all averaged cross terms; singleton coordinates restrict repairs; neither restores the lost physical location. No map to the actual-prime VF discrepancy, Euler square-root clock, or OAI ideal characters is supplied. The already-merged #1145/#1146 coercivity results remain separate verified restrictions, not an upper supplier recovered by relabeling.

### G. Implementation And Validation Design

Six focused new files: `research/NYMAN_VARIANCE_REPAIR.lean`; exact-type, live-axiom/dependency and inventory checks under `scripts/lean/nyman_variance_repair/`; `scripts/nyman_variance_repair_regression.py`; and the dedicated `.github/workflows/nyman-variance-repair.yml`. Existing gates, pins and root imports were not weakened or edited. The existing research import-closure action makes the module reachable for hosted compilation; no duplicate root abstraction was created.

Imported original source: `research/NYMAN_FLAT_TAPER_RETURN_20261104.lean`, blob `2d23721027ecc44e85b7add02fc632b482f03352`; its dependency `NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean`, blob `2da630c1d5fb9302e2097ec1e170cf41c2b40609`. Library and PR searches found no existing implementation of this finite repair result. Pinned Mathlib arithmetic-function and finite-product APIs were read before coding.

Toolchain: Lean 4.34.1, lean-toolchain blob `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PNT `c39a751132c88b6e8080b74c74023fd95b3d8be0`; lakefile blob `6ef95e9ebf184d5846fee88a9cdf2db3a38afc97`; manifest blob `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`. Lean was executed ONLY in GitHub Actions, never locally.

Finite regression: 1,896 exact rational assertions passed locally and in hosted CI. Registered domain: primitive-residue-pair counts for Jordan n=1..256, divisor sums/products/half bounds/telescopes; N=0..24 with four signed rational vectors; K=1..8 with three rational repairs. Controls detect support extension, deleted signed cross terms and the omitted centering subtraction. The repair fixtures use rational gap coefficients, not numerical logarithms or a claim to test the original logarithmic family exhaustively. Exact original logarithmic coefficients are covered by the formal theorem. These finite checks are regression evidence, not a proof of an asymptotic Nyman estimate.

Six exact-type consumers include the literal ordered gcd kernel. The live audit checks all five public theorem axiom sets and verifies the original Jordan source and, for the consumer, the full-square decomposition, lower bound, divisor identity, original flat coefficient/kernel bridge and Mobius symbol. No holes, new axioms or added target-strength premises are permitted.

### H. Proof Branch And PR Evidence

Branch: `agent/lean-verification/20261118-variance-repair`. Base main: `935840aec9b1fcbc66fe4e0164061d661a8ca3b1`. [PR #1147](https://github.com/OVVO-Financial/RH_Lean/pull/1147) was opened as a draft and marked ready only after exact-head proof and audit success. Its source head is `e77d049ff83809c13c52e3d90922f34ed032efac`, source tree `39f5005419e119bb7f23df25b086a38dff4cd1fb`, and [proof module](https://github.com/OVVO-Financial/RH_Lean/blob/e77d049ff83809c13c52e3d90922f34ed032efac/research/NYMAN_VARIANCE_REPAIR.lean) blob `92608fc013c26102ac12250558a850209028e6d8`. Immutable source readback exactly matches the locally edited file.

Three focused commits: initial `67329cc284da431ab0caab406e247ffe1d84adc7`; elaboration repair `7f000022e281479dd31f6076762fbd0e03629c68`; final warning cleanup `e77d049ff83809c13c52e3d90922f34ed032efac`. Six added files only. No source/contract/policy on main was changed. Human merge remains required; no merge or auto-merge was performed. Main was freshly checked and remains the baseline SHA above.

### I. GitHub Actions Evidence

The [dedicated exact-head job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410914/job/135038879279) explicitly checked out `e77d049ff83809c13c52e3d90922f34ed032efac`, printed Lean 4.34.1 (compiler commit 5045d0056413266e57c625dcd7c365b10e377c52), completed the 8,956-job prerequisite build, compiled one new research module with two cached dependencies, and ran all six exact-type consumers with warnings fatal. The exact elaborated types were read from the actual log and match E, including no extra bound/moment hypothesis.

All five live axiom outputs are exactly `[propext, Classical.choice, Quot.sound]`. Project-dependency traversal counts, in VR1..VR5 order: 381, 483, 526, 698, 741. All original-source guards passed. The fail-closed inventory reported five public statements, six exact types, live dependencies and axioms. The 1,896 exact rational regressions passed in the same job.

The [targeted integration job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410464/job/135038878048) independently compiled the research closure (`compiled=1 cached=2`) and verified artifact reuse (`compiled=0 cached=3`). The [hosted root build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371411188/job/135038881017) completed 9,786 jobs. These repository-wide integration jobs used GitHub's synthetic merge `b0fd094746ffd839af282bb644b0b40b127db264` of the exact PR head into the unchanged base; they are not misreported as raw-head checkouts. The dedicated mathematical job above did use the raw PR head.

All 13 checks attached to the current head were completed successfully:

| Workflow / job | Actual job URL | Result |
| --- | --- | --- |
| Coordinate atlas and static search corpus | [135038886486](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371412128/job/135038886486) | success |
| Lean source audits / Hosted Lean build | [135038881017](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371411188/job/135038881017) | success |
| Lean source audits / audit | [135038880285](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371411188/job/135038880285) | success |
| Public export verification | [135038879675](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410545/job/135038879675) | success |
| VF pre-914 consolidation | [135038879335](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410885/job/135038879335) | success |
| Nyman complete covariance repair | [135038879279](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410914/job/135038879279) | success |
| VF first-bad source to sector-six inlet | [135038878706](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410549/job/135038878706) | success |
| VF first-bad final aggregate contraction | [135038878528](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410553/job/135038878528) | success |
| Targeted Lean iteration | [135038878048](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410464/job/135038878048) | success |
| VF first-bad normalized infrastructure | [135038878024](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410575/job/135038878024) | success |
| Proof inventory | [135038877999](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410377/job/135038877999) | success |
| Prevent new cold-only Lean and OpenAI CI | [135038877530](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410598/job/135038877530) | success |
| VF recursive child population and complement capacity | [135038877133](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44371410415/job/135038877133) | success |

### J. Actual CI Failures And Repairs

1. At initial head `67329cc284da431ab0caab406e247ffe1d84adc7`, [run 44369768596 / job 135033053822](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44369768596/job/135033053822) failed. A broad power rewrite hit the wrong occurrence; unrestricted simplification of the zeta application unfolded it into a divisor-antidiagonal sum; a nonzero-gcd conjunct remained explicit; and warning-fatal checks found unnecessary sequencing/unreachable tactics. The repair normalized exponent forms explicitly, rewrote zeta before simplification, handled the divisor-set conjunction directly and removed redundant sequencing. No public theorem type was changed.
2. At `7f000022e281479dd31f6076762fbd0e03629c68`, [targeted job 135035886850](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44370564545/job/135035886850) reported only `No goals to be solved` after a successful field simplification and an unused `hl` private-kernel premise. The final commit deleted the now-unreachable tactic and the genuinely unnecessary private premise, adjusting its call. No linter or CI gate was disabled.
3. The final exact-head and integration jobs in I pass. No unresolved Lean error or formal-audit failure remains. The finite Python fixture's earlier `math.prod` start-keyword error was fixed before its initial successful pass, without changing the registered domain. These are engineering repairs, not evidence that the mathematical statements were false.

### K. Mathematical Conclusions

VR1 and VR3 provide STRUCTURAL_CONTROL; VR2 and VR4 provide independent QUANTITATIVE_CONTROL on the exact finite Jordan/covariance objects; VR5 is a QUANTITATIVE_NECESSARY_REPAIR_RESTRICTION on the original two-band coefficient, supporting the accepted PV2 obstruction program. Formal soundness and endpoint significance are assessed separately. No all-scale squarefree-density theorem, full PV1/PV3 theorem, complete-period interpretation, actual weighted norm upper bound, prime estimate or RH result is claimed.

`NEW_VERIFIED_ENDPOINT_GAIN=NONE`; `VERIFIED_ETA=NONE`; `NEW_ACCEPTED_RH_ROUTE=NONE`; canonical objective and complete signed upper supplier remain OPEN. The prior near-uniform baseline is unchanged.

### L. Formalization-Driven Discoveries

The finite repair inequality does not require either moment condition: they are needed for the intended exact-head analytic family, not for this necessary finite covariance restriction. Its literal correction-band argument works for 1<=H<=4K, a broader domain than the paper family's H<3K. This is an explicit justified generalization, not a hidden weakening. The proof also permits every real coefficient vector and every finite upper-half subset in VR4, eliminating irrelevant assumptions about the other coefficients.

The final-support qualification is essential. A coefficient at 2q can cancel q's divisor coordinate after the cutoff is enlarged; the old singleton formula then fails. The finite regression retains this as a negative control. The first CI failures were algebraic elaboration and warning-fatal script issues, not counterexamples to the statements; no new mathematical hypothesis was introduced to repair them.

### M. Mathematical Significance

The substantive consumer is the gap squared-distance bound for arbitrary same-support repairs, not another restatement of a target norm. It certifies why large changes on an untouched genuine Mobius band cannot be avoided by cancellation elsewhere in the same finite covariance. The Jordan and singleton mechanisms are inherited from NS; their formal implementation is justified here by this accepted original-coefficient consumer. No claim of literature novelty is made.

The lemma does not show that the complete weighted Nyman energy is large: that would confuse a period statistic with a location-weighted norm. Conversely, small variance alone is only one proposed sufficient tail method, not a necessary condition for every successful Nyman approximant. All nine independent route toolkits remain available. No investigator portfolio, saved prompt, schedule or permission was changed.

### N. Specialist Handoffs

- Research Coordinator / Proof Architect: record the exact tested PR status in H/I, retain inherited NS attribution, and use VR5 only as a finite necessary repair constraint within the bounded feasibility audit. Do not promote it to a half-continuation or endpoint gain.
- Owner Payment: the theorem does not transfer to first-owner chronology or compressed strict-history payment. HC's restored positive J terms and original occurrence multiplicities remain separate; no prime-arrival theorem is certified by this covariance.
- Analytic Type II: the accepted PV2 finite squared-distance core is implemented, with moments removed from this local statement and H<=4K allowed. The squarefree-density, support/mass/correlation asymptotics, PV3, period-average identity and complete upper return remain outside this PR. The new full-support theorem must be used before any proposed support enlargement.
- Finite Wheel & Incidence: PM's Euler routing/capacity question has no supplied bridge to this linear residue kernel. Keep both ordered orientations and final support explicit in any attempted transport; no new assignment or agent launch is implied.
- Prime Census Laboratory: reuse the 1,896 exact regression assertions and their omission controls. Do not extend ranges merely to fit an exponent. A useful new discriminator must test a specific complete-source signed upper mechanism, retaining physical weights and the full tail. PS's finite signs retain their own review status.
- Adversarial Referee: audit PR #1147's exact types and the distinction between V and E; compare the broadened H domain and absent moment hypotheses against the local proof, not the analytic family's separate constraints. The new growing-cell FC statements remain self-authored paper work pending independent review, not automatically certified here.

### O. First Unresolved Mathematical Theorem

For one common unbounded legal exact-head sequence, independently prove
`forall epsilon>0, exists C_epsilon, forall sufficiently large heads H in that sequence, E(H)<=C_epsilon H^epsilon`,
where E is the COMPLETE original weighted squared residual, with genuine Mobius coefficients, both corrections, all middle/after-support locations and the infinite tail. A corresponding complete finite-output estimate is available as a paper localization only after using the already-paid remote-tail bound at its exact legal cutoff. Neither small V, a favorable cross sign, moments alone nor a target-equivalent renamed premise establishes this input.

On the formal side, the period-average interpretation of the complete gcd kernel and the separate paper Mellin endpoint consumer are not claimed proved by this PR. They should be implemented only when a concrete accepted continuation needs them; they are not substitutes for the missing arithmetic upper estimate.

### P. Next-Run Resume Capsule And Publication

```text
TRIGGER=2026-11-18T18:14:01Z; role=Lean Verification; RUN_ID_UNAVAILABLE
AUTHORITY_MAIN=935840aec9b1fcbc66fe4e0164061d661a8ca3b1
HALF_ACK=BOOTSTRAP_TO_HALF_V1; ROUTE=NYMAN bounded feasibility
CLAIM=20261118-analytic-0909-EST/PV2 finite core
REVIEW=20261118-referee-1203-EST/FC ACCEPT_WITH_SCOPE
FORMAL_IDS=20261118-lean-1314-EST/VR1..VR5
PR=1147; STATE=OPEN / READY_FOR_REVIEW / UNMERGED
HEAD=e77d049ff83809c13c52e3d90922f34ed032efac
SOURCE_BLOB=92608fc013c26102ac12250558a850209028e6d8
RAW_HEAD_RUN=44371410914; JOB=135038879279; SUCCESS
ALL_CHECKS=13/13 successful; STANDARD_AXIOMS_ONLY
EXACT_TYPES=6; PUBLIC_THEOREMS=5; RATIONAL_REGRESSION=1896 PASS
FAILED_PRIOR_HEADS=67329cc284da431ab0caab406e247ffe1d84adc7,
  7f000022e281479dd31f6076762fbd0e03629c68; both superseded by repaired head
FIRST_OPEN=independent complete signed weighted-energy upper estimate
ENDPOINT_GAIN=NONE; RH=OPEN; NO_NEW_HALF_BOOTSTRAP
```

Publication history: the early checkpoint was committed at `2b6b2e11a6d64d0e9cab2d2bd75135e6013658b3`, blob `d0799e0cc4474e80f130308915a591787f6c4576`, with exact immutable readback. The implementation checkpoint was committed at `0b98276edd5b623ef044b9c0c667eaa11fec6d38`, blob `79e8769ccc7bd7b6657bcfd2306caa978834138e`, also read back exactly. A final report-tree refresh found no newly changed upstream Nov 17/18 role blobs. This synthesis preserves all preceding own-report text; publication is certified only by the subsequent immutable readback receipt.

At the next actual invocation, refresh main and PR #1147 first. Reuse this exact green evidence if source and relevant dependencies are unchanged; do not make a no-op CI commit. Repair any genuinely new failure before starting a duplicate. If human-merged, record the merge separately from this tested head. Seek a newly accepted necessary step for a qualifying continuation, not another equivalent finite kernel lemma or a conditional small-E wrapper. No other agent was launched and no schedule, saved prompt, security requirement or tool grant was altered.


### Verified Publication Receipt - 2026-11-18 13:44:03 EST

The complete VR synthesis was published at [commit 37f7fcdb18cd87747034f962f54d9dac13e103b1](https://github.com/OVVO-Financial/RH_Lean/commit/37f7fcdb18cd87747034f962f54d9dac13e103b1), report blob `06c4181ef77b362a7f65ca510bd0ff1431d48994`. Immutable readback matched all 68,190 characters exactly, including preserved earlier history and all sixteen A-P sections. Publication status: PUBLISHED / READBACK_VERIFIED.

Final PR refresh: #1147 OPEN, draft=false, merged=false, head `e77d049ff83809c13c52e3d90922f34ed032efac`; all 13 current checks success. PR verification metadata now links the exact hosted proof/integration evidence and the immutable synthesis. No source changed after successful CI or review-readiness transition.

Stable newest-handoff prefixes retained for future backfill: `20261118-coordinator-0710-EST/DAMP`; `20261118-owner-0809-EST/HC`; `20261118-analytic-0909-EST/PV`; `20261118-wheel-1012-EST/PM`; `20261118-census-1100-EST/PS`; `20261118-referee-1203-EST/FC`. Their source blobs and separate acceptance scopes are in B/C. This receipt does not change any mathematical classification: the five finite theorems are certified at the PR head, while the complete weighted upper estimate and RH remain OPEN.
