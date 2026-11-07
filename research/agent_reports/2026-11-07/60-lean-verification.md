# RH | Lean Verification - 2026-11-07

## Early Checkpoint - Scheduled 05:10 EST Invocation

Actual trigger: 2026-11-07T05:10:01-05:00, America/New_York.
RUN_ID_UNAVAILABLE; run label 20261107-lean-1.
Reporting: IN_PROGRESS / PARTIAL. New mathematical and implementation results PENDING.

Main is 1c057c1d65b6d4cb4d59d207f69a815c52353314.
AGENTS blob: 48b2a58ab5fcd402321a4dace511c7d54bf688a1.
CURRENT_PROOF_CONTRACT blob: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; policy blob 13d58dd12d90fbf1160812c7c93442dc5d0576ac.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1; policy blob ffd8f1c65cc4da656174956d4e03b48bea46768b.
These acknowledge current authority; substantive proof progress is not yet claimed.

The canonical actual-prime VF von Koch estimate remains OPEN. Existing native 7/8 and strict-slot results are established inputs, not new discoveries.
eta_gate=SEARCH_BROAD; net_endpoint_gain=UNKNOWN.

Open PR discovery returns only #1101, an unmerged instruction proposal. No open proof PR is available for repair. Main includes the human merge of #1100; its exact-head proof logs will be checked, not inferred from its title.

Intake retrieved today's Owner SG, Analytic GL, Wheel DI, Census SC, and Referee GL/NC/PF reports, and all seven roles' November 6 reports. Coordinator TODAY=PENDING, YESTERDAY=CARRY_FORWARD (00/90 blob 8812a90540fb511279b5f4ce08e108ef717d5ef1). Own previous report blob b8bfe3ce9c20d7903395364efb39bcec974c8a2f. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no November entry; old routing is superseded, source cautions remain valid.

Candidate selection is in progress. Today's independently accepted CODIV GL1-GL4 is a promising source-exact candidate; compare its quantitative tail bound and essential coprimality masks with existing declarations before branching. GL3's support lower bound is not signed cancellation. Referee's new NC/PF extensions remain separately review-pending. Other route candidates and yesterday's accepted work remain eligible.

Lean/Mathlib pins retrieved: leanprover/lean4:v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. All Lean execution will be through proof-PR GitHub Actions only. No local Lean, no direct main writes, no merges, no agent launches. Ordinary network cloning returned CONNECT 403; connected GitHub reads work, so this is not yet a proof-write blocker.

Next: finish the focused candidate/dependency audit, implement a complete qualified theorem if ready, inspect actual CI, and append a full A-P synthesis preserving this checkpoint.

## Implementation Milestone - Same Scheduled Invocation

[Draft PR #1102](https://github.com/OVVO-Financial/RH_Lean/pull/1102) is open on agent/lean-verification/20261107-codiv-large-gcd. Base 1c057c1d65b6d4cb4d59d207f69a815c52353314; initial head 3ccef8f0a095268a322be71403cb9c909605181b. Connected branch/blob/tree/commit/ref/PR writes succeeded; BLOCKED_WRITE_ACCESS does not apply.

Selected accepted claim: 20261107-analytic-1/GL2, independent acceptance 20261107-referee-1. The complete Lean proof attempt bounds the original absolute covariance by its genuine squared-Mobius support, then by 4 X h^2/(G-1) and 8 X h^2/G. The canonical-gcd injection retains every physical pair; the later overcount is explicitly nonnegative. A proof-driven extension removes h<=X: 1<=X and 2<=G<=h suffice. That extension is SELF_AUDIT, not a fabricated Referee verdict.

Actual exact integer/rational regression passed 4896 original/lattice cases, including 1785 with h>X and 544 empty-cutoff cases, plus six declared fixtures. Both covariance signs occur (16 at X=225,h=6,G=5; -16 at X=1764,h=12,G=9); n+d is not clipped at 4X. These are finite checks, not kernel certificates.

The dedicated CODIV and targeted Lean workflows have started on this exact head. Current state DRAFT_PR / CI_PENDING; no PROVED_IN_LEAN claim yet. Five public types and all their transitive axioms are explicitly audited. Existing root/inventory/export checks remain enabled. No GL3 lower bound or open GL4 signed supplier is assumed or claimed.

Prior #1100 was directly confirmed merged; its dedicated job 128270266477 in run 42328802826 is successful. Retrieved logs show the exact synthetic-merge checkout and eleven standard-axiom lists. Tested source blob c5ebb3d5d96898549ad039fd32e1a26955c5b8f8 equals current main. This reuses prior evidence, not a fresh build of today's entire main.

## CI Diagnosis And Repair Checkpoint - Same Invocation

Initial head 3ccef8f0a095268a322be71403cb9c909605181b failed dedicated run 42363415534 / job 128376323672. Actual logs exposed ASCII pair-type notation parsed as multiplication of types, explicit reciprocal denominator/normalization obligations, and two positivity tactic failures. These were proof-script/elaboration issues; no mathematical premise was strengthened.

Repair head d551268cc0c74b2f5ed49a88fd81b87cd81c3e63 failed dedicated run 42363634625 / job 128376980950 on an unnecessary tactic after a solved field calculation and an unsuccessful source-equality simplification. The four quantitative/support declarations printed only the permitted standard axioms, but the full warning-fatal file failed and the source-equality declaration had compiler error-recovery sorryAx. This revision is NOT accepted as a completed Lean result.

Current repaired head aa401fb98b888fe94a99d719ac8366e67831c9ca, source blob 62ec0fc04fa722672746d9b3ff65826ea0c3ae58, makes the product-sum rewrite explicit and removes the solved-goal tactic. The five public theorem statements, hypotheses, coefficients, normalizers and all checks are unchanged across repairs. No authored proof hole or new axiom was introduced. Current state remains DRAFT_PR / CI_PENDING until the complete latest-head audit succeeds.


## Final Research Synthesis - 20261107-lean-1

This is the continuation of the scheduled 05:10 EST invocation, not a new launch.
The earlier checkpoints and failed revisions above remain part of the record.
Final mathematical certification and publication receipt are recorded below.

### A. Strongest Actual Result

Selected claim **20261107-analytic-1/GL2** now has a complete implementation in
[PR #1102](https://github.com/OVVO-Financial/RH_Lean/pull/1102).
Current certification: **PROVED_IN_LEAN_AT_PR_HEAD / REVIEW_READY / UNMERGED**.
Own stable implementation ID: **20261107-lean-1/GL2-TAIL**.

For genuine Moebius values, all natural X,h,G with 1<=X and 2<=G<=h,

```text
T_ge = 2 sum_(1<=d<h) (h-d)
           sum_(X<=n<4X, gcd(n,d)>=G) mu(n)mu(n+d),
W_ge = 2 sum_(1<=d<h) (h-d)
           sum_(X<=n<4X, gcd(n,d)>=G) mu(n)^2 mu(n+d)^2,

|T_ge| <= W_ge <= 4 X h^2/(G-1) <= 8 X h^2/G.
```

The original second integer n+d is never clipped at 4X. The implementation
removes the paper assumption h<=X and obtains the stronger intermediate
denominator G-1. This extension has an explicit independent derivation below;
it is author SELF_AUDIT, not a fabricated additional Referee acceptance.
The name `le_sharp` means stronger than the constant-eight corollary here,
not a claim that its constant is optimal.

Classification: **QUANTITATIVE_CONTROL / INDEPENDENT_COMPONENT_ADVANCE**.
This pays a proper interaction sector. It supplies no favorable covariance
sign, full small-gcd bound, new endpoint exponent, or canonical VF theorem.
`eta_gate=SEARCH_BROAD`; `NEW_VERIFIED_ENDPOINT_GAIN=NONE`.
Existing strict-gap results remain established at their actual scopes.

### B. Live Authority And Objective

Main baseline and refreshed main: `1c057c1d65b6d4cb4d59d207f69a815c52353314`.
AGENTS blob `48b2a58ab5fcd402321a4dace511c7d54bf688a1`;
CURRENT_PROOF_CONTRACT blob `7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c`.
The live authority, selector, broad-search, complete-return, research-engine,
role instructions and dynamic protocol were retrieved and read.

`baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`, policy blob
`13d58dd12d90fbf1160812c7c93442dc5d0576ac`.
`deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`, policy blob
`ffd8f1c65cc4da656174956d4e03b48bea46768b`.
Actual implementation of the independent large-gcd estimate, not this policy
acknowledgment, is the substantive arithmetic step.

The canonical actual-prime VF von Koch statement remains OPEN:
there exists C>=0 such that for every natural R>=2,
`|pi(R^2)-vfCanonical(R^2)| <= C R log R`.
The inspected terminal `riemannHypothesis_of_vfCanonicalSquare` explicitly
requires both `ClassicalVonKochRHCriterion` and the unproved arithmetic
statement. Neither is replaced by a hypothesis with a more convenient name.
The fixed canonical phase and actual-prime carrier are unchanged.

The native all-prefix 7/8 replay and strict-slot improvement are established
inputs. Optional sharper maximal-shell energy is a different sufficient
CODIV route, not an absent premise of that completed replay or a universal
assignment. Unmerged instruction proposal #1101 was not treated as authority.

### C. Continuity And Formalization Queue

Both America/New_York calendar days, November 7 and November 6, were read.
All available role reports were retrieved; relevant accepted claims,
derivations, rejections, open work and handoffs were consumed. This does not
claim independent reproduction of every experiment embedded in those reports.

| Role | November 7 source and status | November 6 carry-forward source |
| --- | --- | --- |
| Coordinator | TODAY=PENDING, confirmed again at closeout; YESTERDAY=CARRY_FORWARD | 00/90 identical blob `8812a90540fb511279b5f4ce08e108ef717d5ef1`; accepted NS spectral work and newer review-pending CS shift coherence |
| Owner | `1006bb9f0c61a22ceeb7fab25d177a40dc24f25e`; SG1-SG5 genuine SAT cofactor sector, review pending | `1856a96aaaa9d86a5ee2d59ffe50ced936443fa6`; BT/RZ, DR, MS packets |
| Analytic | `6712040159ca37ef3257cf507ec8198fd26fbb91`; GL1-GL4 accepted with scope by today's Referee | `7997620b6ab7eb0701296994734ee910df3c3ba1`; FP CODIV, accepted RM Nyman, review-pending AQ OAI |
| Wheel | `b943f16b0fedbcefa53545f8a7c77482e688399e`; DI1-DI5 CORR4 restrictions, review pending | `3099558194a00358962ff1844bf283e625b9283d`; accepted CP, newer PB/GF |
| Census | `c9d78787ca4fca22f89bc9bcaf886e5ae74deda2`; SC1-SC5 label-capacity overuse/corrected transport, review pending | `c34ac074296e8b2e5b20dee3a2ce02518571206c`; FW radical increment, spectral-cross counterexample, earlier HC/GM |
| Referee | `787a9030cc6d6f8f63fa89cd3a99d7cf54e25ea5`; GL acceptance; new NC/PF SELF_AUDIT only | `da3265467c799e9d21832ab25245617ba3b15a54`; CP/RM/NS/FW3 decisions, newer jump-energy obstruction |
| Lean | This report, retaining all earlier checkpoints | `b8bfe3ce9c20d7903395364efb39bcec974c8a2f`; #1100 awaiting human merge then |

External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry
after October 18. Original-source/complete-return qualifications are retained;
old task routing is superseded. No external handoff bypassed review.

Queue and duplication decision:

1. Priority A: no active open proof PR existed at intake. #1101 is a policy
   proposal, not a broken proof. Prior #1100 is now human-merged; its evidence
   is reused below, not repaired or reimplemented.
2. Priority B selected: independently accepted GL2, a ready quantitative
   proper-sector estimate on the genuine arithmetic carrier. Search of the
   current declarations, proof surfaces, source notes and open PRs found no
   existing declaration of this exact short-additive-lag bound.
3. Further qualified candidates: GL3's effective actual-support lower bound
   and accepted NS/RM/CP supporting work remain eligible. They are not claimed
   to have been formalized by this PR.
4. New SG/DI/SC, NC/PF and CS packets retain their actual review-pending status.
   They were not promoted solely because they appeared in a report.

The October 19 long-shell-lag note already contains large-gcd counting and
common-factor sign stripping. This PR is a source-exact formalization and
strengthening of the accepted short-lag result, not a priority claim for the
general counting technique or a new version of the completed 7/8 proof.

### D. Independent Proof Plan And Derivation

Target: absolute original covariance bounded by its exact squared-Moebius
support and then by the displayed uniform constants, without h<=X.
Dependencies: the existing genuine `realMoebiusStep`, its pointwise square
bound, natural gcd divisibility, finite-sum injections and field arithmetic.
No Mertens, zero-free, prime-error, global covariance, or RH premise is used.

For each physical pair (d,n), define
`g=gcd(n,d), k=d/g, m=n/g`. Exact divisibility reconstructs
`(d,n)=(g*k,g*m)`, so this map is injective. On the original domain,
`G<=g<h`, `1<=k<=floor(h/g)` and `1<=m<=floor(4X/g)`.
Every original weight is exactly `2(h-gk)` and every lattice weight is
nonnegative. Thus enlarging to this lattice is a legitimate majorant.
It neither reuses a physical occurrence twice nor substitutes a model for
the source being bounded.

For q=floor(h/g),

```text
S_g = sum_(k=1..q)(h-gk) = qh-gq(q+1)/2,
2g S_g = h^2-(h-gq)^2-g^2 q <= h^2,
floor(4X/g) * 2 S_g <= 4Xh^2/g^2.
```

The reciprocal-square tail telescopes:

```text
sum_(G<=g<h) 1/g^2
 <= sum_(G<=g<h) (1/(g-1)-1/g)
 = 1/(G-1)-1/(h-1) <= 1/(G-1).
```

Since G>=2, `G<=2(G-1)` gives the constant-eight corollary. Actual
`mu(n)` lies in {-1,0,1}; consequently `|mu(n)mu(n+d)|` equals its squared
support term and that term is at most one. This proves the entire chain.
G=h is the empty original tail. X>=1 guarantees positive original n;
real subtraction is used in weights, with positivity proved from d<h.

Implementation strategy: canonical Sigma-valued gcd coordinates, inverse
map and finite-set injection; exact triangular-sum induction; reciprocal
tail induction; explicit original-source product-sum transport. Denominators,
casts, truncated natural quotient endpoints and all finite ranges are proved
inside the module, not informal side conditions.

### E. Exact Formal Surface

Source: `research/CODIV_LARGE_GCD_TRIANGULAR_20261107.lean`, namespace
`RHLean.Analysis`. Definitions `codivLargeGcdPairs`,
`codivLargeGcdCovariance`, `codivLargeGcdSupport` preserve the original
finite pair filter and genuine Moebius values.

The five public declarations are:

```text
codivLargeGcdCovariance_eq_original (X h G : Nat) :
  covariance X h G = the original nested filtered sum above

codivLargeGcdCovariance_abs_le_support (X h G : Nat) :
  |covariance X h G| <= support X h G

codivLargeGcdSupport_le_sharp (X h G : Nat)
  (hX : 1<=X) (hG : 2<=G) (hGh : G<=h) :
  support X h G <= 4*X*h^2/((G:Real)-1)

codivLargeGcdSupport_le (X h G : Nat)
  (hX : 1<=X) (hG : 2<=G) (hGh : G<=h) :
  support X h G <= 8*X*h^2/G

codivLargeGcdCovariance_abs_le (X h G : Nat)
  (hX : 1<=X) (hG : 2<=G) (hGh : G<=h) :
  |covariance X h G| <= 8*X*h^2/G
```

Here the short labels covariance/support abbreviate the fully named
definitions only for readability; the committed source and CI `#check`
output contain the exact elaborated types. There is no hidden h<=X,
positive-sign assumption, asymptotic hypothesis, or target-sized supplier.
Five public declarations and seven private supporting theorems suffice;
no parallel arithmetic abstraction or unrelated root reorganization is added.

### F. Carrier, Dependency And No-Circularity Audit

Original pairs, triangular weights, gcd cutoff, both Moebius factors and the
forward halo are retained in the definitions. The first sign loss occurs
only in the explicitly stated absolute-to-support inequality. The subsequent
positive majorant drops arithmetic masks lawfully for an upper bound.
It is not presented as an equality with a mask-free primitive source.

GL1's full primitive-pair identity with both coprimality masks is tested
finitely but is not separately formalized here. GL3's support lower bound,
its large explicit threshold, and Referee NC/PF claims are not part of this
Lean result. In particular a lower bound for support does not lower-bound
the signed sum. No nonpositive cross-term, independence, density, missing
residual estimate or frozen-normalization change occurs.

The imported native module contains unrelated legacy native computations.
Permission is assessed through the actual transitive axiom output of these
five declarations, not by assuming the whole imported namespace has the
same axiom footprint. Only the standard permitted logical axioms may pass
the dedicated fail-closed audit. No local Lean execution was performed.

### G. Implementation And Independent Finite Checks

Exactly three focused files are added: the Lean module, a deterministic
exact-arithmetic regression script, and its dedicated Actions workflow.
Existing root declarations, source-policy checks, inventory and export
checks are untouched. The targeted research closure reaches the new leaf;
the dedicated job explicitly checks every new public theorem and its axioms.

The Python script uses trial factorization and integer/Fraction arithmetic.
It passed 4896 cases with X=1..32, h=2..18, G=2..h, including 1785 with
h>X and 544 with G=h. It checks source weights, unique gcd coordinates,
positive lattice domination, telescoping and both upper bounds. It also
tests the two-mask primitive identity without claiming a kernel proof of it.

Six named fixtures (including two reused sign controls) return (T_ge,W_ge):

| (X,h,G) | Exact values |
| --- | --- |
| (225,6,5) | (16,56) |
| (1764,12,9) | (-16,260) |
| (49,17,2) | (-578,2410) |
| (1,41,2) | (-454,574) |
| (2,64,3) | (-580,1928) |
| (4096,16,12) | (-86,1710) |

These tests detect favorable-sign and endpoint-clipping mistakes. They are
finite checks, not a substitute for the uniform Lean theorem or a claim of
new independent Referee review. Python syntax validation also passed.

### H. Branch And Exact Revision

PR #1102 targets main from the authorized branch
`agent/lean-verification/20261107-codiv-large-gcd`.
Base: `1c057c1d65b6d4cb4d59d207f69a815c52353314`.
Current head: `5b246ac81398ae8ee8f177dc9acda18288765a4e`.
Lean blob: `f24498bfe13d88d0f8ba621ce103e81d6c800379`.
Regression blob: `3ce118ef956751e8c78f521ff32bc5451582d5bb`.
Workflow blob: `b5f580308ee435577c5e087de573ff31b0fac469`.
Tree: `0f66340aaf1e43c2f0fbc93d18f8b69efe40bf59`.
After all exact-head checks passed, the PR was marked ready for review at
2026-11-07T10:36:44Z. It is open, non-draft and unmerged. Human review and
merge remain outstanding, not delegated to this agent.
The connected branch/blob/tree/commit/ref/PR writes actually succeeded.
No direct-main write, merge, auto-merge, schedule edit or agent launch occurred.

### I. GitHub Actions Evidence

All **13 check runs across 12 workflows** are completed/success on exact
head `5b246ac81398ae8ee8f177dc9acda18288765a4e`. The raw run metadata
confirms pull_request event, PR #1102, that head, and the pinned main base.
The checkout log records synthetic merge
`388a28232f1b07f0c9c6b561dca1ae58cef210ad`, with parents equal to that base
and head. Its Git tree exactly equals the head tree in H; its fetched Lean
blob and full source bytes match the implementation. This is exact PR-head
evidence, not a claim that unmerged source is already on main.

| Workflow | Run / directly inspected job where applicable | Result |
| --- | --- | --- |
| CODIV large-gcd triangular bound | [42364367658 / 128379218641](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367658/job/128379218641) | SUCCESS; exact regressions, pinned warning-fatal closure, fresh recompile, all five types and axiom lists |
| Targeted Lean iteration | [42364367519 / 128379218006](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367519/job/128379218006) | SUCCESS; independent changed-source compile and source-addressed reuse smoke check |
| Lean source audits | [42364367459](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367459), jobs 128379217692 and 128379217915 | SUCCESS; source/holes/axioms/root manifest and hosted native build/elaborated graph |
| Proof inventory | [42364367599 / 128379218177](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367599/job/128379218177) | SUCCESS; source counters and graph regressions |
| Public export verification | [42364367469 / 128379217931](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367469/job/128379217931) | SUCCESS; export synchronization, closure and repository-reference audits |
| Coordinate atlas | [42364367557](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367557) | SUCCESS |
| Prevent new cold-only Lean/OpenAI CI | [42364367466](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367466) | SUCCESS |
| VF normalized infrastructure | [42364367592](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367592) | SUCCESS |
| VF recursive child/complement | [42364367564](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367564) | SUCCESS |
| VF source to sector-six inlet | [42364367489](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367489) | SUCCESS |
| VF final aggregate contraction | [42364367470](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367470) | SUCCESS |
| VF pre-914 consolidation | [42364367498](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367498) | SUCCESS |

Actual dedicated logs show `compiled=1 cached=0`, then a fresh
`lake env lean -DwarningAsError=true` invocation and successful fail-closed
audit. Each of the five declarations prints exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or native-evaluation
axiom remains. The exact elaborated hypotheses and coefficients agree with
E. The targeted workflow also shows `compiled=1 cached=0`, followed by
`compiled=0 cached=1` on its explicit reuse check.

Hosted root logs verify agreement on 8,870 named native proofs and no
RHLean-owned warnings. These native inventory counts are not the new
research leaf's declaration count; the dedicated audit checks its five
public declarations separately. Export logs explicitly state that export
Lean compilation is intentionally local-only: no separate export compile
is claimed or attempted. No export source changed. The global source/root,
export synchronization/reference, and dedicated research compilation checks
together cover the repository's applicable surfaces without weakening them.

The [preserved source and audit artifact](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367658/artifacts/13571431345)
is artifact 13571431345, with recorded ZIP SHA-256
`fbf36a6ce7b150791192fc4c22ad0e5ca094270ad34778ef8a6842474cb63f6d`.
Its upload and metadata were verified; the source and full audit were read
directly from immutable GitHub source and actual job logs. No unperformed
binary-artifact download is claimed.

Pinned compiler: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
PNT+: `c39a751132c88b6e8080b74c74023fd95b3d8be0`.
The dedicated workflow requires fresh warning-fatal compilation after the
source-addressed closure build, exact coverage of the five public theorem
names/types, explicit `#print axioms`, a fail-closed permitted-axiom test,
and a no-placeholder/native-evaluation source scan.

### J. Actual Failures And Repairs

| Revision | Dedicated run / job | Diagnosis and repair |
| --- | --- | --- |
| `3ccef8f0a095268a322be71403cb9c909605181b` | 42363415534 / 128376323672 | Pair-type ASCII multiplication parsed as a type-level multiplication; denominator normalization and positivity obligations. Use explicit `Prod Nat Nat` and prove the field/positivity steps. |
| `d551268cc0c74b2f5ed49a88fd81b87cd81c3e63` | 42363634625 / 128376980950 | A tactic ran after its goal was solved; original-sum simplification did not finish. Remove the redundant tactic and make the finite-sum transport explicit. |
| `aa401fb98b888fe94a99d719ac8366e67831c9ca` | 42363898896 / 128377780348 | Product-sum rewrite still failed to match the displayed filtered expression. Use the general finite-product lemma with the explicit membership equivalence. |

These were elaboration/proof-script failures, not counterexamples or reasons
to change the mathematics. Error-recovery `sorryAx` appeared in failed
compiler output for the unfinished declaration; those revisions are not
certified. No `sorry`, `admit` or project axiom was authored. All five public
theorem statements and hypotheses remained unchanged through the repairs.
Warnings-as-errors and all audits remain enabled.

### K. Prior Merged Work Reverified

Prior unfinished #1100 is now human-merged, at 2026-11-07T05:19:51Z.
Its tested head is `e52207d527da684346e151d4ff680696c88e8fa7` and its merge
is today's main. The retrieved [dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42328802826/job/128270266477)
in run 42328802826 is completed/success. Actual logs show warning-fatal
compilation and eleven standard-axiom lists at synthetic merge
`c004afeecb0e4d81b734e2b9796cf2a6e43468b4`, incorporating that head into
`d4df133117c5b58f90979d2eb680167ef37995cf`.
Tested radical-increment source blob
`c5ebb3d5d96898549ad039fd32e1a26955c5b8f8` equals current main.
This reuses verified unchanged evidence; it is not a new build of all main
and does not certify the CODIV theorem or an Nyman norm bound.

### L. Mathematical Discoveries From Formalization

The paper proof counted the short interval by `3X/g+1` and used h<=X to
absorb a harmonic term. Counting inside the larger positive initial interval
`1<=m<=floor(4X/g)` instead gives `4X/g` directly. The same triangular
weight then removes the need for h<=X without any new arithmetic hypothesis.
The telescoping step also exposes the stronger denominator G-1.

This is a genuine quantified strengthening and a simpler independent proof,
not a changed carrier or a silently weakened target. It does not improve
the 1/G exponent or contradict GL3's accepted support-only sharpness.
No optimal constant or uniform near-cutoff lower bound is inferred.

### M. Significance And Complete Consumer

Formal soundness is the exact-head proof/axiom status in section I.
Mathematical significance is narrower: an unconditional quantitative bound
for the large-gcd part of the original signed short-lag covariance.

The independently accepted paper return, not newly formalized in this PR,
retains all source terms:

```text
E_max(H) <= (8H/h^2) T_lt(H^2,h,G)
          + 64H^3/G + 24H^3/h
          + 8H(h-1)(2h-1)/(3h) + 2H(h-1)^2.
```

The new stronger denominator allows the tail term to be replaced on paper
by `32H^3/(G-1)`. This is a constant improvement, not a new power.
The displayed remaining terms are, respectively, the small-gcd signed
source, paid large-gcd source, arithmetic diagonal, full forward halo and
translation endpoint error. Mixed interactions are not deleted.

For h=floor(H^(2/3)), G=ceil(H^(7/12)), the paid tail has size O(H^(11/4))
before its consumer multiplier. A new one-sided small-gcd bound of the same
size with arbitrary positive loss would imply E_max << H^(29/12+eps),
and, after shell Cauchy, dyadic aggregation and incomplete-prefix payment,
M(x) << x^(41/48+eps). These are CONDITIONAL conclusions only.
The missing supplier is target-equivalent to the inherited sufficient
OPEN-CD5 lag estimate at this cutoff because the complementary tail is
independently paid. It is not thereby equivalent to, or proof of, the
canonical actual-prime objective. No endpoint comparison is promoted to
an achieved gain; broad research remains active.

### N. Specialist Handoffs

- Coordinator: register GL2-TAIL as a scoped quantitative component with
  exact PR-head status; preserve all nine routes, existing strict baseline
  and SEARCH_BROAD. Do not count the conditional 41/48 return as achieved.
- Analytic: the upper tail now admits X>=1 without h<=X; the first open
  supplier is the one-sided small-gcd estimate in O. GL3's accepted lower
  support theorem remains a separate formalization candidate.
- Referee: check the strengthened parameter range and positive initial-
  interval majorant independently. Your GL2 acceptance covers the original
  range; this report does not self-issue acceptance for the extension.
- Owner: SG cofactor restrictions may be compared only through an explicit
  original-weight map. No SAT-to-CODIV transport or signed gain is presumed.
- Wheel: any DI/CORR4 overlap restriction used for T_lt must preserve actual
  occurrences, coefficients, multiplicity and the unbounded forward value.
- Census: preserve both-sign fixtures and h>X/empty-cutoff/halo controls.
  SC capacity-safe transport does not automatically pay the signed source;
  propose tests for a stated small-gcd mechanism, not a global power from a
  finite scan.

### O. Exact First Missing Mathematical Statement

For every eps>0, independently prove existence of C_eps>0 and H0 such that
for every integer H>=H0, with h=floor(H^(2/3)) and G=ceil(H^(7/12)),

```text
2 sum_(1<=d<h) (h-d)
  sum_(H^2<=n<4H^2, gcd(n,d)<G) mu(n)mu(n+d)
    <= C_eps H^(11/4+eps).
```

This is a one-sided original signed bound, not an absolute-support bound;
the forward endpoint n+d remains genuine. Its constants may depend on eps,
not on H. It is OPEN, is not an assumption of the new Lean theorem and is
not solved by the positive lattice majorant. The next invocation should
not restart the completed large-gcd argument or reconstruct paid native 7/8.

### P. Source Ledger, Resume And Publication

Material source blobs at the pinned baseline:

| Path | Blob SHA |
| --- | --- |
| RHLean/Analysis/DeterministicTGreenKuboComparison.lean | `802a58b4e1994a5f8c14f1080ac42d0f5f28a0d5` |
| research/VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019.lean | `55839f2013fc5b8d352dcea0e2ed4bb47d763693` |
| research/VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019.lean | `4ace115a6ec7537af5f871a97486e2b8cd5086e5` |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| lean-toolchain | `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5` |
| lakefile.lean | `6ef95e9ebf184d5846fee88a9cdf2db3a38afc97` |
| lake-manifest.json | `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4` |
| .github/actions/research-compile/action.yml | `be6e049c256719f08cd82f3c6581f27ede888b58` |

Public theorem statements are unchanged across the repair history. The
regression script SHA-256 is
`6a1b84a8eb99b1caa7d7818a9821efe12244bc47bc63424c5a1d7f24b10ce79d`.

Resume: first refresh main and #1102's actual latest head/status. Reuse green
evidence only for unchanged source and dependencies. If a new valid head
fails CI, repair that proof first; otherwise preserve the human review/merge
boundary and choose the next independently ready mathematical candidate.
Do not introduce the open O supplier as a hypothesis and report its endpoint
as established. No extra scheduled run or agent delegation was launched.

Report path remains
`research/agent_reports/2026-11-07/60-lean-verification.md` on agent-reports.
Earlier verified publication commits are
`ce3c664b2b9d0d5d9bd901c3696e8d9195b13d57`,
`48812e4e550fd9658628cd3f1e3bccdf7fbab136`, and
`d9d3a101e3965f01c14c84608545de5004d3dbad`.
This synthesis is PENDING_READBACK until its actual commit and immutable
byte-for-byte readback are recorded in the receipt. No local artifact or
unperformed test is presented as a published result.
