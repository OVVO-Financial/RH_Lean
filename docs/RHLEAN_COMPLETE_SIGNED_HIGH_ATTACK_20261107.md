# Complete signed HIGH: common objective, independent proof routes

**2026-11-08 update:** The new [all-route handoff](RHLEAN_REPO_WIDE_PROOF_ATTACKS_20261108.md) and [generated DAG](PROOF_DEPENDENCY_DAG.md) supersede the pre-#1107 baseline in this directive. #1107/#1108 prove the same-source explicit strict boundary 7/8-1/(48*N_*) and an exact original amplification bound; #1109 proves original off-ray q2 cutoff image multiplicity only. The complete signed HIGH objective remains, but all nine viable routes and independent owner/analytic/wheel portfolios are protected. Existing 1->7/8 signed cancellation and the new strict gain are PAID. A local marked 1+t/2 or kappa supplier is not itself an improved terminal bound, and the terminal q(X)->0 is OPEN.


**Policy tag: `COMPLETE_SIGNED_HIGH_ATTACK_V1`. Effective after human merge.**

All seven agents focus on improving the complete signed contribution carrying the global Mertens endpoint, or on an explicitly justified route to that improvement. The existing cancellation and strict endpoint are starting inputs. This policy changes research priorities; it proves no new inequality, numerical exponent or RH claim. Repository text alone does not update saved Studio settings or establish that an agent has run.

Initial source snapshot for this instruction update: main `aa10b310efb2a095fd4c69dc965e6bde0bd135d6`, including merged PR #1103. On actual execution, verify current main and affected declarations; this snapshot is provenance, not a frozen task queue or a substitute for current proof evidence.

## 1. Authority and meaning of the focus

Read this directive with [AGENTS](../AGENTS.md), the [stable task selector](RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md) and [seven-role prompts](RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md). It governs the shared objective and supersedes conflicting dated NEXT-* priorities, historical unpaid-cancellation tickets and repository prompt templates. Live mathematical hypotheses, counterexamples, proof-integrity rules and role permissions remain authoritative.

The [cancellation-chain reuse policy](RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md), [paid-baseline correction](RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md) and [independent multi-front policy](RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md) remain supporting rules. Use their established suppliers and exact consumers. Do not rediscover the already-paid chain or introduce a new universal covariance, sharp-shell, arbitrary-vector or inverse-norm prerequisite.

Exclusive focus means that a substantive task identifies the complete signed endpoint it serves, its actual or prospective consumer, and the mathematical change under investigation. It does not require every role to attack one formula or every supporting lemma to contain HIGH in its name. Developing a missing quantitative bridge, finding a useful identity, repairing a genuine source obstruction and establishing a needed auxiliary LOW estimate are eligible work when their purpose and current conditional status are explicit.

Protect all nine routes: **VF-LOW, SAT, JOH, CODIV, OAI-NNS, NYMAN, FINITE-AC, CORR4 and MU-LIFT**. Serious new hybrids remain eligible. Owner retains VF-LOW/SAT/JOH; Analytic retains CODIV/OAI-NNS/NYMAN; Wheel retains FINITE-AC/CORR4/MU-LIFT. A common endpoint does not transfer all three portfolios into OAI or make a rational-to-Hecke identification a prerequisite for native work.

Keep the established BLOCK and other source-valid falsifiers at their proved scopes. A refuted narrow component inequality does not refute a complete signed identity with its legitimate corrections restored.

## 2. Canonical accounting: LOW is supplied

Fix one cutoff `Lambda >= 0`, independent of the scale. Use the actual canonical largest-prime/cofactor representation and the atom's birth square block. Its HIGH threshold is an **absolute-height** condition; positive orientation alone does not establish HIGH membership. Preserve both orientations and the original Möbius coefficients.

Write:

```text
X_R = R^2 - 1
L_R = canonicalLowPrefix_Lambda(R - 1)
H_R = canonicalHighPrefix_Lambda(R - 1)
M(X_R) = L_R + H_R
|L_R| <= (Nat.floor Lambda + 1) * R.
```

The definitions and partition are in [CanonicalHighSectorCore](../RHLean/Analysis/CanonicalHighSectorCore.lean); [CanonicalLowOccupancy](../RHLean/Analysis/CanonicalLowOccupancy.lean) supplies the unconditional LOW bound. [CanonicalHighSectorBridge](../RHLean/Analysis/CanonicalHighSectorBridge.lean) supplies LOW internally when relating the canonical criteria. There is no remaining canonical LOW-control hypothesis to discover for fixed `Lambda`.

For an exponent at least `1/2`, the exact split and LOW bound transfer an applicable global Mertens bound to HIGH. Conversely, a HIGH bound controls the square endpoints; filling an unfinished square block costs at most `2*R + 1` using `|mu(n)| <= 1`. Include this cost in a claimed global transfer. This explanation is not a claim that this policy adds a newly compiled theorem.

The `O(R)` allowance is the floor of this particular transfer. It is not a lower bound on the actual size of either signed component. Allowing `Lambda` to grow requires new uniform estimates and explicit accounting; the fixed-cutoff argument does not provide them.

## 3. Common target and comparison with the certified baseline

Before claiming an improvement, identify the strongest applicable certified baseline on the chosen source/consumer path. Record its exact declaration, source revision, hypotheses, quantifiers and any existential witness or epsilon dependence. Use `b_base` for the exponent or every-positive-loss boundary so supplied. Do not silently replace an existential strict gain by an explicit number, claim a limiting infimum is attained, or weaken an available strict result back to nominal `7/8` for comparison.

A common canonical target is a fixed `eta > 0`, with `b_base - eta >= 1/2`, satisfying:

```text
For every epsilon > 0, there exists C_epsilon >= 0 such that
for every integer R >= 2,
  |H_R| <= C_epsilon * R^(2*b_base - 2*eta + epsilon).
```

Constants may depend on the fixed cutoff, chosen baseline witness, fixed gain and epsilon. Record all additional dependencies. A family of constants depending on the growing scale does not establish this target.

The corresponding HIGH prefix-window target is:

```text
For every epsilon > 0, there exists C_epsilon >= 0 such that
for every integer N >= 1 and every integer h with 1 <= h <= N,
  sum_(0 <= j < h) |canonicalHighPrefix_Lambda(N + j)|^2
    <= C_epsilon * h * N^(4*b_base - 4*eta + epsilon).
```

These are energies of **prefix values**, with a constant uniform in `N` and `h`. They are not energies of square-shell increments. Include `h = 1`: it recovers a pointwise bound after the square root, index shift and epsilon relabeling. Conversely, summing the pointwise estimate over `[N,2N)` gives the displayed window bound. An estimate only at `h = N` does not automatically supply all windows or the same global exponent.

For orientation, a boundary `b_base = 7/8` gives amplitude `R^(7/4 - 2*eta + epsilon)` and window energy `h*N^(7/2 - 4*eta + epsilon)`. Use the actual stronger baseline when one is certified. An already-proved strict HIGH consequence is paid work, not a fresh discovery.

Spend the loss explicitly before announcing a fixed exponent. For example, applying the amplitude target with `epsilon = eta`, restoring LOW and the final partial square block, gives `M(x) = O(x^(b_base - eta/2))`. This is a fixed gain of `eta/2` over `b_base`. Alternatively state an every-positive-loss boundary at `b_base - eta` with its own quantifiers. Do not announce the exact fixed power `b_base - eta` while retaining an unspecified positive epsilon.

An independent route can target its own stronger Mertens, prime-error or RH criterion. State the proved quantitative transfer and its direction, or name its missing bridge as the next lemma. A prospective bridge is a research task; it is not an established global gain.

## 4. Complete representations and the terms they retain

Use the actual source definitions and the [coordinate atlas](COORDINATE_ATLAS.md). Names and syntactic import paths do not prove that two populations coincide or that an estimate transfers in both directions.

| Representation | Required signed accounting | Source |
|---|---|---|
| Canonical HIGH covariance | Coherent mean and centered covariance together | [CanonicalHighSectorCovariance](../RHLean/Proof/CanonicalHighSectorCovariance.lean) |
| Birth and moving HIGH | Still-HIGH mass plus absorbed birth-HIGH mass | [BirthMovingAbsorption](../RHLean/Proof/BirthMovingAbsorption.lean) |
| Ancestry path | Root, low-to-high forcing and high-to-high transport in the full six-term Gram | [CanonicalGapAncestryQuadraticClosure](../RHLean/Proof/CanonicalGapAncestryQuadraticClosure.lean) |
| Corrected conductor sector | Conductor one, large conductors, all cross terms and the smooth correction | [CorrectedConductorHighSectorGram](../RHLean/Analysis/CorrectedConductorHighSectorGram.lean) |
| Collapsed signed conductor core | Exact reindexing error and the actual cutoff hypotheses | [CorrectedConductorHighSectorCutoffError](../RHLean/Analysis/CorrectedConductorHighSectorCutoffError.lean) |
| Frozen/top/far endpoint | Compensated root boundary and the complete far residual | [FinalCompensatedParentReduction](../RHLean/Proof/FinalCompensatedParentReduction.lean), [FrozenTopFarAdaptiveRawBridge](../RHLean/Proof/FrozenTopFarAdaptiveRawBridge.lean) |

For covariance, retain `h*|mean(H)|^2` together with the centered energy. At `h = 1` the centered contribution is zero and the coherent contribution contains the whole value. Removing the zero frequency or declaring a main term harmless requires an exact, quantitatively controlled compensation.

For moving cutoffs, use the signed identity:

```text
canonical birth-HIGH prefix = still-HIGH birth mass + absorbed birth-HIGH mass.
```

A bound on surviving atoms does not bound their original birth prefix after absorbed mass is dropped. Retain lifetimes, activation and absorption boundaries, both height orientations and their multiplicities.

For an ancestry path `A - B - C`, use:

```text
G = E(A) + E(B) + E(C)
    - 2*<A,B> - 2*<A,C> + 2*<B,C>
  = E(actual HIGH path).
```

Preserve every sign and cross term before taking norms. Separately small positive pieces can be a sufficient approach, but are stronger demands than the complete target. The compiled identity/equivalence does not discharge the quantitative proposition named by a `Statement`, `EstimateAt` or `BoundedBy` definition. Retain `Lambda >= 0`, endpoint source bounds and all other hypotheses of the chosen ancestry transfer.

For conductor work, call the cutoff `Q` here to distinguish it from the square-root index `R`. The hard sector contains `J_1 + sum_(q > Q) J_q`; the controlled small sector is `2 <= q <= Q`. Retain the full cross-conductor Gram. A boundary-divisor cutoff `d` introduced by Möbius reindexing is not automatically the original conductor `q`.

Under the source's primorial-block hypotheses and `Q^8 <= U`, the cutoff-error theorem supplies:

```text
|HIGH_sector|^2 <= 2*|HIGH_core|^2 + 512*U.
```

This is a one-way bound from the complete core to the sector, with its error. It gives no reverse bound on the core or its individual components. Use the existing synchronized wheel-to-Mertens construction with its actual block endpoints; do not manufacture an abstract missing bridge where a concrete one is already supplied. The remaining quantitative task must identify the complete signed object and its true scale map.

For the frozen/top/far path, preserve:

```text
M(R^2 - 1) = finalCompensatedRootBoundary(R)
            - lowWheelFrozenTopFarResidual(R)
|finalCompensatedRootBoundary(R)| <= 10*R  for R >= 56.
```

The far residual carries the remaining endpoint. Retain parent, child and pivot ordering, repeated occurrences, the exact crossing wall and every rough-root/ledger correction in the representation used. A counterexample to uncorrected raw parent-core domination does not reject a recurrence with a legitimate additive `O(R)` allowance.

Already-zero or controlled corrected HIGH tails are paid inputs. In particular, keep complete nonrecursive high-owner cancellation separate from recursive owners, owner two, renewal terms and terminal columns. Do not reopen the paid tail as an unpaid generic cancellation campaign.

## 5. Immediate analytic priority: retain strength through the complete return

Use the existing [retained-slot feedback record](../research/oai_434/RETAINED_SLOT_FEEDBACK.md), current source declarations and their actual verified revisions. The [native seven-eighths replay](../research/oai_434/VF919NativeSevenEighthsReplay.lean), [native strict Mertens path](../research/oai_434/VF919NativeStrictMertens.lean) and cancellation-reuse directive locate paid consequences. This policy uses source evidence; it neither adds the external full audit bundle to the repository nor claims a fresh repository-wide kernel rebuild.

### A. Carry the literal marked `1+t/2` estimate downstream

The retained-slot supplier `RetainedSlotDetector.source_batch_plain_marked_fine_half` preserves `1 + D.t/2`; the older common moment interface allows `1 + D.t`. Trace the actual wrapper or consumer where this information is widened. Preserve the sharper branch through marked counts, combined counts and the complete probe return instead of reproving the supplier.

Keep the actual selected slots, profiles, source rows, fineness, heights, plain factors and zero cases. Preserve the marked capacity:

```text
2*m + 6*kappa*sum_selected_widths <= 1.
```

A second moment does not license a fourth-moment argument. A weighted fourth-moment or retained rescaling route remains eligible where its actual supplier and consumer match. Retaining `1+t/2` improves the global result only if the complete comparison improves after all other binding terms are restored.

### B. Extend combined counts at the generalized `kappa`

The generalized energy/moment package admits `kappa > 1/2` subject to its full licensing conditions. The older combined branch/count/crossing argument uses `Delta >= 0` with `kappa = 3/4 + 2*Delta`. Its moment-record parameterization

```text
Delta_kappa = (kappa - 3/4)/2
```

is negative when `kappa < 3/4`. That is a parameter in the generalized moment representation. It does not license changing the actual `HighData`, assigning a negative physical source parameter, or silently reusing an old proof that needs nonnegativity.

Reprove or parameterize the combined-count and crossing steps exactly where the old sign restriction was used. State what replaces it and verify every boundary case. Keep the original actual `HighData` and all its source hypotheses unchanged. Preserve old interfaces where useful, with a separately proved generalized consumer.

Choose a fixed `kappa0 > 1/2` before selecting constants, margins and thresholds. State any uniformity for `kappa >= kappa0` explicitly. Do not infer uniform control as `kappa0` tends to `1/2` from the fixed-margin theorem.

Retain full-family licensing, including

```text
2*HeckeZeroSupremum.beta - 1 <= kappa,
```

and the source's original lower-beta range, profiles, height, conductor and fineness conditions. Licensing a single detected zero is not licensing the full family. The complete theorem must retain its actual admissible source and parameter ranges.

### C. Demonstrate the endpoint change

Connect the improved supplier to the actual global consumer, then recompute the full LOW/HIGH/principal comparison and every selected, unselected, remote, exceptional, height, conductor and complementary branch. Identify the worst surviving term. A smaller admissible `kappa`, a sharper marked count, licensing/mesh reuse or an import alone is not a new endpoint theorem.

For feedback, establish the next step from the already-certified input boundary: `b_new <= F(b_old)` with `F(b_old) < b_old` on its licensed range. Supply each step's hypotheses and constants. Do not use the desired output to license its own proof, iterate automatically to `1/2`, or claim a uniform gain across an unproved boundary regime.

These are immediate Analytic/Lean/Referee handoff priorities. Native ancestry, conductor, frozen/top/far, Co-Div and the other protected routes continue independently, with their own complete consumers.

## 6. Supporting LOW work and honest obstruction scope

Canonical LOW, OAI selected reflected-inverse LOW, a detector HIGH branch, energy-induction HIGH and a full-probe HIGH estimate are different objects. An inverted quotient coordinate can make the quantity named HIGH easy and the quantity named LOW difficult. Identify the carrier, cutoff, norm, weights and transfer before using any of these labels.

In the OAI reflected-inverse construction, `low_selected_nominal_energy_tilted` uses `lowSelectedInverseRow_actual_reflected_energy` with its selected-slot scale conditions. The familiar `24*t <= ell_i` restriction is a sufficient admission condition arising from that construction's tilted physical scales. Preserve it when invoking that theorem; do not promote it to a universal impossibility theorem for all complete-return methods.

Improving a supporting LOW consumer, retaining a weight, or proving an alternative legal bridge is compatible with exclusive focus on the complete signed endpoint. Conversely, dropping an inverse weight, nonunit mask, principal/resonant mode, collar or complementary population because its name seems peripheral is not a valid improvement.

A definition is not its bound; a compiled equivalence is not its missing hypothesis; an exact coupling is not an invertible norm estimate. State whether a claimed obstruction refutes a particular construction, parameter regime or complete criterion. A source mismatch or missing import is not evidence that every other route needs a new primitive cancellation theorem.

## 7. Seven distinct outputs and protected portfolios

| Role | Required useful output under this objective |
|---|---|
| Coordinator / Proof Architect | Maintain one complete-return map per active proposal, compare its certified baseline and candidate budget, identify the first unpaid term and assign at most two implementation-sized Lean tasks. Protect independent coverage and deduplicate unchanged replays. |
| Owner Payment / Signed Arithmetic | On VF-LOW/SAT/JOH, derive a stronger actual weighted return or the minimal needed bridge, retaining chronology, least-owner multiplicities, masks, mismatches and terminal/cross-owner costs. Use applicable native Mertens/prime-error input without assuming Hecke identification. |
| Analytic Type II | On the OAI-NNS turn, propagate the literal marked estimate and prove generalized-kappa combined/crossing consumers, with the full return. On CODIV and NYMAN turns, pursue their own signed coefficients, common windows, full basis and tail. |
| Finite Wheel & Incidence | On FINITE-AC/CORR4/MU-LIFT, improve the complete signed conductor/occurrence/renewal consumer or a needed incidence/admission interface. Preserve conductor one, multiplicities, boundaries, product-versus-LCM distinctions and all corrections. |
| Prime Census Laboratory | Discriminate a specific changed inference using original carriers and exact arithmetic or certified intervals. Test coherent/absorption/cutoff and crossing boundary cases, restoring complements. State the scope of a witness or feasibility certificate. |
| Adversarial Referee | Independently reconstruct the changed inference, validate the baseline and complete budget, check scale/parameter licensing and challenge both erased signed terms and unnecessary stronger prerequisites. Return scoped acceptance, a legal falsifier or the smallest missing lemma. |
| Lean Verification | Repair genuinely active diagnosed CI failures, then formalize the highest-readiness justified improvement with its actual consumer. Verify theorem types, dependencies, exports and axioms; distinguish helpers, conditional transfers and complete global results. |

The three investigators retain the established rolling three-substantive-invocation route coverage and the recorded breakthrough-deferral/recovery mechanism. Do not spend every invocation on the immediate OAI branch or silently reset coverage because the shared objective changed. Cross-route help is useful; copying the same investigation into seven reports is not.

## 8. Compact report and continuation contract

Append substantive work to the existing own report, preserving prior failures, corrections, source provenance and the resume capsule. Do not create another shared administrative report or regenerate the historical audit. The [persistent research engine](RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md) and [multi-run policy](RHLEAN_MULTIRUN_DAILY_AGENT_POLICY_20261031.md) remain in force.

Use this compact record where applicable:

```text
high_attack_ack: COMPLETE_SIGNED_HIGH_ATTACK_V1
main_policy_sha / source_sha / role / selected_route:
exact_signed_object_and_cutoffs:
certified_baseline_declaration_and_hypotheses:
reused_supplier / actual_or_prospective_consumer:
changed_inequality_or_structural_restriction:
scale_map_and_complete_return_terms:
candidate_endpoint_budget_and_explicit_loss_spend:
first_remaining_unproved_step:
result_scope / independent_review / compilation_evidence:
next_derivation_and_coverage_continuation:
```

Record `high_attack_ack` on the first actual post-merge consumption, alongside the observed main/policy revision. Preserve existing chain, baseline and deployment acknowledgments where required. An acknowledgment alone is not research progress.

For exploratory work, mark the consumer or transfer as prospective and make its exact missing lemma the next task. For an endpoint claim, supply the whole return and comparison with the same baseline witness and hypotheses. Report separately: structural progress, component estimate, conditional transfer, independently reviewed proof, verified PR head and human-merged theorem.

Unchanged scans, renamed identities, repeated baseline replays and green wrappers that assume the target are not new gains. A source-valid failure can be progress when it narrows the next derivation. Reserve `VERIFIED_ETA` for the fully justified improvement under the existing acceptance contract, including explicit loss spending and required review/formal evidence.

## 9. Execution, report ownership and activation

Six non-Lean roles remain own-report-only. Coordinator owns byte-identical complete `00-coordinator-am.md` and `90-coordinator-pm.md` mirrors; Owner owns `10-owner-payment.md`; Analytic `20-analytic-type-ii.md`; Wheel `30-finite-wheel.md`; Census `40-prime-census.md`; Referee `50-adversarial-referee.md`. Preserve report provenance and the existing publication/checkpoint discipline.

Lean owns `60-lean-verification.md` and retains user-authorized task-relevant repository read/write on non-main branches through reviewable PRs, including source, documentation, scripts, workflows and policy. This directive adds no path, prefix or per-claim restriction to that authority.

Run Lean only through pinned, warning-fatal **GitHub Actions**. No local Lean, `sorry`, `admit`, hidden desired-bound premise, new project axiom, unsupported native evaluation or weakened checks. Inspect exact theorem types, imports, public exports, proof inventory and permitted axioms. Reuse verified evidence at identical hashes; do not create no-op CI merely to produce activity.

Merging remains human-only. No scheduled agent may push main, merge, enable auto-merge, launch another agent, change actual Studio schedules or alter tool grants. The policy permits continuation across the already-configured actual daily invocations; it does not invent a new invocation, finished check or activation.

After human merge, verify adoption from each agent's next actual report and its `high_attack_ack` plus observed revision. Until that evidence exists, report only that the repository instruction change is proposed or merged. Distinguish repository prompt updates from saved Studio configuration, and a queued check from its completed result.
