# RH | Lean Verification - 2026-11-03

## Scheduled Run Checkpoint - Claim `20261103-lean-1`

**Status:** PARTIAL / IN_PROGRESS. Scheduled invocation at 2026-11-03 05:10:01 America/New_York; runtime run ID unavailable.

**Authority:** main `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`; AGENTS blob `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; proof contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`. Canonical actual-prime VF von Koch statement and RH remain open.

**Continuity:** retrieved all available 2026-11-03 and 2026-11-02 role reports at reporting head `7b653e80430662c99565f7b565c99d1e48115e2a`, plus EXTERNAL_HANDOFFS blob `038018145c0fddb2f6306c0712373adf9cd1ea52` (no new entry after October 18). Today's Coordinator is TODAY=PENDING; yesterday's byte-identical Coordinator mirrors are YESTERDAY=CARRY_FORWARD. Previous Lean continuation `20261102-lean-3` was PARTIAL and selected #1075; it is not treated as completed.

**Priority A:** resume #1075, authorized branch `agent/lean-verification/slot-anchored-endpoint-20261102`, current head `acaa66c510259a6722e3d5590106fcb9b7d50181`. Eight returned ancillary workflows passed, but dedicated workflow [41580316113](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41580316113) FAILED. Diagnose its actual logs before any edit; do not infer mathematical failure from compilation failure.

**Other exact heads:** #1073 `9cbfce5295343bcb411e6d2cb159b59995cd985b` has 13 successful workflows; #1074 `5f53bca7d728576efcbbf2762885b7720e89aef7` has 7; #1076 `f676c9b13960f8c80b68bdf35a5f04b07370e228` has 8. All remain draft/open/unmerged. Today's Referee provides new scoped acceptance of #1074/#1076; detailed source and audit inspection is in progress. No fresh endpoint certification is asserted by this checkpoint.

**deployment_ack:** current NEXT-LEAN bootstrap is superseded by merged earlier finite identities and the explicit unfinished #1075 repair. Resume its precise source-sized fixed-7/8 HIGH/LOW endpoint, preserve the complete source and all audit checks. Lean execution is GitHub Actions only. No local Lean, policy changes, merges, schedule changes, or additional agents.

**Gate:** latest committed reports describe VERIFIED_ETA_ON_PR_HEAD, never on main; verification and exact scope are being checked. No new numerical gain, sharp-shell estimate, or RH conclusion is claimed here.

## Repair And Review Milestone - 2026-11-03 05:26 EST

PR #1075 received focused commit `c54bce957fa8c49ca944852b3a1b0e143f2d693b`, changing only `research/oai_434/VF919SlotAnchoredConsequences.lean` (new blob `0ef06d7ec94b2dbbc64f30aef3db65255ae59ff4`). The failed rewrite at line 68 is an elaboration/matching failure between explicit `Real.rpow` and power notation, not a false exponent identity. The repair normalizes with `Real.rpow_eq_pow` before applying the pinned `Real.rpow_mul_natCast` with explicit exponent and natural power. Added exact type prints for the signed-pair and signed-energy consequences. No theorem hypothesis, conclusion, carrier, workflow, or audit was weakened.

The new dedicated run [41618470421](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470421), job `125857764947`, started on the exact new head and remains CI_PENDING at this checkpoint. The old failed run printed `sorryAx` only for the unresolved energy proof and rejected the batch; that failed elaboration was not accepted as a theorem.

Separately, #1076 at unchanged head `f676c9b13960f8c80b68bdf35a5f04b07370e228` is now marked ready for human review. All 8 workflows, the actual dedicated logs, exact endpoint/axiom/live-dependency audit, and archived generated source were checked. Artifact 13205450942 has matching SHA256 `cbb21d4180886598d3f41bc16096049e8aa0a6e190121fc51cdeb8ab242defb6`; its three tracked proof blobs match current GitHub source. Referee `20261103-referee-1` independently accepts this exact head. No new build was requested for unchanged green source.

Both branches remain stacked on #1073 and overlap in three proof modules. The stronger #1076 tilt is `7*rmin/192`; #1075 uses `7*rmin/384`. This is a same-source comparison, not a numerical lower bound for an existential witness and not an additional exponent improvement produced in this run. Human integration must reconcile the alternatives. Nothing was merged.

## Final Synthesis - Claim `20261103-lean-1`

**Execution:** COMPLETE. **Formal result:** PROVED_IN_LEAN / PR_HEAD_ONLY. **PR status:** #1075 and #1076 REVIEW_READY, open and unmerged. **Review scope:** this repair is SELF_AUDIT; the unchanged #1076 has the separately cited independent Referee acceptance. Evidence snapshot: 2026-11-03 05:36:38 EST. Runtime run ID was not exposed; this is the scheduled 05:10:01 invocation, not an invented second run.

### A. Most Important Formal Result

Resumed unfinished `20261102-lean-3` and repaired the signed-energy consequence in [PR #1075](https://github.com/OVVO-Financial/RH_Lean/pull/1075) without changing its statement. All nine workflows pass at new exact head `c54bce957fa8c49ca944852b3a1b0e143f2d693b`. The separate, stronger LOW-first [PR #1076](https://github.com/OVVO-Financial/RH_Lean/pull/1076) was verified at its unchanged head and marked ready for human review. No new independent arithmetic exponent saving is attributed to this run.

### B. Authority And Continuity

Main at intake: `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`, human merge of #1072. Main's `AGENTS.md` blob is `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; proof contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`. The selector, breadth, complete-return, role, multirun and dynamic policies were retrieved and applicable instructions consumed. `deployment_ack`: active diagnosed repair supersedes the completed finite-telescope bootstrap.

The canonical target remains `VFCanonicalSquareVonKochStatement`: there exists C>=0 such that for every natural R>=2, `|pi(R^2)-VF_can(R^2)| <= C R log R`. The fixed sqrt(2) phase, actual prime carrier, and separate classical von Koch interface are unchanged. Neither this repair nor #1076 proves RH or the sharp-shell energy target. Final main recheck still gives `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`; the report branch has no intervening upstream report after this run's milestone commit.

Continuity was read at report snapshot `7b653e80430662c99565f7b565c99d1e48115e2a`, using America/New_York dates. Today Coordinator is `TODAY=PENDING`; its yesterday mirrors have identical blobs and are `YESTERDAY=CARRY_FORWARD`. Yesterday's last Lean section was PARTIAL, not assumed complete. Relevant mathematical summaries, review verdicts, handoffs and resume sections were consumed; unreviewed claims were not silently accepted.

| Role | November 2 blob | November 3 intake blob |
| --- | --- | --- |
| Coordinator 00/90 | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | PENDING |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | 5c085d12ca455327b2a9ab42d7e55a1b6b2d631b |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 7a167a551ca047c0b5bccf6220f40152d78ea176 |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | ae0ce9040b145c8b2ee04418e02a363d10b5da38 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 09ecf82c4a8d5d36b10ed6d64167d695e096ce03 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | 226a5a6d971f347b45e016a046007bc4ceb368ee |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | This invocation |

External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than October 18. Its historical routes are not current assignment authority. Merged #1070 and #1071 were confirmed, not reimplemented. #1072's tested head `1c134fcc04f4369499d2ca09f8fc66b25e36968c` has 13 successful workflows; dedicated run 41520553305/job 125535156435 contains the successful native non-strict replay/dependency audit. This is exact PR-head evidence for work subsequently merged, not an invented new main build.

### C. Formalization Queue

1. Priority A: #1075's actual final consequence failure, now repaired on its existing authorized branch. No duplicate PR.
2. Ready review: #1076's independently accepted source-calibrated endpoint, unchanged green evidence reused. #1073 acceptance is carried forward from `20261102-referee-3`; #1074 and #1076 from `20261103-referee-1`.
3. Accepted paper candidates: `20261102-coordinator-3` C20-C22/C25 and `20261103-census-2` PC4, accepted with scope in `20261103-referee-3`. They do not supply the missing maximal/frozen covariance rate and did not displace an active valid repair.
4. Pending review, not implementation-ready by assertion alone: Owner `20261103-owner-1` SAT dilation obstruction; Analytic `20261103-analytic-1` NYMAN tail; Wheel `20261103-wheel-1` integer cap; Referee's new certificate-size and squarefree-support obstruction claims. Their stated open suppliers remain open.

### D. Selection And Proof Plan

The failing module already contained a complete valid mathematical argument. For a source fixed before epsilon and n, apply the Mertens growth bound with loss epsilon/2, square its nonnegative sides, use the exact all-pair square identity, and combine powers. Dependencies are the constructed source endpoint, `vf919_mertens_sq_eq_signedPair`, `sq_le_sq₀`, and pinned Mathlib real-power multiplication. Potential issue: explicit `Real.rpow` versus overloaded power notation in rewrite matching. Validation: unchanged dedicated warning-fatal compilation, exact types, axiom/dependency audit, and all attached integration checks on the new head.

### E. Exact Theorem And Original Carrier

In #1075, `slotTilt D=((7/8)*D.rmin)/48=7*D.rmin/384`. The repaired declaration is:

```lean
theorem native_slot_tilt_signed_energy :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ ∀ eps : ℝ, 0 < eps →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
          realMertensDiagonal (x+1) + 2 * realMertensPositiveLagPairSum (x+1) ≤
            C * Real.rpow (x:ℝ) (7/4-2*slotTilt D+eps)
```

The diagonal is the exact sum of mu(n)^2, and the positive-lag term is the signed sum of mu(n)mu(m) over m<n, through x. The site n=0 contributes zero. Their combination is exactly `|M(x)|^2`, not a sum of local shell squares. All original positive and negative pair interactions remain. D is chosen before epsilon, C and x; no scale-dependent saving or unstated quantitative premise is introduced.

The same module certifies `native_slot_tilt_growth_exponent`, `native_slot_tilt_fixed_power`, and `native_slot_tilt_signed_pairs`. The fixed-power corollary spends half the positive tilt; it does not assert an exact-boundary power envelope without epsilon.

### F. Independent Mathematical Audit

The energy implication was checked directly, not inferred from its name. The exponent calculation is `2*(7/8-delta+eps/2)=7/4-2*delta+eps`, with constant C replaced by C^2. Thus this is a quantitative consequence of the existing complete Mertens endpoint, not new independent cancellation. No target-equivalent premise is assumed by the terminal theorem.

The endpoint proof keeps the same compensated physical probe for LOW and HIGH. LOW has exponent `3/16-9*delta+loss`, the signal shift is `-11/16-8*delta`, and fixed-reference HIGH has exponent `7/8+shift-sigma`. The actual Hecke supremum is not redefined. Source construction supplies sigma=12*delta for #1075 (6*delta for #1076), discharging the reserve before character/zero/scale choices. The original native moments, finite exclusions, principal comparison, floor/nonfloor transport, tails and variable-boundary continuation remain in the proof path. The native Mertens transfer uses the exact zeta/Hecke product and existing converse, not a substitution of rational signs for ideal-character coefficients.

This invocation's repair/source audit is SELF_AUDIT, not a new independent Referee run. The independent #1076 acceptance is reused at its exact unchanged head; it is not automatically assigned to every line of #1075.

### G. Lean Implementation And Source Provenance

Only `research/oai_434/VF919SlotAnchoredConsequences.lean` was changed. The repair expands `mul_pow`, normalizes `Real.rpow_eq_pow`, applies `Real.rpow_mul_natCast` with explicit exponent and natural power 2, then closes the exponent equality by ring arithmetic. Exact type prints were added for the pair and energy consequences. No workflow, policy, source definition, import surface, theorem statement or audit was altered.

| Source | Blob SHA |
| --- | --- |
| Consequences before repair | b9b7666f2fd73957d2106ef1c1b22e89560dbfa7 |
| Consequences after repair | 0ef06d7ec94b2dbbc64f30aef3db65255ae59ff4 |
| #1075 source endpoint | b6cce722add0fc0473238523919d021b19db7a83 |
| #1075 physical budgets | cc9c8303b7b76caae25cacfedcf3eac5b043e7e8 |
| #1075 source constructor | 1ec9c6d54fe046150e9c9822bfc511228ac6a4e8 |
| #1075 endpoint audit | 81d6bea7908a9aa8ad4bd38df09a38fb0d232b45 |
| #1075 dedicated workflow | 5a2c2bcfa3c01495b0cde04ee09dee54be8da11b |
| Main exact signed-square bridge | 000016ee47c3ee772bd81c2a4f00a858986b5af1 |
| Main Green-Kubo definitions | 802a58b4e1994a5f8c14f1080ac42d0f5f28a0d5 |
| Main Mertens exponent envelopes | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |
| Main native non-strict replay | ff963b716bc2066c2312d9237764e39898f1cdb8 |
| Pinned Mathlib Pow/Real.lean | 6e3f62550a758e94a1d513133cd744406b319e41 |

Toolchain: Lean 4.34.1, toolchain blob `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, manifest blob `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`; original openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. No local Lean was executed.

### H. Branch And PR State

PR #1075 branch: `agent/lean-verification/slot-anchored-endpoint-20261102`. Repair parent `acaa66c510259a6722e3d5590106fcb9b7d50181`; new commit `c54bce957fa8c49ca944852b3a1b0e143f2d693b`. The update was a checked fast-forward of the unchanged branch head. Its base remains #1073 at `9cbfce5295343bcb411e6d2cb159b59995cd985b`, not main. After actual successful CI, #1075 was marked REVIEW_READY, with the historical failure and fresh evidence preserved in its description. Final readback confirms its unchanged head, non-draft/open/unmerged status, and no auto-merge action.

PR #1076 is REVIEW_READY, open/unmerged, exact head `f676c9b13960f8c80b68bdf35a5f04b07370e228`. Its description now records actual verification instead of leaving only historical pending-CI text. #1073 and #1074 remain unmerged; #1074's branch is outside this agent's routine write lane and was not changed.

Integration risk: #1075 and #1076 overlap in three proof modules and define different slot tilts under the same names. Human integration must choose/reconcile the variants. On the same source, #1076's `7*rmin/192` is twice #1075's `7*rmin/384`; this does not evaluate either existential witness or imply that two independently chosen witnesses have a known ratio. Nothing was merged or enabled for auto-merge.

### I. GitHub Actions Evidence

For repaired #1075, [run 41618470421](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470421), [job 125857764947](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470421/job/125857764947), completed SUCCESS on exact head `c54bce957fa8c49ca944852b3a1b0e143f2d693b` at 10:33:16 UTC. Event: pull_request, attempt 1. The job's actual steps confirm pinned-toolchain checks, no-hole checks, native covariance integration, physical guidepost, complete native replay, and the slot-anchored generation/compilation/audit all passed. Cold-build steps were legitimately skipped on a source-pinned cache hit; they are not represented as newly executed.

The actual consequence log prints the exact four theorem types and only `[propext, Classical.choice, Quot.sound]` for each, including `native_slot_tilt_signed_energy`. No elaboration error or forbidden axiom dependency remains. The three literal `sorryAx` occurrences in the successful full job log are displayed rejection-command patterns, not declaration dependencies. Lake emits existing patched-package/local-change diagnostics; Lean declaration compilation still passes warning-fatal validation.

The two source endpoint audits pass exact quantified type and permitted-axiom checks with 35,316 and 35,695 live value dependencies, requiring the original complete LOW/HIGH suppliers and excluding prior strict-gap endpoints as proof suppliers. Artifact 13223690940 was downloaded and SHA256-checked as `c60d70ca9d97260d27fd234691dafefc664ff497964e23b633ba4f8db9c6e4a1`. Its tracked budget/constructor/endpoint Git blob hashes match section G. Both archived audit logs say PASS. The committed repaired consequence itself was fetched again and is byte-identical to the repaired source, blob `0ef06d7ec94b2dbbc64f30aef3db65255ae59ff4`.

All nine attached workflows remain SUCCESS after marking the PR ready:

| Workflow | Exact-head run | Result |
| --- | --- | --- |
| Complete original proof and slot-anchored extension | [41618470421](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470421) | SUCCESS |
| Public export verification | [41618470464](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470464) | SUCCESS |
| Prevent new cold-only Lean and OpenAI CI | [41618470450](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470450) | SUCCESS |
| Coordinate atlas and static search corpus | [41618470418](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470418) | SUCCESS |
| Documentation checks | [41618470569](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470569) | SUCCESS |
| Targeted Lean iteration | [41618470540](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470540) | SUCCESS |
| Proof inventory | [41618470417](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470417) | SUCCESS |
| Lean source audits | [41618470423](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470423) | SUCCESS |
| Original OpenAI full certified 7/8 covariance integration | [41618470460](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41618470460) | SUCCESS |

For unchanged #1076, all 8 attached workflows passed. Dedicated [run 41579190117](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41579190117), [job 125729734224](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41579190117/job/125729734224), exact endpoint type checks and axiom output were retrieved. The two audits report 35,316 and 35,695 live value dependencies, with only `propext`, `Classical.choice`, `Quot.sound`. Counts are not themselves a proof; the checked types, code and axiom policy are material.

Archived #1076 artifact 13205450942 was downloaded and SHA256-checked: `cbb21d4180886598d3f41bc16096049e8aa0a6e190121fc51cdeb8ab242defb6`. The artifact's budget, constructor and endpoint blobs exactly match `295003535ac11058fc9c966b71c30e96501494e2`, `ae34e670f823bd1139c336bc97c48d22db1f2b45`, and `115d2b19148fa37c329329f153eceea512ade377`. The generated complete HIGH assembly and provenance were inspected. The generation manifest's GENERATED_NOT_VERIFIED label describes generation; the subsequent compile and audit logs establish verification.

For #1073, the unchanged head has 13 successful runs, including 41554561404. #1074 has 7, including 41561947246/job 125674368395; the actual latter log records both source-relative endpoint audits and standard axioms. Their independent acceptance remains the exact scoped Referee verdict, not a new full re-review in this invocation. Source-pinned caches were reused by CI; no claim of a fresh cold rebuild of all upstream mathematics is made.

### J. Failure And Repair Record

Original failed run 41580316113/job 125733356116 stopped at consequence line 68: `rewrite` could not find the power pattern in an expression written with explicit `Real.rpow`. The diagnostic goal was `C^2 * rpow x a ^ 2 = C^2 * rpow x (2*a)`, up to ring normalization. This is a representation-matching failure, not a missing mathematical hypothesis. The failed elaboration printed `sorryAx` for that unresolved declaration, and the batch correctly rejected it. That output was never treated as an accepted proof or repaired by adding a placeholder.

Exactly one proof repair commit was made in this invocation. The baseline LOW/HIGH theorem and all checks were preserved; no no-op commit or rerun of unchanged green #1076 was requested.

### K. Mathematical Conclusions

The repaired consequence retains the complete squarefree diagonal and all signed pairs. It inherits the source-sized Mertens gain, with the correct doubled energy exponent and half-epsilon choice. This is formal completion of existing mathematics, not a newly discovered arithmetic inequality.

`eta_gate: VERIFIED_ETA / PR_HEAD_ONLY` is supported by the independently accepted strict endpoint work, especially unchanged #1076. Main retains the non-strict native 7/8 result. No evaluated positive rational lower bound for rmin, no new sharp-shell gain, no canonical VF estimate, and no RH result are claimed. Protected research portfolios remain distinct.

### L. Formalization-Driven Findings

The compiler failure required normalization, not a strengthened hypothesis. The explicit power proof also confirms the epsilon accounting: squaring a bound with loss eps would cost 2*eps, so the energy statement correctly requests eps/2 upstream. The diagonal is not an error term and is not dropped during conversion.

The stronger #1076 theorem `gate_implies_tilt_le_slotTilt` proves maximality only for its current sufficient finite-slot gate. Repeating the fixed 7/8 reference does not justify subtracting the same tilt a second time. The source-local gate and lower-reference HIGH proof would need genuinely new justified inputs for that improvement.

### M. Mathematical Significance

Formal soundness and significance are separate. Successful exact-head verification certifies the complete original signed prefix consequence. It does not make the equivalent all-pair square an independent source of cancellation, nor does it control a sum of local shell squares. The principal contribution here is removal of an actual verification blocker and delivery of reviewed work for human integration.

### N. Specialist Handoffs

- Coordinator: record the repaired exact head and #1076's review-ready state; retain the overlapping-branch integration warning. Do not count this repair as a second independent eta.
- Referee: unchanged #1076 acceptance is consumed; #1075's narrow power-normalization diff is supplied for review. Optional explicit finite-slot/empty-tuple dependency whitelist hardening remains a nonblocking follow-up, not a newly found false theorem.
- Owner: SAT `20261103-owner-1` is recorded as pending independent review; the R=7 zero-layer dilation falsifier does not constrain the completely restored endpoint by itself.
- Analytic: NYMAN tail claim remains paper/self-audit; its middle residual is unpaid. The verified global Mertens exponent does not supply that norm convergence automatically.
- Wheel: CORR4 W1-W9 and the R=125 local sign witness await independent review; W10 remains an explicit signed supplier, not implied by the integer cap.
- Census: PC4's scoped paper acceptance is consumed. PC5 and the frozen-field covariance rate remain unproved; no repeated or expanded census was performed.

### O. First Unresolved Mathematical Input

No new mathematical premise is needed for the repaired signed-energy conversion. Beyond the verified fixed-source endpoint, a further exponent improvement needs a new independently justified complete LOW/HIGH restriction or a calibrated lower-reference argument with all budgets proved. The existing sufficient gate alone cannot supply it.

For the parallel shell route, the actual signed frozen-field covariance rate and a valid maximal-fragment-to-original-shell comparison remain unpaid; PC5 is conjectural and a generic support/prefix inference is refuted only at its stated comparison-sequence scope. Canonical actual-prime VF and RH remain open. These are mathematical gaps, not renamed compilation failures.

### P. Resume Capsule - Evidence At 2026-11-03 05:36:38 EST

- Selected task: finish `20261102-lean-3` by fixing the actual #1075 consequence failure.
- Proof head: `c54bce957fa8c49ca944852b3a1b0e143f2d693b`; changed blob `0ef06d7ec94b2dbbc64f30aef3db65255ae59ff4`.
- Dedicated run/job: 41618470421 / 125857764947; final evidence recorded in section I.
- State: COMPLETE, nine successful workflows, exact repaired theorem PROVED_IN_LEAN / PR_HEAD_ONLY, ready for review, not merged; no pending build or failed repair remains.
- Review-ready unchanged stronger result: #1076 at `f676c9b13960f8c80b68bdf35a5f04b07370e228`.
- First next action: respond to concrete review/integration findings; preserve source calibration when reconciling #1075/#1076. Reuse unchanged green evidence, do not rebuild for activity.
- Subsequent eligible queue: reviewed maximal-fragment interfaces only if used by a real quantitative argument; await review for today's other new candidates.
- Main/policy freshness and all source hashes must be rechecked at the next actual invocation. No agent, schedule, policy, other report, or main branch was changed.

Publication history: early checkpoint commit `a366fcf7f7d0bd06c98256223ea60baf3f0c0adb` and milestone commit `d95f1ced39fa03b8f1a1f95a44bae313d0851c3f` were committed and read back. Timing correction: the milestone commit is 2026-11-03 10:26:15 UTC / 05:26:15 EST, so its earlier 05:27 heading is corrected to 05:26 in this append. No mathematical history is removed. Final synthesis publication/readback will be recorded in a separate receipt after the write succeeds.

## Publication Receipt - 2026-11-03 05:39:16 EST

**Publication:** PUBLISHED / READBACK_VERIFIED. Final synthesis commit `0fa090ef379c86c03ec7c0df1e3fbd77ae018e47`, report blob `ebeadc6b1ed6ca5030309b1dbd643c4bfe710dd4`, was fetched after publication and matched the submitted content byte for byte at 2026-11-03 10:39:16 UTC. This receipt is appended to that verified report; prior checkpoints, the failed run and the correction history remain present. The invocation is COMPLETE. #1075 and #1076 remain exact-head verified, ready for human review and unmerged. Canonical VF and RH remain open.

## Scheduled Continuation Checkpoint - Claim 20261103-lean-2

**Invocation:** SCHEDULED, 2026-11-03 13:14:01 EST (-0500), America/New_York; RUN_ID_UNAVAILABLE. This is a distinct actual run. Prior results, repair history and publication receipts remain unchanged.

**Execution:** PARTIAL / IN_PROGRESS. Main at intake is `98b1a5a2082a46d9f46d2af191da090365582561`, human merge of #1079. AGENTS blob `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; proof contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`. The canonical actual-prime VF bound and RH remain OPEN.

**Continuity:** retrieved all seven roles' available November 2 and November 3 reports at reporting snapshot `75d76cdd0b19ce5c3e12ba4cb8e74fe28f44b131`, plus external inbox `038018145c0fddb2f6306c0712373adf9cd1ea52`. TODAY=AVAILABLE for all roles; YESTERDAY=CARRY_FORWARD. Relevant sections are being checked. The inbox has no entry after October 18; its historical routing does not override live main.

**Queue and deployment_ack:** both GitHub search and the direct open-PR collection returned no open/draft PRs. The old finite-telescope bootstrap and #1075 repair have been completed in earlier work. The newer independent verdict `20261103-referee-5` accepts Coordinator `20261103-coordinator-1` C29-C30 and Analytic N4 with scope. Select ONE candidate: C29's finite Nyman high-coefficient annihilator and original weighted norm restriction. Inspect the genuine residue basis, Mobius/log divisor identity, endpoints and existing declarations; do not assume the RH-strength boundedness premise. N4 is a fallback with a larger analytic dependency burden. New NR1-NR7, Owner/CORR4/Census claims remain separate pending-review work.

**Operational boundary:** this run's create_file/update_file connector schemas restrict remote file writes to `agent-reports` and dated Lean reports. Proof-source publication is therefore BLOCKED_WRITE_ACCESS through the authorized file-write interface. Lower-level Git tree/ref operations will not be used to evade that restriction. No Lean build has been run, and no new theorem is certified. Continue independent mathematical/source analysis and exact existing CI inspection; report the actionable proof gap and implementation handoff.

**Gate:** prior independently accepted strict Mertens gain is reported as merged by today's Referee. Verify source and exact-head CI before carrying its precise scope forward. No new numerical gain, sharp-shell result, canonical VF bound or RH proof is asserted here.

---

## Scheduled Continuation Synthesis - 20261103-lean-2

Invocation: 2026-11-03 13:14:01 EST (America/New_York); platform run ID not supplied. This is a distinct actual scheduled invocation, not a claimed extra launch. It appends to, and preserves, 20261103-lean-1 and this invocation's early checkpoint. Synthesis timestamp: 2026-11-03 13:39 EST. Main was rechecked and remains `98b1a5a2082a46d9f46d2af191da090365582561`; the open-PR collection is empty.

Execution: `REPORT_COMPLETE / IMPLEMENTATION_PARTIAL_UNCOMPILED / BLOCKED_WRITE_ACCESS`. New proof PR: NONE. New Lean CI: NOT_RUN. No new result is classified PROVED_IN_LEAN. The accepted C29 finite arithmetic proof is mathematically ready; the operational blocker is proof-branch write access, not an unproved finite identity.

### A. Most Important Formal Mathematical Result

The strongest new proof-engineering output is a complete, source-faithful **uncompiled Lean proof attempt for the finite arithmetic core of Coordinator C29**, independently accepted at paper scope in `20261103-referee-5`. The draft derives the high-coefficient invariant from finite divisor sums and the actual Mobius/von-Mangoldt identity, without an approximation-error or RH premise. It is reproduced below for continuation, not offered as certified Lean source.

The paper proof exposes the exact support condition `1 <= m` and `2*m <= H`, where coefficients are fixed through H. The special restriction N=6K is unnecessary for this finite statement. Two exact boundary witnesses show why neither positivity of m nor the coefficient-support condition may be silently dropped. A finite sum-of-squares certificate organizes the accepted factor-16 norm comparison, including overlapping m and 2m indices. The weighted comparison is not yet implemented in Lean.

Existing merged mathematics was separately checked: PR #1079's exact-head dedicated CI, terminal axioms, and archived source blobs match current main. This certifies those existing statements at their stated scope; it does not certify the new Nyman draft or supply an evaluated numerical exponent. Carry forward `VERIFIED_ETA / ON_MAIN` only for the previously independently accepted strict-gap programme scope. New NYMAN gain in this run: NONE.

### B. Current Authoritative Objective

Main: `98b1a5a2082a46d9f46d2af191da090365582561`. Current authority is main, not the reporting branch. The actual-prime canonical objective remains OPEN:

```text
VFCanonicalSquareVonKochStatement:
  exists C : Real, 0 <= C and for every R : Nat, 2 <= R ->
    abs(vfCanonicalSquareDefect R) <= C * R * log R.
```

The canonical sqrt(2) phase is unchanged. The terminal RH consumer additionally requires its explicit `ClassicalVonKochRHCriterion`; neither the criterion nor the required actual bound is supplied by this run. Global Mertens control is not a local shell sum-of-squares theorem.

| Authority or dependency | Blob / pinned revision |
| --- | --- |
| main:AGENTS.md | `9fa5e9519e2fb6dde22217aa2a18982dafef373a` |
| main:CURRENT_PROOF_CONTRACT.md | `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a` |
| Task selector, RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | `d05c327ae694ea54b599dab0a21032a056b521f1` |
| Broad-search-until-eta policy | `b5c063c51556ba57c4b25bcc380a606fa8daa207` |
| Source-faithful complete-return contract | `16838f7f3c8724b970f8b8ece0bceaab9418066d` |
| Seven-agent research engine | `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55` |
| Role prompts | `7366bb71e8a97fd11689a64311c7f590edeb1adf` |
| Dynamic operating protocol | `fe21d2824491fb001726311f736b9825a8f97eca` |
| Multi-run policy | `643cfd596116720a8e5b1efc07a6124b55d70946` |
| Preserved pre-engine AGENTS | `59dc2c6d6ca06b2fae6fe7e18ad4ddf71a21e052` |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| lean-toolchain: Lean 4.34.1 | `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5` |
| lake-manifest.json | `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4` |
| lakefile.lean | `6ef95e9ebf184d5846fee88a9cdf2db3a38afc97` |
| Mathlib revision | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| PrimeNumberTheoremAnd revision | `c39a751132c88b6e8080b74c74023fd95b3d8be0` |
| openai/math revision | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` |

`deployment_ack`: main and the above live policies were consumed. The engine's old NEXT-LEAN odd-Mobius telescope ticket is already implemented: `research/ODD_MOBIUS_FLOOR_TELESCOPE_20261101.lean`, blob `fbe472cca89f757c8f6f25e630a49847a2bd6ad0`. Newer committed Coordinator/Referee handoffs select C29. This run resumed that finite arithmetic derivation and produced actual proof code and exact regression checks; it did not repeat the completed bootstrap or change investigator rotation.

### C. Formalization Candidates And Continuity

Today and yesterday's seven role reports and the external inbox were retrieved. All today's required reports were present: `TODAY=AVAILABLE`; yesterday's verified unchanged material is `YESTERDAY=CARRY_FORWARD`. Intake reporting-branch head: `75d76cdd0b19ce5c3e12ba4cb8e74fe28f44b131`. These are snapshot references, not a claim that other agents cannot append later.

| Role | 2026-11-02 blob | 2026-11-03 intake blob |
| --- | --- | --- |
| Coordinator, 00/90 mirrors | `1e932d4ce0eb0fd2c5f4507f6b111194d633eb32` | `f9c04a1099048cd0b02fd5264b753e916cbcd521` |
| Owner Payment | `abfe546d72b151f4cd200fc61de3197efe23a65c` | `0688ba1d205ac2e846c3c3a55adfc267a6eb6a40` |
| Analytic Type II | `8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73` | `79f5f11020d7038028f4ddfe92ff3f95d4bd0798` |
| Finite Wheel | `abf8ac8c22a708886183849552c90dd62787ac8d` | `15802d31f6b7abf3ffff97a5a57942baf3bc2d07` |
| Prime Census | `2cd84c57ab18d923e97368764f29f4ccd2ec3bb3` | `5b564235ba20bf4a53c13dac0cc91d210d665a84` |
| Adversarial Referee | `814af1684df66e6ac99b8df1f102cb592b316f89` | `dff2382a732be1829ad7583e046ebbc64c61e4c9` |
| Lean Verification | `02d19d792e26f072004cb5909f149538752626e9` | `579d19654925823b5fa2ef849366da2925d2c1b0` |

The Coordinator mirrors have identical directory blob SHAs; one copy was read. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than October 18. Its historical routing does not override live policy; no new external claim changes this selection.

| Priority | Candidate and exact status | Decision |
| --- | --- | --- |
| A | Repair active valid proof PR | None: open/draft PR collection empty at intake and final recheck. Earlier #1075 repair already succeeded; do not duplicate it. |
| B | 20261103-coordinator-1 C29 finite high-coefficient invariant and weighted comparison; independently ACCEPT_WITH_SCOPE in 20261103-referee-5 | Select finite identity first; draft below. |
| B | Same C27-C28 and 20261103-analytic-1 N4/N5, N1-N3/N6-N8 | Accepted paper scope; queued, not implemented in this run. N4 retains full covariance/principal mode. |
| B/E | Same C30, bounded error in stipulated logarithmic-head class implies RH | Accepted conditional paper consequence, not a proved bounded-error supplier and not a cheap substitute for the missing estimate. |
| C/D | 20261103-referee-6/-7 NR1-NR7 | New SELF_AUDIT results, independent review pending. No automatic formal promotion. |
| C | Owner-2 raw ancestry capacity witness; Analytic-2 sharp pair-cap attainment; Wheel-2 moving-admission packet obstruction; Census-3/-4 reserve-credit failures | Relevant new counterexamples read, independent review pending. Preserve original carriers and claim IDs. |

Specific continuity: Owner-1's SAT zero-layer dilation, Owner-2's q=1000000000039/118-composite capacity witness, Analytic-2's R=376 simultaneous q=17/19 positives and 3946/323 pair cap, Wheel-1's CORR4 integer gate and R=125 q=11 credit 10/11, Wheel-2's {2,3} packet with negative indices {10,15,16,22,34}, and Census-3/-4's R=57/59 half-reserve failure are not converted into new global conclusions. Previously accepted C20-C22/C25/PC4 remain structural interfaces without the missing all-scale rate. C32 correctly withdraws the Referee's earlier integral-arithmetic criticism: 1/(3 sqrt(3)) < 1/4. No report history is erased.

### D. Candidate Selection And Proof Plan

C29 is useful because it is an exact theorem on the original residue carrier and isolates what high coefficients cannot change. Its finite proof uses available Mobius divisor identities, unlike a premature formalization of the full analytic C30 implication or N4 large-sieve input. Repository source and PR searches found no existing implementation of this exact Nyman invariant; the paper source itself is not a compiled theorem.

Target: derive the dyadic residual identity for all natural N,H,m with N>=2 and 1<=m, 2m<=H<=N. Dependencies: finite sum interchange, cardinality of multiples in an interval, Mobius divisor sum, and the Mobius-log/von-Mangoldt identity. Missing supporting facts: residue-to-floor transport, support cancellation, and the finite logarithmic floor convolution. Strategy: prove those on the original finite sets, then combine them algebraically. Complications: natural division/coercions, k=1 removal, nonzero log N, exact upper endpoints. Validation required: actual elaborated theorem type and warning-fatal Lean compilation, root/import/export/inventory integration, no-hole scan and terminal axiom closure on the exact proof-PR head. These validation stages remain PENDING.

### E. Exact Theorem Statement

Original source: `research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md`, blob `b2775c892edffe920a101651eef6f3581c73c9d4`. The basis is the actual fractional residue of an integer, not a model for prime membership:

```text
a_k(m) = (m mod k)/k,
r_(N,c)(m) = 1 - sum_(k=2..N) c_k a_k(m),
w_m = 1/[m(m+1)],
c^base_(N,k) = -mu(k) log(N/k)/log N,
psi(m) = sum_(n=1..m) Lambda(n).
```

Here Lambda counts prime powers with weight log p; psi is not pi. All residues and residuals are real; the mod and floor divisions are natural-number operations before coercion.

For N,H,m natural, N>=2, H<=N, m>=1, 2m<=H, and every real coefficient vector c satisfying `c_k=c^base_(N,k)` for 2<=k<=H, the intended theorem is

```text
log N * [r_(N,c)(2m) - 2 r_(N,c)(m)] = 2 psi(m) - psi(2m).
```

There are no constraints on H<k<=N and no norm bound. The draft declaration is `RHLean.Analysis.nyman_high_coefficient_annihilator`; its exact source statement and complete proof attempt appear in Appendix 1. The intended statement is not an observed elaborated type: Lean has not run on it.

Taking H=floor(N/2), X=floor(N/4) recovers the accepted C29 range. More generally, for X natural with 2X<=H, the independently derived paper comparison is

```text
sum_(m=1..X) w_m [2 psi(m)-psi(2m)]^2
  <= 16 (log N)^2 sum_(n=1..2X) w_n r_(N,c)(n)^2.
```

If the full infinite weighted norm E_N is used, its nonnegative omitted terms give the further inequality to 16(log N)^2 E_N. The draft does not implement that weighted or infinite-sum step.

### F. Independent Mathematical Audit

Let b_k(m)=floor(2m/k)-2 floor(m/k). Direct Euclidean division gives b_k(m) in {0,1}, and b_k(m)=0 for k>2m. On the original carrier,

```text
a_k(2m)-2 a_k(m) = -b_k(m),
r(2m)-2r(m) = -1 + sum_(k=2..N) c_k b_k(m).
```

Thus only k<=2m can affect the expression. For m>=1, finite divisor-sum interchange and the identities sum_(d|n) mu(d)=1_(n=1), sum_(d|n) mu(d) log d=-Lambda(n) give

```text
sum_(k=1..m) mu(k) [log N-log k] floor(m/k) = log N + psi(m).
```

When 2m<=N, subtracting twice the m identity from the 2m identity gives the logarithmic-kernel carry sum `-log N + psi(2m)-2psi(m)`. The k=1 carry is zero. Multiplication by the negative coefficient normalization yields exactly E's statement. The original log(N/k) normalization is explicitly transported using positivity of N and k, not silently redefined. There is no circularity, assumed residual bound, imported zero-free conclusion, randomization, or lost multiplicity. Extending beyond N requires the original truncation tail U_N; that extension is not claimed.

The norm comparison has the following exact finite certificate, for any real r on 1..2X:

```text
16 sum_(n=1..2X) w_n r_n^2 - sum_(m=1..X) w_m(r_(2m)-2r_m)^2
 = sum_(m=1..X) w_m(r_(2m)+2r_m)^2 + sum_(n=1..2X) A_n r_n^2,
A_n = 16 w_n - 8*1_(n<=X) w_n - 2*1_(2 divides n) w_(n/2).
```

The last term is interpreted only for even positive n. Each A_n is positive: for n=2m, `w_m/w_(2m)=4-2/(m+1)<4`; odd n have no last subtraction. This retains cross-index overlap rather than asserting orthogonality. It is an implementation-oriented certificate for the already accepted constant 16, not a new claimed sharpness theorem; Referee NR7's new universal-sharpness result still needs separate review.

Exact finite checks used rational arithmetic and coefficient-wise linear forms in formal prime logarithms, not floating tolerances or Lean evaluation. Frozen N set: {2,3,4,6,7,10,11,17}; H in {floor(N/2),N-1,N}; arbitrary rational perturbations above H. Result: 60 logarithmic-floor checks, 63 perturbed-head identity checks, 360 carry checks, 36 square-certificate checks; all passed. These 519 finite regressions do not prove universal quantifiers.

Two excluded-hypothesis witnesses also passed. At N=6,H=3,m=2, changing c_4 by +1 changes the claimed normalized identity by +log 6: m is outside floor(N/4). At m=0 the left side equals -log 6 and the right side is zero. Neither witness refutes C29. The exact reproducer appears in Appendix 2.

### G. Lean Implementation

No repository Lean file changed. Appendix 1 is a local, uncompiled proof attempt with imports `Mathlib` and `RHLean.Analysis.NativePNTMertens`. It contains complete `by` bodies, not placeholders, for residue transport, support invariance, the finite floor/divisor interchange, logarithmic convolution, and the final identity. Static forbidden-token inspection found no sorry/admit/new axiom/native_decide shortcut. This is not a compiler or axiom audit.

The exact existing dependency source `RHLean/Analysis/NativePNTMertens.lean` has blob `090c01e8ac656021a4c88af697a46f5ce7c2f2b3`; inspected lemmas include `nativeCardMultiplesIcc` and `nativeSumMoebiusDivisors`. Pinned Mathlib `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`, blob `f0587555fbb762fc7283a1c22c7f1be07350c589`, supplies `ArithmeticFunction.sum_moebius_mul_log_eq`. These avoid assuming the desired Nyman identity.

Draft SHA256: `6ff21172d4cd01be847d3b86cfd8067f21e7b6fde99886af70d4312929b15ab3`. Exact-regression script SHA256: `0810fbab039a62498a81e8b7f3a50f56237ecbbff5512accfdf79ed971354df3`. Both hashes refer to the appendix payloads with a final newline. Lean syntax/elaboration risks remain until Actions runs. The weighted theorem, root/import integration, inventory and exact-type audit harness are not implemented; the whole C29 package is therefore incomplete.

### H. Proof-Branch And PR Evidence

The live repository authorizes own proof branches, but the current content-write schemas constrain the branch to literal `agent-reports` and are configured for dated Lean reports. This invocation cannot lawfully write Lean source on `agent/lean-verification/...`. Low-level tree/commit/ref tools are not an authorized way around that restriction. Status: `BLOCKED_WRITE_ACCESS`. No proof branch was created, no proof PR opened, no proof commit made, and no CI dispatch or no-op commit attempted.

If proof writes are enabled in a later invocation, create a date-correct scoped branch from freshly checked main, deduplicate first, and publish the finite invariant as a focused draft PR. Do not reuse another agent's branch. The current main SHA is the intended baseline only, not a proof-branch head.

The early report checkpoint was committed as `c36dc43b6fe2d3fc0fcc4622025002f9fb4ccad1`, producing blob `6b562657be954c91b14dab8f5aaca2fbde41c0c6`, and read back exactly. This synthesis is appended using a fresh own-report blob; its final commit/readback is recorded in the user-facing completion, not invented inside the content being committed.

Later merge metadata supersedes earlier same-day status snapshots without erasing their tested evidence:

| PR | Actual relevant head | Merge / disposition |
| --- | --- | --- |
| #1073 | `9cbfce5295343bcb411e6d2cb159b59995cd985b` | main merge `0ac2bcccfc18d3f37d220b2758b29010a1b538c8` |
| #1075 | `c54bce957fa8c49ca944852b3a1b0e143f2d693b` | stacked merge `902d9cc2001413a6376e0bf1fe2e5ebfdfcc7fd4`, later integrated |
| #1076 | `9041df50518bd63f250bf701f849903e27d816b2` | stacked merge `9e7111c84d3452903ff6516562b59adff8a2795f`; this is later than the earlier f676... audit snapshot |
| #1077 | `9e7111c84d3452903ff6516562b59adff8a2795f` | main integration `acffafc79df1a3713e77dcd14eb551b7413d00c2` |
| #1078 | `86780b5683c0f93c9c036b20d1130e3c71b6df12` | main merge `3930d884282dd5315f0453e5dd88b356d187a8e0`; signed prime-window estimate remains OPEN |
| #1079 | `7ff378e3edd971a8d9e2f11fe39db1aef598ba85` | main merge `98b1a5a2082a46d9f46d2af191da090365582561` |
| #1080 | `892b98a8ff07b505f899df4213965f41e5d1f03c` | CLOSED, unmerged draft; no numerical certificate inferred |

### I. GitHub Actions Evidence

Existing proof head: `7ff378e3edd971a8d9e2f11fe39db1aef598ba85`. Dedicated workflow [Native LOW-first slot-calibrated contraction, run 41676598704](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41676598704), attempt 1, event `pull_request`, completed SUCCESS. The actual API head was checked. [Job 126058888532](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41676598704/job/126058888532) logs were read. All 13 workflows on that PR head succeeded, including the targeted Lean iteration, source audits, proof inventory, public exports and related integration checks. The current main has 11 successful push workflows; these are separate evidence, not a substitute for the PR-only dedicated run.

The dedicated run executes pinned builds, source generation, warning-fatal selected compilation and terminal audits. Its actual new terminal axiom output is exactly `[propext, Classical.choice, Quot.sound]` for:

```text
native_beta_le_true_physical_slot_minimum          dependency closure 35334
native_mertens_true_physical_slot_minimum          dependency closure 35713
native_signed_pair_true_physical_slot_minimum      dependency closure 35728
```

The source statements existentially supply positive `actualSlotMinimum D` and the boundary `7/8 - actualSlotMinimum D/24`, with the corresponding Mertens and signed-pair consumers. They do not supply an evaluated rational minimum. `ActualSlotMinAudit.lean` checks dependency/axiom properties; do not attribute the older audit's explicit expected-type parser check to this newer audit. The theorem source types were inspected directly. The unchanged LOW-first audit separately compares its expected terminal types and has closure counts 35316/35695.

Important limitation: the full prerequisite job log contains existing Wiener.lean:325/344 sorry warnings and package warnings. The cold original-analytic build was skipped in favor of pinned caches. It would be false to claim a fresh cold rebuild, a wholly warning-free log or a placeholder-free repository. The audited terminal closures exclude sorryAx; the selected warning-fatal source checks passed. No new local Lean execution, CI rerun or build occurred here.

Artifact `13252645647` was downloaded. Its ZIP SHA256 `f685425546d4a3e49d5bb5aaff5bc65c0c72d117cab1e07547ef780af0b8c877` matches the GitHub artifact digest. All eight tracked files below were hashed from the archive using Git blob hashing and match current main. Six generated anchored modules and the generation manifest were also inspected; generation's `GENERATED_NOT_VERIFIED` label alone is not compilation evidence. The successful subsequent job provides the selected compilation/audit evidence.

| Archived path | Blob SHA, matched to main |
| --- | --- |
| research/oai_434/VF919ActualSlotMinRetighten.lean | `138c4726085995b966204406805f70082402bec4` |
| research/oai_434/VF919LowFirstSlotAnchoredEndpoint.lean | `d9373ce13b703b1e5f4e4bcde158ef9004d250dd` |
| research/oai_434/VF919LowFirstSlotCalibratedData.lean | `950c00c60d8757c7b6cd0dcea19e94d5114ea0ba` |
| research/oai_434/VF919LowFirstPhysicalTiltFullBudget.lean | `0923ee1d78bdea48d494d9993834e1d31638bbda` |
| scripts/lean/slot_anchored/ActualSlotMinAudit.lean | `c7d04f7556563b2f83d88ff5eef6021148b980db` |
| scripts/lean/slot_anchored/SlotAnchoredAudit.lean | `b99ae97aa3ccb862f71ce7e08694b130350a1f5a` |
| scripts/lean/slot_anchored/prepare_anchored.py | `0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725` |
| scripts/lean/slot_anchored/run_anchored_in_verified_ci.sh | `513e9c81925ad87e7230017e266bb11bd2560623` |

Workflow blob: `ff76063794861d083358b919aabe5340098964ce`. Native strict Mertens source blob: `b33a4883e1ddb0551b0f11f062bce46680d87450`. This existing source goes through the actual zero/Hecke/Mertens-converse chain; no canonical VF phase substitution was introduced. Its independent accepted scope is carried forward, not re-proved from the Nyman identity.

### J. CI Failures And Repairs

No active failed proof PR was found. The earlier 20261103-lean-1 #1075 real-power repair is preserved and now integrated; no redundant repair or rerun was made. The Nyman draft has no compiler output to diagnose. Manual proof construction is not successful elaboration. The new task is blocked before PR publication, not `BLOCKED_CI_NOT_TRIGGERED` from a draft workflow that actually failed to start.

A narrow source audit also addresses Coordinator's optional gate-liveness hardening suggestion. `VF919TiltedLowPhysical.lean:351` constructs the live empty/nonempty selected-slot gate directly inside `low_selected_nominal_energy_tilted`, using `Finset.single_le_sum` and hgap. Thus requiring the generic declaration `finite_slot_gate` by name could reject an equivalent valid inline proof. `VF919TiltedLowReflection.lean:1123` does directly call `empty_active_tuple_dyad_width` in the empty branch. The existing whitelist includes `low_original_completed_energy_tilted`, but does not explicitly require either helper. Successful printed axioms for a helper alone do not establish its terminal liveness. No CI policy or whitelist was changed; no failure is alleged. Any future permitted hardening should follow the actual caller and empty branch, not an assumed helper name.

### K. Mathematical Conclusions

Formal soundness: existing #1079 results have actual exact-head CI and matched archived source evidence. New C29 draft: NOT_FORMALLY_VERIFIED. The accepted underlying finite paper theorem is independently justified; its N,H generalization and explicit boundary analysis here are SELF_AUDIT, not a new independent Referee verdict.

Mathematical content: **structural control** of the exact dyadic residual and an already accepted **quantitative comparison**, not a bound on E_N. It is an **obstruction** to treating arbitrary high-modulus changes as changing this low-range invariant. It is not an impossibility theorem for unrestricted full-basis approximation. It supplies no positive eta, no new local sharp-shell estimate, no all-scale covariance bound and no canonical or RH closure.

### L. Formalization-Driven Discoveries

The proof needs only 2m<=H<=N, not N divisible by six. It needs m>=1 because the Mobius divisor indicator contributes its initial constant only on a positive interval. Coefficients above 2m are exactly annihilated by the dyadic carry; extending even one relevant modulus can change the invariant. The original log-ratio coefficient can be transported to a difference of logs under explicit nonzero arguments. The factor-16 estimate admits a finite positive remainder certificate while preserving overlapping indices. These are useful implementation facts; no claim of priority over the already read Referee analysis is made.

### M. Mathematical Significance

The draft gives the Nyman route a faithful finite certification target and prevents a false interpretation of high-modulus repair. It neither solves the full weighted approximation problem nor substitutes the missing estimate with a hypothesis. The finite invariant is not target-equivalent by itself. In contrast, the independently accepted C30 implication says that a uniformly bounded E_N for all sufficiently large N=6K in this fixed logarithmic-head class already implies RH; the reverse implication was not established there. A finite numerical scan cannot supply that premise.

### N. Specialist Handoffs

| Recipient | Precise handoff |
| --- | --- |
| Proof Architect | Keep C29 accepted at paper scope and code UNCOMPILED. Queue its finite invariant first when proof writes are available. Preserve VERIFIED_ETA / ON_MAIN only at inherited accepted scope; do not recategorize it as a new NYMAN gain. |
| Owner Payment | None of the Nyman residues is a once-only owner slot or frozen historical coefficient. Preserve the raw ancestry counterexample and request its independent review before any owner-source formalization. |
| Analytic Type II | The fixed low coefficients force the exact dyadic defect on 2m<=H. N4's accepted complete remote tail still leaves the growing middle norm uncontrolled. State any proposed supplier uniformly with all cutoffs and correction terms. |
| Finite Wheel | The {2,3} packet admission and CORR4 credit results remain different carriers. Do not transport the constant-16 norm comparison to wheel cells without an explicit source map. |
| Prime Census | Existing finite credit failures remain obstructions to that supplier, not a global counterexample. The exact Nyman tests here are fixed regression witnesses only; no enlarged scan is requested. |
| Adversarial Referee | Original C29 acceptance reused. Please distinguish the H-generalized finite statement and endpoint witnesses (this run's SELF_AUDIT) from accepted C29 and your own NR1-NR7 pending independent review. No new analytic/RH implication is claimed. |

### O. First Unresolved Mathematical Theorem

There is no unresolved mathematical gap in the finite carry/divisor argument above. Its immediate blocker is operational publication and subsequent formal verification. The missing mathematical supplier for the larger corrected Nyman family is control of its growing middle region in the original weighted norm, uniformly with the chosen coefficients and growing cutoff. Schematically the needed conclusion is

```text
sum_(m=1..T_N) [1 - sum_(k=2..N) c_(N,k) (m mod k)/k]^2 / [m(m+1)] -> 0,
```

with T_N and coefficients tied to the proved remote-tail bounds, retaining any separately treated head. The accepted remote-tail estimate does not imply this. For the stipulated logarithmic head, even a uniform bound for the complete norm at all sufficiently large N=6K is already the RH-strength supplier identified by C30. The canonical actual-prime square-clock estimate and any local-shell comparison required to recover it remain separately OPEN.

### P. Next-Run Resume Capsule

```text
CLAIM: 20261103-lean-2
INVOCATION: 2026-11-03 13:14:01 EST; platform run ID unavailable
RESUME_WRITTEN_AT: 2026-11-03 13:39 EST
REPORT: complete synthesis appended after early PARTIAL checkpoint
MAIN: 98b1a5a2082a46d9f46d2af191da090365582561, unchanged at final recheck
AUTHORITY: AGENTS 9fa5e9519e2fb6dde22217aa2a18982dafef373a
CONTRACT: 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a
TASK: accepted C29 finite arithmetic identity, not full C30 or N4
MATHEMATICS: C29 PAPER_PROOF / ACCEPT_WITH_SCOPE; generalized H statement SELF_AUDIT
CODE: Appendix 1, complete uncompiled identity proof attempt; weighted Lean theorem pending
CODE_SHA256: 6ff21172d4cd01be847d3b86cfd8067f21e7b6fde99886af70d4312929b15ab3
TESTS: Appendix 2; 519 exact finite checks and two excluded-hypothesis witnesses passed
PR: none created; final open/draft collection empty
BLOCKER: BLOCKED_WRITE_ACCESS; content writes permit agent-reports only
NEW_CI: NOT_RUN; no local Lean execution; no source or audit certification of draft
EXISTING_CI: #1079 head 7ff378e3edd971a8d9e2f11fe39db1aef598ba85
RUN: https://github.com/OVVO-Financial/RH_Lean/actions/runs/41676598704
JOB: https://github.com/OVVO-Financial/RH_Lean/actions/runs/41676598704/job/126058888532
ARTIFACT: 13252645647, digest and eight tracked main source blobs matched
GATE: inherited VERIFIED_ETA / ON_MAIN only at previously accepted strict-gap scope
NEW_GAIN: none; canonical actual-prime estimate and RH remain open
NEXT: refresh authority/access/PR state; if proof writes are available, implement the
      appendix on an own date-correct branch, integrate required proof surfaces,
      open draft PR, inspect exact-head Actions, and repair actual diagnostics.
      Add the finite weighted certificate as the next scoped theorem if suitable.
AVOID: no low-level write bypass, no duplicate telescope, no re-run of unchanged green
       CI, no assumption that uncompiled draft has elaborated, no full-norm claim.
```

### Appendix 1. Complete Uncompiled Lean Proof Attempt

The following code is preserved as an implementation handoff inside this report. It is not a Lean module on main or a proof PR. The `#check` and `#print axioms` commands are proposed checks and were not executed. Hash and status are recorded in G/P.

```lean
import Mathlib
import RHLean.Analysis.NativePNTMertens

/-!
UNVERIFIED PROOF DRAFT. No Lean execution has been performed on this file.

Finite arithmetic core of Coordinator C29, accepted with scope in
20261103-referee-5. The residue carrier is the original Nyman carrier.
The final theorem does not assume an error bound or an RH-strength premise.
The weighted norm comparison and analytic RH consequence are not implemented.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanResidue (k m : Nat) : Real := (m % k : Nat) / (k : Real)

def nymanResidual (N : Nat) (c : Nat -> Real) (m : Nat) : Real :=
  1 - sum (Icc 2 N) (fun k => c k * nymanResidue k m)

def nymanLogKernel (N k : Nat) : Real :=
  (ArithmeticFunction.moebius k : Real) *
    (Real.log (N : Real) - Real.log (k : Real))

def nymanLogCoefficient (N k : Nat) : Real :=
  -nymanLogKernel N k / Real.log (N : Real)

def nymanPsi (m : Nat) : Real :=
  sum (Icc 1 m) (fun n => ArithmeticFunction.vonMangoldt n)

def nymanCarry (k m : Nat) : Real :=
  ((2 * m / k : Nat) : Real) - 2 * ((m / k : Nat) : Real)

theorem nymanLogCoefficient_eq_original
    (N k : Nat) (hN : 2 <= N) (hk : 1 <= k) :
    nymanLogCoefficient N k =
      -(ArithmeticFunction.moebius k : Real) *
        Real.log ((N : Real) / (k : Real)) / Real.log (N : Real) := by
  have hNz : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hkz : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [Real.log_div hNz hkz]
  unfold nymanLogCoefficient nymanLogKernel
  ring

theorem nymanResidue_eq_div_sub_floor (k m : Nat) (hk : 1 <= k) :
    nymanResidue k m =
      (m : Real) / (k : Real) - ((m / k : Nat) : Real) := by
  have hkz : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hmod : ((m % k : Nat) : Real) +
      (k : Real) * ((m / k : Nat) : Real) = (m : Real) := by
    exact_mod_cast Nat.mod_add_div m k
  unfold nymanResidue
  field_simp [hkz]
  nlinarith only [hmod]

theorem nymanResidue_dyadic (k m : Nat) (hk : 1 <= k) :
    nymanResidue k (2 * m) - 2 * nymanResidue k m =
      -nymanCarry k m := by
  rw [nymanResidue_eq_div_sub_floor k (2 * m) hk,
    nymanResidue_eq_div_sub_floor k m hk]
  unfold nymanCarry
  push_cast
  ring

theorem nymanCarry_eq_zero_of_lt (k m : Nat) (h : 2 * m < k) :
    nymanCarry k m = 0 := by
  have hm : m < k := by omega
  simp [nymanCarry, Nat.div_eq_of_lt h, Nat.div_eq_of_lt hm]

theorem nymanResidual_dyadic_eq_carry (N m : Nat) (c : Nat -> Real) :
    nymanResidual N c (2 * m) - 2 * nymanResidual N c m =
      -1 + sum (Icc 2 N) (fun k => c k * nymanCarry k m) := by
  have hsum :
      sum (Icc 2 N) (fun k => c k * nymanCarry k m) =
        2 * sum (Icc 2 N) (fun k => c k * nymanResidue k m) -
          sum (Icc 2 N) (fun k => c k * nymanResidue k (2 * m)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hd := nymanResidue_dyadic k m (by
      have := (Finset.mem_Icc.mp hk).1
      omega)
    nlinarith only [congrArg (fun z : Real => c k * z) hd]
  unfold nymanResidual
  rw [hsum]
  ring

theorem nymanResidual_dyadic_congr_low
    (N H m : Nat) (c b : Nat -> Real) (hm : 2 * m <= H)
    (hlow : ∀ k, k ∈ Icc 2 N -> k <= H -> c k = b k) :
    nymanResidual N c (2 * m) - 2 * nymanResidual N c m =
      nymanResidual N b (2 * m) - 2 * nymanResidual N b m := by
  rw [nymanResidual_dyadic_eq_carry, nymanResidual_dyadic_eq_carry]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkH : k <= H
  · rw [hlow k hk hkH]
  · rw [nymanCarry_eq_zero_of_lt k m (by omega)]
    simp

theorem nyman_sum_mul_floor_eq_divisor_sum (A : Nat) (f : Nat -> Real) :
    sum (Icc 1 A) (fun d => f d * ((A / d : Nat) : Real)) =
      sum (Icc 1 A) (fun n => sum n.divisors f) := by
  classical
  have key : ∀ d : Nat,
      f d * ((A / d : Nat) : Real) =
        sum (Icc 1 A) (fun n => if d ∣ n then f d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, nativeCardMultiplesIcc]
    ring
  calc
    _ = sum (Icc 1 A) (fun d =>
        sum (Icc 1 A) (fun n => if d ∣ n then f d else 0)) :=
      Finset.sum_congr rfl (fun d _ => key d)
    _ = sum (Icc 1 A) (fun n =>
        sum (Icc 1 A) (fun d => if d ∣ n then f d else 0)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [<- Finset.sum_filter]
      apply Finset.sum_congr
      · ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨hd, hdiv⟩
          exact ⟨hdiv, by have := Finset.mem_Icc.mp hn; omega⟩
        · rintro ⟨hdiv, hn0⟩
          have hnpos : 0 < n := by have := Finset.mem_Icc.mp hn; omega
          have hdpos := Nat.pos_of_dvd_of_pos hdiv hnpos
          have hdle := Nat.le_of_dvd hnpos hdiv
          exact ⟨⟨hdpos, by have := Finset.mem_Icc.mp hn; omega⟩, hdiv⟩
      · intro d hd
        rfl

theorem nymanLogKernel_divisor_sum (N n : Nat) (hn : 1 <= n) :
    sum n.divisors (nymanLogKernel N) =
      Real.log (N : Real) * (if n = 1 then 1 else 0) +
        ArithmeticFunction.vonMangoldt n := by
  have hmu : sum n.divisors (fun d => (ArithmeticFunction.moebius d : Real)) =
      if n = 1 then 1 else 0 := by
    exact_mod_cast nativeSumMoebiusDivisors n hn
  have hlog := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  change sum n.divisors (fun d =>
    (ArithmeticFunction.moebius d : Real) * Real.log (d : Real)) =
      -ArithmeticFunction.vonMangoldt n at hlog
  simp only [nymanLogKernel, mul_sub, Finset.sum_sub_distrib]
  rw [<- Finset.sum_mul, hmu, hlog]
  ring

theorem nymanLogKernel_floor_sum (N m : Nat) (hm : 1 <= m) (hmN : m <= N) :
    sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) =
      Real.log (N : Real) + nymanPsi m := by
  have hsub : Icc 1 m ⊆ Icc 1 N := by
    intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hmN⟩
  have hrestrict :
      sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) =
        sum (Icc 1 m) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkN hkm
    have hmk : m < k := by
      simp only [Finset.mem_Icc] at hkN hkm
      omega
    simp [Nat.div_eq_of_lt hmk]
  rw [hrestrict, nyman_sum_mul_floor_eq_divisor_sum]
  have hsum :
      sum (Icc 1 m) (fun n => sum n.divisors (nymanLogKernel N)) =
        sum (Icc 1 m) (fun n =>
          Real.log (N : Real) * (if n = 1 then 1 else 0) +
            ArithmeticFunction.vonMangoldt n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact nymanLogKernel_divisor_sum N n (Finset.mem_Icc.mp hn).1
  rw [hsum, Finset.sum_add_distrib, <- Finset.mul_sum]
  simp [nymanPsi, Finset.sum_ite_eq', Finset.mem_Icc, hm]

theorem nymanLogKernel_carry_sum (N m : Nat) (hm : 1 <= m)
    (hmN : 2 * m <= N) :
    sum (Icc 2 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
      -Real.log (N : Real) + nymanPsi (2 * m) - 2 * nymanPsi m := by
  have hsub : Icc 2 N ⊆ Icc 1 N := by
    intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hsame :
      sum (Icc 2 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
        sum (Icc 1 N) (fun k => nymanLogKernel N k * nymanCarry k m) := by
    apply Finset.sum_subset hsub
    intro k hk hnot
    have hk1 : k = 1 := by
      simp only [Finset.mem_Icc] at hk hnot
      omega
    subst k
    simp [nymanCarry]
  rw [hsame]
  have hsplit :
      sum (Icc 1 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
        sum (Icc 1 N) (fun k => nymanLogKernel N k * ((2 * m / k : Nat) : Real)) -
          2 * sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold nymanCarry
    ring
  rw [hsplit, nymanLogKernel_floor_sum N (2 * m) (by omega) hmN,
    nymanLogKernel_floor_sum N m hm (by omega)]
  ring

theorem nymanLogCoefficient_dyadic (N m : Nat) (hN : 2 <= N)
    (hm : 1 <= m) (hmN : 2 * m <= N) :
    Real.log (N : Real) *
      (nymanResidual N (nymanLogCoefficient N) (2 * m) -
        2 * nymanResidual N (nymanLogCoefficient N) m) =
      2 * nymanPsi m - nymanPsi (2 * m) := by
  have hL : Real.log (N : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [nymanResidual_dyadic_eq_carry, mul_add, Finset.mul_sum]
  have hterm : ∀ k : Nat,
      Real.log (N : Real) * (nymanLogCoefficient N k * nymanCarry k m) =
        -(nymanLogKernel N k * nymanCarry k m) := by
    intro k
    unfold nymanLogCoefficient
    field_simp [hL] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib,
    nymanLogKernel_carry_sum N m hm hmN]
  ring

theorem nyman_high_coefficient_annihilator
    (N H m : Nat) (c : Nat -> Real) (hN : 2 <= N) (hHN : H <= N)
    (hm : 1 <= m) (hmH : 2 * m <= H)
    (hlow : ∀ k, k ∈ Icc 2 N -> k <= H ->
      c k = nymanLogCoefficient N k) :
    Real.log (N : Real) *
      (nymanResidual N c (2 * m) - 2 * nymanResidual N c m) =
      2 * nymanPsi m - nymanPsi (2 * m) := by
  rw [nymanResidual_dyadic_congr_low N H m c (nymanLogCoefficient N) hmH hlow]
  exact nymanLogCoefficient_dyadic N m hN hm (hmH.trans hHN)

#check nyman_high_coefficient_annihilator
#print axioms nyman_high_coefficient_annihilator

end RHLean.Analysis
```

### Appendix 2. Exact Finite Regression Reproducer

This standard-library Python program executed successfully in this invocation. It is not Lean compilation or a proof of the universal theorem. Its exact result is reported in F; its hash is recorded in G.

```python
"""Exact finite regressions for the uncompiled C29 proof draft.

Linear forms in formal prime logarithms are compared coefficient by coefficient.
These tests neither execute Lean nor certify an infinite theorem.
"""

from fractions import Fraction as Q
from collections import Counter
import json


def factors(n):
    out = Counter()
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] += 1
            n //= p
        p += 1
    if n > 1:
        out[n] += 1
    return out


def mu(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def clean(a):
    return {p: Q(v) for p, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for p, v in b.items():
        out[p] = out.get(p, Q(0)) + v
    return clean(out)


def scale(c, a):
    return clean({p: Q(c) * v for p, v in a.items()})


def minus(a, b):
    return add(a, scale(-1, b))


def logform(n):
    assert n >= 1
    return clean(factors(n))


def psi(m):
    out = {}
    for n in range(2, m + 1):
        f = factors(n)
        if len(f) == 1:
            out = add(out, {next(iter(f)): Q(1)})
    return out


def scaled_residual(n, delta, m):
    length = logform(n)
    out = dict(length)
    for k in range(2, n + 1):
        lc = add(scale(-mu(k), minus(length, logform(k))),
                 scale(delta.get(k, 0), length))
        out = minus(out, scale(Q(m % k, k), lc))
    return out


def kernel_floor(n, m):
    out = {}
    for k in range(1, n + 1):
        out = add(out, scale(mu(k) * (m // k),
                             minus(logform(n), logform(k))))
    return out


def weight(m):
    assert m >= 1
    return Q(1, m * (m + 1))


def run():
    # Frozen before execution: odd/even, non-sixfold, and smallest cutoffs.
    cutoffs = (2, 3, 4, 6, 7, 10, 11, 17)
    floor_checks = 0
    invariant_checks = 0
    for n in cutoffs:
        for m in range(1, n + 1):
            assert kernel_floor(n, m) == add(logform(n), psi(m))
            floor_checks += 1
        for h in sorted({n // 2, n - 1, n}):
            delta = {k: Q((-1) ** k * (k + 1), k + 2)
                     for k in range(h + 1, n + 1) if k >= 2}
            for m in range(1, h // 2 + 1):
                left = minus(scaled_residual(n, delta, 2 * m),
                             scale(2, scaled_residual(n, delta, m)))
                right = minus(scale(2, psi(m)), psi(2 * m))
                assert left == right
                invariant_checks += 1

    # These are counterexamples to removing stated hypotheses, not to C29.
    n, m = 6, 2
    changed = minus(scaled_residual(n, {4: Q(1)}, 2 * m),
                    scale(2, scaled_residual(n, {4: Q(1)}, m)))
    target = minus(scale(2, psi(m)), psi(2 * m))
    assert minus(changed, target) == logform(6)
    zero = minus(scaled_residual(6, {}, 0),
                 scale(2, scaled_residual(6, {}, 0)))
    assert zero == scale(-1, logform(6))

    carry_checks = 0
    for m in range(0, 18):
        for k in range(1, 2 * m + 4):
            carry = (2 * m) // k - 2 * (m // k)
            assert carry in (0, 1)
            assert Q((2 * m) % k, k) - 2 * Q(m % k, k) == -carry
            if 2 * m < k:
                assert carry == 0
            carry_checks += 1

    # Check the exact sum-of-squares certificate, including overlap of m and 2m.
    energy_checks = 0
    for x in range(1, 13):
        for seed in range(3):
            r = {n: Q(((n * n + 3 * seed * n + seed) % 13) - 6, n + 1)
                 for n in range(1, 2 * x + 1)}
            energy = sum(weight(n) * r[n] ** 2 for n in r)
            dyadic = sum(weight(m) * (r[2 * m] - 2 * r[m]) ** 2
                         for m in range(1, x + 1))
            certificate = sum(weight(m) * (r[2 * m] + 2 * r[m]) ** 2
                              for m in range(1, x + 1))
            for n in r:
                coefficient = 16 * weight(n)
                if n <= x:
                    coefficient -= 8 * weight(n)
                if n % 2 == 0:
                    coefficient -= 2 * weight(n // 2)
                assert coefficient > 0
                certificate += coefficient * r[n] ** 2
            assert certificate == 16 * energy - dyadic
            assert dyadic <= 16 * energy
            energy_checks += 1
    print(json.dumps({
        "status": "PASS_EXACT_FINITE_REGRESSIONS_NOT_LEAN",
        "cutoffs": cutoffs,
        "mobius_log_floor_checks": floor_checks,
        "arbitrary_high_coefficient_invariant_checks": invariant_checks,
        "residue_carry_checks": carry_checks,
        "weighted_square_certificate_checks": energy_checks,
        "excluded_endpoint_defect_N6_m2_delta4_1": "log(6)",
        "zero_index_defect_N6": "-log(6)",
    }, indent=2))


if __name__ == "__main__":
    run()
```
