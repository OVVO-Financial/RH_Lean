# Semantic proof-integrity audit (2026-11-24)

This PR extends the merged #1202 reporting repair with a repository-wide candidate census. It pins main `9f84aae95729d566d4aa7189584620fbd0e1099a`, final-proof PR #1201 `92f46c80a678df7f05f4741437068b51607b643c` and supplier PR #1208 `b8e18c7c195537f5775273807e5b693f25896223`. Every tracked Lean source is included, including exports, research and scripts. Duplicate sources are counted separately by path and also by SHA-256. Lexical hits are review leads only, not proof defects; neither a clean scan nor a clean axiom list establishes mathematical independence. No Lean statement is weakened or deleted.

## Concrete inspected risks

- `RHLean/Proof/RiemannHypothesisBridge.lean`: `ActualStartRHBridge.pointwiseSquareBounded_to_riemannHypothesis` is itself a field that must be independently supplied. The old final composition theorem assumes this bridge. Correct conditional result, never an unconditional proof.
- `RHLean/Analysis/AlpogeNativeZetaWindowWitness.lean`: the raw witness permits arbitrary inertia/Frobenius/ell and has the quantitative `top` field. Its bridge module explicitly documents the degenerate specialization. Do not count a witness assembled by assuming its top field as supplying that field.
- `RHLean/Analysis/AlpogeNativeBoundHandoff.lean`: the original finite prime-power formula and the explicit window assumptions are distinct. All RH consumers take those assumptions. The epsilon-window implication requires a strictly positive epsilon range. Correct conditional transport.
- #1201 `NativeExistingRecoveryPayment.lean`: the principal cyclic source identity is an exact arithmetic identity. The window theorem assumes the entire quantified upstream bound, and the mean-loss theorem assumes eleven geometric premises and the physical size windows. The DIV lemma assumes the independent degree inequality. None are a supplier of the assumed bounds.
- #1206 positive-moment route: its unconditional exponent-one estimate is distinct from its conditional critical moment implication. Preserve this distinction.
- `scripts/proofq.py`: previously describes the graph's proved label as unconditional or depending only on proved propositions, despite source-derived hard-blocked inputs and hidden telescope limitations. The CLI now explicitly states that status labels are graph candidates, not unconditional certification.

## Mandatory terminal acceptance

The final proof must be a closed proof of Mathlib's literal root `RiemannHypothesis`, with no free or implicit RH-strength hypothesis. Audit all premise constructors on the same physical data, actual period/rank/mass/height, source equality with literal Lambda and centering, uniform choices before scale, nonempty windows, and transitive permitted axioms. A full Lean source census is not a full semantic proof review. Every high-risk witness must be traced to actual independent constructions; legitimate definitional identities and conditional theorems are retained and labelled accordingly.

The hosted workflow scans the three pinned snapshots and the PR's current checkout. Results and individual candidate locations are uploaded as JSON; no claim of completed hosted execution is made until readback. Future Lean PRs get the inexpensive census, independently of the Lean build.

## Hosted initial census (run 45400959036, exact pins above)

All three pinned jobs read every tracked Lean source with zero scan failures:

| Snapshot | Files read | Unique file contents | Lines | Parsed declarations | Geometric reflexive review | Direct RH return with visible premises |
|---|---:|---:|---:|---:|---:|---:|
| main | 3365 | 3087 | 842614 | 43917 | 136 | 191 |
| #1201 | 3584 | 3306 | 894635 | 47246 | 237 | 191 |
| #1208 | 3584 | 3306 | 894643 | 47246 | 237 | 191 |

No literal constant-True/False definition, root RH shadow, or apparently closed direct RH return matched the initial detector. This is limited lexical evidence. The trust-escape candidate count was 341/344/344, mostly finite computation such as native_decide; these are not all axioms or defects. Individual hits and full paths are in the hosted JSON artifacts.

A confirmed literal reflexive theorem occurred in three copies of FixedPackets.lean: packet_horizon_independent has two unused horizon arguments and concludes packet x u M = packet x u M. GitHub indexed code search found only those definitions. Removed the theorem from all three copies; the packet definition and the substantive concatenation/energy lemmas remain. Historical commits remain unchanged. Hosted compilation and exact tracked-reference check are needed on the removal commit.

The original self-premise scan also flagged long OAI statements where a let type contained arrows; source inspection showed these are parser false positives, not self-assumptions. Refined the detector to restrict literal self-premise detection to simple raw conclusions, and distinguish a False conclusion from a False premise. The single new degenerate geometry candidate in #1201/#1208 is a restriction to the top open W in NativeCMSchemeRetract.lean:189, not a fabricated geometric host. The examined rank_lt_height assignment in CanonicalGapAncestryBridge.lean is the projection of a genuine bounded source subtype, with a separate strict parent-rank proof. rescaleCovol is an alias of a named covolume formula theorem, not a height assignment.

## Kernel-type audit extension

The previously merged graph still uses source-parsed hypothesis positions even when ingesting kernel dependency edges. Section variables and implicit parameters can be missed. The revised exporter reads the outer Pi domains directly from each compiled declaration's type. Only literal monomorphic named propositions can seed name-based closure; universe-polymorphic or complex arguments remain unclassified rather than merged by identifier. Legacy/synthetic records retain source-candidate status, explicitly not kernel-type evidence. Regression fixtures cover hidden section assumptions, external/opaque inputs, universe blocking, valid seed propagation and the exact direct RH consumer.

The hosted build now checks the exact Mathlib root RiemannHypothesis return type on every exported kernel constant. An unexpected closed exact root candidate stops the open-phase audit for independent review; it does not automatically mark RH proved. That guard must be replaced by a pinned exact final theorem and its independent transitive axiom/semantic acceptance checks in the final proof PR. No source parser or kernel type shape can establish the meaning of a geometry model; the supplier-by-supplier review remains required.

Second-commit Python and Lean hosted verification is pending. The initial hosted full-source census is complete, not a claim that every candidate has been semantically cleared.
