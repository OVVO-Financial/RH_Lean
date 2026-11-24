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
