# Established baseline, exact consumer, genuinely new arithmetic

**PAID_BASELINE_EXACT_CONSUMER_V1 - 2026-11-06. Effective after reviewed human merge.**

This is a correction to research starting points and gain accounting, not a new theorem or a new single-route campaign. It complements [NO_PIGEONHOLING_ROUTE_SELECTOR_V1](RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md), which continues to govern independent route selection and protected rotation. Conflicting historical instructions to reconstruct the already supplied 1-to-7/8 argument, or to require a sharp square-shell norm from every route, are superseded. Their genuine source qualifications and counterexamples remain valid.

## 1. Start from the arithmetic already proved

The existing native replay is not merely an assumed terminal 7/8 bound. It assembles the original analytic suppliers, native source moments, the same compensated LOW/HIGH probe, and the final zero-supremum argument. Its all-prefix covariance consequence is an established result of that chain, even though its final transport uses nonvanishing and the Mertens converse. Do not call that consequence absent merely because the proof is not a direct rational-Mobius pair estimate. Equally, do not call reuse of the original analytic suppliers an independent reproof of all of them.

Source inspected for this correction: RH_Lean main `4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a`; original OAI pin `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. This documentation change does not claim a fresh Lean build. Preserve existing exact-head proof evidence; recheck affected dependencies when their source or hypotheses actually change.

For the genuine coefficients, define

```text
D(N) = sum_(1<=n<=N) mu(n)^2,
C(N) = sum_(1<=m<n<=N) mu(m)mu(n),
D(N) + 2 C(N) = M(N)^2.

For every epsilon>0 there is A_epsilon>=0, independent of N, such that
for every integer N>=1:
  D(N) + 2 C(N) <= A_epsilon N^(7/4+epsilon),
  [D(N) + 2 C(N)]/N^2 <= A_epsilon N^(-1/4+epsilon).
```

The precise declarations are in [VF919NativeSevenEighthsReplay.lean](../research/oai_434/VF919NativeSevenEighthsReplay.lean), blob `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` at the inspected main:

- `native_uniform_fixed_source_moments`, `native_uniform_common_probe`, `native_beta_le_seven_eighths`;
- `nativeReplay_signed_covariance`, `nativeReplay_mertens_growth`;
- `nativeReplay_signed_energy_seven_fourths`, `nativeReplay_normalized_signed_energy`;
- `nativeReplay_all_square_blocks`, which retains cross-block terms inside the square.

The existing strict-gap and constructed-slot declarations in [VF919NativeStrictMertens.lean](../research/oai_434/VF919NativeStrictMertens.lean), [VF919SlotAnchoredConsequences.lean](../research/oai_434/VF919SlotAnchoredConsequences.lean), and [VF919ExplicitFixedSourceSlotCount.lean](../research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) are separate established baseline claims at their actual scopes. In particular, the fixed-count theorem states `HeckeZeroSupremum.beta <= 7/8 - 1/(288*explicitSlotCount)`. Do not erase an existing positive gap, recount it as a new agent discovery, assert an unevaluated decimal, or optimize its astronomical denominator as the default task. Distinguish a growth exponent with every positive loss from a fixed no-loss power envelope; spending part of a gap changes the certificate.

The open goal is a **new** source-faithful arithmetic strengthening, a stronger complete exponent relative to the best applicable existing bound, or RH itself. The canonical actual-prime VF estimate remains open. The global signed-pair theorem does not automatically prove the clipped VF/#915 source-payment inequality or a local lag/window estimate.

## 2. The original exponent-producing estimates are concrete

For an OAI-NNS investigation, reuse the original exact chain rather than announcing that its arithmetic inequality still has to be found:

```text
canonical_nonexceptional_ideal_sum / canonical_exceptional_ideal_sum
 -> original_source_truncation_bound
 -> original_energy_nonzero_bound + zero-mode bound
 -> actual_additive_gram_bound
 -> original compensated LOW assembly and normalization
 -> native source moments and same-probe HIGH/principal comparison
 -> native_beta_le_seven_eighths
 -> nativeReplay_signed_energy_seven_fourths.
```

Original pinned sources:

- [GramSourceEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/GramSourceEstimate.lean)
- [GramInfiniteEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/GramInfiniteEstimate.lean)
- [GramBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/GramBound.lean)
- [LowGramApplied.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowGramApplied.lean)
- [LowGramScale.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/LowGramScale.lean)

With `P=Y^2/Q`, the actual arithmetic Gauss-energy theorem is

```text
||G(Q,Y;v)|| <= K (1+|v|)^J (Q/Y) [1 + P^(1/6) + P^2/Y] Y^epsilon.
```

Its original smooth-profile, calibration, excluded-prime, positivity and scale hypotheses remain part of the theorem. `P^(1/6)` comes from the exceptional arithmetic contribution. This is not a free positive saving parameter or a generic bound on arbitrary coefficients.

At the nominal physical scales `X=Z^(17/48)`, `Y=Z^(23/48)`, with fixed calibration and tuple divisor `L=1`, one has `Q` proportional to `XY` and `P` proportional to `Z^(1/8)`. The three displayed powers are `17/48`, `3/8`, and `1/8`. The square-root Gram power is `3/16`; the fully assembled LOW probe has that exponent up to positive loss, and the principal signal shift is `-11/16`. Thus `3/16-(-11/16)=7/8`. The HIGH remainder and source moments on the same probe are indispensable, already supplied parts of this baseline proof. The nominal calculation does not replace the actual all-tuple, moving-scale assembly.

The existing physical tilt in [VF919TiltedProbe.lean](../research/oai_434/VF919TiltedProbe.lean) changes

```text
x = 17/48 - 24 delta,       y = 23/48 + 12 delta,
LOW exponent = (5x+y)/12 = 3/16 - 9 delta,
principal shift = -11/16 - 8 delta,
LOW minus principal shift = 7/8 - delta.
```

Its slot-charge condition and complete HIGH reserve are not optional. This is existing leverage, not a fresh discovery or an automatic iterable contraction.

## 3. Do not replace a paid global conclusion by a stronger compulsory target

The square of a sum of square-shell increments, with all cross-shell terms retained, is different from the sum of squared increments. The existing global result does not assert

```text
sum_(H<=R<2H) |sum_(R^2<=n<(R+1)^2) mu(n)|^2
  <= C_epsilon H^(5/2+epsilon).
```

That sharper local norm remains an eligible **optional sufficient route**, not a missing premise of the completed OAI/native replay and not the entrance requirement for every new exponent proof. A researcher choosing it must explain what extra structural advantage justifies paying that stronger norm. Keep the direct global, signed mixed-bill, inverse/prime, recurrence, and full-basis consumers available.

Similarly, the original CORR4 identity already yields an inherited-scale upper estimate. Write `G_R=M(R^2-1)-M(R-1)`, `d_q=M(floor((R^2-1)/q^2))`, and sum over the original odd primes `q^2<R`. With its nonnegative physical diagonal `H_R`,

```text
B_R = G_R^2 + 2 G_R sum_q d_q/q - 2 sum_q d_q^2 - H_R
    = (1 + (1/2)sum_q 1/q^2)G_R^2
        - 2 sum_q (d_q-G_R/(2q))^2 - H_R.
```

The reciprocal-square sum is bounded independently of R. Consequently an available `M(x)=O_epsilon(x^(b0+epsilon))` gives `B_R=O_epsilon(R^(4b0+epsilon))`. At `b0=7/8`, this is `R^(7/2+epsilon)`. This is a mathematical consequence of the existing identity and input, not a claim that this documentation has formalized a new declaration. Do not queue that inherited estimate as an independently missing theorem. A source-native improvement must beat the best applicable `b0` or independently establish a new route to the desired endpoint.

## 4. Compare the proposed inequality with its real consumer

For the selected route only, record a compact improvement packet in the existing report, then spend the run on the derivation:

| Item | Required mathematical content |
| --- | --- |
| Established input | Exact declaration/source SHA, original carrier and quantified bound already available. Substitute available results before declaring a gap. |
| Proposed change | The inequality to strengthen, its unchanged hypotheses or explicitly justified changed ones, and the arithmetic feature that could make it stronger. |
| Original loss | Identify the first relevant triangle, absolute value, Cauchy, relaxation, collision, scale or truncation loss; do not assume every loss is binding. |
| Complete return | Preserve actual coefficients, all selected cases, history, moving cutoffs, diagonal, principal, complementary and mixed terms. Pay only losses this route introduces. |
| Endpoint accounting | State the old and candidate amplitude/energy powers in the same variable, the actual consumer, and the net improvement after losses. Mark an unfinished transport conditional. |
| New work | Supply a genuine proof step, source-valid falsifier, or exact test of a changed claim, and the first still-unproved inequality. Distinguish component progress from a verified endpoint gain. |

Do not require a finished endpoint theorem before allowing a useful intermediate lemma. Conversely, a rewritten identity, a stronger-looking coordinate, a finite fit, or a bound recycled from the desired conclusion is not an independent saving. A target-equivalent conclusion is a legitimate theorem to prove; equivalence alone neither proves it nor makes it an invalid research route. A constant-factor gain becomes an exponent gain only through a proved uniform iteration/recurrence or other complete consumer.

For a global signed-energy improvement `D(N)+2C(N) << N^(7/4-kappa+epsilon)`, the rounded-baseline amplitude gain is `kappa/2`. For a CORR4 bill `B_R << R^(7/2-eta+epsilon)`, it is `eta/4`. Neither is automatically a gain beyond an already stronger inherited boundary. Keep the additional loss and fixed-power distinctions explicit.

### Two useful OAI comparisons, not mandatory team assignments

**Exceptional Gram term.** Replacing `P^(1/6)` by `P^(1/6-kappa)` for fixed `0<kappa<1/6` would change the nominal Gram power to `3/8-kappa/8` and its square root to `3/16-kappa/16`; the other two displayed nominal Gram terms are smaller. A final improvement `kappa/16` is **conditional** on proving that arithmetic estimate on the original source, propagating it through the complete LOW assembly, and retaining a sufficient same-probe HIGH/principal margin. Do not infer a global improvement from this one factor or treat the input bound as already proved.

**Retained signed tuple terms.** [VF919OriginalLowTupleSignedGram.lean](../research/oai_434/VF919OriginalLowTupleSignedGram.lean) exposes the exact source before the original tuple `norm_sum_le`, including NNS Co-minus-Div. However, the original `J` is the **unselected** subset: `J=empty` is all-selected and has one outer tuple, so its outer off-diagonal is exactly zero. Improving only nonempty-J cross terms does not pay this binding case. Reuse the completed source identity and applicable moving-mass results at their verified scopes; do not rediscover them or assume a universal negative cross term. An inner-row or complete integrated improvement is eligible, but it must be proved on that actual source. This guard prevents the correction from reviving a known false shortcut.

No agent on another route must supply an artificial rational-Mobius-to-Hecke identification, rerun this OAI audit, or switch to either comparison.

## 5. Seven roles, independent routes, shared standard of comparison

| Role | Apply this correction without changing protected coverage |
| --- | --- |
| Coordinator | Distinguish established baseline, independently new arithmetic, and complete endpoint gain. Correct stale queues that ask to rediscover 7/8 or impose local shell energy globally. Assign distinct hypotheses and prevent duplicate reconstruction; do not centralize the team on OAI. |
| Owner Payment | Keep VF-LOW / SAT / JOH. Substitute the strongest applicable actual-prime or Mertens input before naming a missing estimate. Pursue genuine weighted incidence, chronological or joint-source improvements with their original complete return; do not replace actual prime membership by density. |
| Analytic Type II | Keep CODIV / OAI-NNS / NYMAN. On OAI, start at a still-binding arithmetic supplier in the established chain. On other routes, compare with their own available source bound and consumer. Do not require sharp-shell L2 or a new generic covariance hypothesis as a universal prerequisite. |
| Finite Wheel | Keep FINITE-AC / CORR4 / MU-LIFT. Seek an arithmetic restriction beyond the inherited bound, preserving actual factors, signs, resource use and return. Constant-density matching and finite cap improvements keep their true scopes unless a uniform exponent consumer is supplied. |
| Prime Census | Test an explicit proposed strengthening against its established comparator on identical admitted coefficients. Retain decisive falsifiers and original anchors; use exact/certified arithmetic where decisions need it. Do not fit a power or rerun unchanged scans as evidence of a new exponent. |
| Adversarial Referee | Check that the baseline really applies and is not being unnecessarily reproved; then attack the changed inequality, all quantifiers and complete return. Distinguish a genuine counterexample from an unsupported no-go for the entire route. Independently review source-preserving target-equivalent proofs rather than rejecting them just for equivalence. |
| Lean Verification | Reuse unchanged exact-head proof evidence. Repair actual failures or formalize independently qualified mathematics from any route. Do not turn the baseline, an assumed stronger supplier or an algebra-only wrapper into a new-gain claim. Preserve warning-fatal compilation, exact theorem/axiom checks and human-only merge. |

All nine protected routes and serious new hybrids remain eligible. The rolling three substantive investigator invocations and six non-Lean own-report-only permissions remain unchanged. Useful local theory and falsification remain allowed; no positive numerical gain is presumed or required before exploratory work.

## 6. Status language and activation

Use these distinctions accurately: `ESTABLISHED_BASELINE`, `INDEPENDENT_COMPONENT_ADVANCE`, `CONDITIONAL_ENDPOINT_TRANSFER`, and `NEW_VERIFIED_ENDPOINT_GAIN`. These are reporting distinctions, not replacements for the existing proof/CI/publication status scheme. A completed universal signed-prefix bound must not be called missing; an unrelated original VF or sharp-window obligation must not be called paid by it. Mathematical positivity of an existing slot gap is not erased by its small size.

At the first actual invocation after merge, read this correction, record `baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1` with main/policy SHA, identify the existing result actually used on the chosen route, and continue with a new arithmetic step. For a route where the baseline has no useful forward implication, say so and use its own source/consumer; do not fabricate a transport. Reading the policy alone is not mathematical progress. Subsequent runs reuse unchanged verified facts rather than repeating a full historical audit.

This PR changes repository instructions only. It does not edit saved Studio prompts, schedules, tool grants, Lean sources, CI safeguards, agent reports or theorem statuses, launch agents, or authorize a direct main push or automatic merge. Activation is established only by human merge and an actual subsequent report acknowledging consumption. No new eta or delta is proved by this instruction correction.
