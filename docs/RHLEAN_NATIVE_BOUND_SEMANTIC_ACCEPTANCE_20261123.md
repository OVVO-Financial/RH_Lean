# Native bound and proof-meaning acceptance

**Date:** 2026-11-23. **Directive:** NATIVE_BOUND_SEMANTIC_ACCEPTANCE_V1.
This records the user's correction that RH_Lean should exploit its native geometry
and should not default to reconstructing the entire Alpoge development. It also
requires protection against correct Lean proofs of vacuous or misrepresented
statements. The complete native critical estimate remains OPEN.

## 1. Start from the existing arithmetic consumer

The existing
[`riemannHypothesis_of_eventual_squareClock_Gz_rpow`](../RHLean/Analysis/AlpogeNativeSquareClockCriterion.lean)
consumes precisely

\[
\forall\eta>0\;\exists C_\eta\ge0, R_{0,\eta}\;
\forall R\ge\max(2,R_{0,\eta}),\qquad
G_z(R^2-1)\le C_\eta R^{1+\eta}.
\]

The constants and thresholds may depend on eta but not on R. This is one-sided.
Do not require an absolute estimate, a fixed no-loss linear estimate, or a
separate estimate on every signed constituent unless the actual proof needs it.
The [window consumer](../RHLean/Analysis/AlpogeNativeWindowLandau.lean) permits
the weaker stated arbitrarily far multiplicative-window condition. Isolated
good endpoints do not meet that condition.

The [signed square-clock sampling theorem](../RHLean/Analysis/AlpogeSquareClockSignedHistorySampling.lean)
already pays the between-square error at square-root scale. The
[exact NNS bridge](../RHLean/Analysis/AlpogeExactNNSGzBridge.lean) preserves the
signed history and its harmonic/logarithmic correction. Reuse these theorems;
they do not supply the remaining source bound themselves.

The existing finite-A/C and other native consumers remain legitimate alternatives
with their actual quantifiers. Do not infer an epsilon-free finite constant from
an RH consequence with every positive exponent loss, or use an RH-strength
input to establish itself.

## 2. Admit only connected construction work

For each next task record:

1. The independently defined native signed quantity and its exact target bound.
2. The existing consumer and its complete hypotheses.
3. The existing supplying declarations already checked and the first unmet premise.
4. The proposed proof step and how it removes that premise or improves its budget.
5. Any remaining norm, rank, mass, integrality, normalization, or uniformity costs.

CM, Serre, theta, and cusp constructions remain eligible when this record gives
their concrete necessity or an actual quantitative contribution. Completing an
upstream subsystem merely because it is upstream is not the default task.
Preserve real reusable constructions; source size and declaration count are not
measures of progress on the critical estimate.

This directive does not prove that the hard source estimate follows from square
geometry alone. An exact identity, finite rank, determinant, or joint injectivity
cannot replace an unproved uniform norm estimate.

## 3. Acceptance has both formal and semantic parts

For a claimed independent supplier, retain an auditable record of:

- **Statement:** the elaborated type, including section variables, implicit
  arguments, typeclasses, and all nested structure fields that carry estimates.
- **Target:** the actual native arithmetic definitions and, at the terminal
  step, Mathlib's original `RiemannHypothesis`, with no replacement or shadowing.
- **Construction:** the actual objects and separately proved constructors of
  every required premise, on one compatible set of data.
- **Measurement:** ranks as actual ranks, masses from the actual measure, and
  heights/norms from the actual lattice/metric, with the necessary identifications
  proved. Choosing a field to equal the target formula is not that identification.
- **Nondegeneracy:** precisely the positive ranks, nonzero maps, positive masses,
  spans, and positive denominators used in the argument. Do not ban legitimate
  zero-rank cases in general lemmas; prove usefulness at the physical instance.
- **Uniformity:** constants and choices quantified in the required order, with
  every scale-dependent cost retained after the actual signal normalization.
- **Verification:** the exact committed source and required hosted checks,
  including permitted terminal axioms. A source-only inspection is not a build.

`rfl` is valid for preservation and definitional coordinate identities. It is not
evidence of an independent inequality. Conditional theorems are useful when
labelled conditional. Their premises remain open until constructed.

`#print axioms` checks axiom dependencies, not whether a theorem assumes its
conclusion or whether its definitions model the intended mathematics. A theorem
`(h : P) : P` must never promote P to independently proved status. Neither a
lexical graph nor the exact graph of referenced constants alone certifies full
semantic meaning. See the [source audit](../research/RHLEAN_PROOF_MEANING_AUDIT_20261123.md).

## 4. Operational scope

Apply this priority on the next actual relevant invocation. Repository updates
do not launch scheduled agents, alter prompts/grants, or prove activation.
Hosted-only Lean execution, existing report ownership, lossless publication,
and human-only merge remain unchanged. Do not restart the retired OAI replay.
