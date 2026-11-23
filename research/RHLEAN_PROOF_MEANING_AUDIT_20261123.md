# RH_Lean proof-meaning and reconstruction-scope audit

**Date:** 2026-11-23. **Main inspected:**
`4b9881be8fcb2b0b817afe5008d29adbcd829a5c`.
**CM draft inspected:** `ffec57739f5c379ed13c551162373eb842ba4bfd` (PR #1201).
The scope is source inspection and Python reporting-tool validation. No local
Lean/Lake execution was performed. No conclusion of repository-wide semantic
clearance or upstream invalidity follows from this audit.

## Findings

1. The CM draft adds 41,537 lines across 161 changed files relative to the inspected
   main. Its report still marks the complete source bound and RH OPEN, and does
   not certify the integrated hosted closure at that checkpoint. The work has
   expanded into substantial geometric reconstruction.
2. The existing native
   [`riemannHypothesis_of_eventual_squareClock_Gz_rpow`](../RHLean/Analysis/AlpogeNativeSquareClockCriterion.lean)
   proves RH from a one-sided R^(1+eta) bound on the actual Gz(R^2-1), for every
   positive eta. Its internal import closure has no CM, Serre, theta, or
   signed-slope supplier dependency. Such geometry is one possible source of the
   estimate, not a requirement of this endpoint consumer.
3. The actual
   [Gz arithmetic and square-clock sampling](../RHLean/Analysis/AlpogeSquareClockSignedHistorySampling.lean)
   and [NNS identity](../RHLean/Analysis/AlpogeExactNNSGzBridge.lean) use genuine
   von Mangoldt coefficients, including all prime powers, and preserve the
   signed correction. These identities are not the missing quantitative bound.
4. The
   [signed-slope comparison](../RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean)
   requires eleven substantive inputs, followed by size/window conditions for
   its quantitative consumer. `physicalData_Ga` legitimately proves that the
   geometric gain is preserved; it does not prove the gain bound.
5. The raw
   [window-witness interface](../RHLean/Analysis/AlpogeNativeZetaWindowWitness.lean)
   permits degenerate inertia and arbitrary `ell` data, without a certified
   logarithmic-derivative identification. The
   [existing report](ALPOGE_NATIVE_MINIMUM_CUT_AND_DESCENT_20261122.md) explicitly
   warns that `top` can then become the desired Gz bound itself. This is valid
   conditional infrastructure, not an independently constructed physical witness.
6. Bounded inspection of the native geometry did not find the specific
   `anyGeometry := True` / `setDiv` construction described by the user. The
   [prior realization audit](ALPOGE_REALIZATION_BOUNDARY_AUDIT_20261122.md)
   already distinguishes such upstream weak interfaces from substantive
   realization requirements. A name scan cannot establish semantic soundness.

## Reproduced proof-status defect

Before this repair, `scripts/rhlean_kg.py::compute_status` inferred the references
in hypotheses by subtracting conclusion references from all statement references:

```python
hypothesis_refs = set(statement_refs) - set(conclusion_refs)
```

For a named closed proposition P and `theorem t (h : P) : P`, both sets contain
P. Subtraction erases the actual assumption. The status fixed point could then
promote P to `proved` using its own conditional restatement.

This is a reporting-tool error, not a Lean-kernel error. The theorem P -> P is
valid; treating it as a proof of P is not. The same status code is used after
elaborated-graph ingestion, because that dump does not separately encode binder
and conclusion references. The defect was reproduced with an in-memory fixture;
this audit does not assert that the live RH target was marked proved by it.

A second reproduced form accepted a conclusion mentioning only P as a proof of
P, even when it was the reflexive equality `P = P`. The repair resolves hypothesis
references independently, retains overlap with the conclusion, and restricts
closure rules to direct named-proposition conclusions or literal named
equivalences. Other visible hypotheses conservatively block closure unless they
are named closed project propositions that the fixed point separately discharges.
Regression tests cover self-assumption, reflexive/composite conclusions, and
valid independent premise discharge. The CI preflight runs these inexpensive
tests before Lean setup. This is a targeted correction, not a complete semantic
decision procedure.

A comparison on all 19,709 source declarations at the inspected main snapshot
changes 68 theorem/lemma labels from `proved` to `reduced`, because shared named
premises are now retained. No closed-proposition status changes. For example,
`nativePNTHasAffineEnvelope_lowSlope_cubic_step` assumes an affine-envelope
predicate and proves it at another exponent; `NativeTheta.Paired.IsHarmonic.colAct`
assumes harmonicity and transports it through a column action. These are valid
conditional results. The reporting correction does not invalidate their Lean
proofs or establish that the live RH target was previously marked proved.

## What an axiom audit does and does not establish

The user's example supplies `hRH : RiemannHypothesis` and returns that same proof
alongside an independently trivial bundle. Its logical content is RH ->
(True-like certificate and RH). It proves no unconditional RH result. The
explicit hypothesis is a function parameter, not a custom global axiom, so
`#print axioms` need not flag it.

The [Lean reference's validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
separates proof validity from the meaning of the statement. Source hash checks,
an allowed terminal-axiom list, and kernel checking are necessary evidence for
their respective purposes; none substitutes for examining the full theorem
type and the definitions of the intended quantities.

The graph remains a navigation/status aid. Source parsing does not completely
elaborate section variables, notation, typeclasses, or witness semantics. A final
unconditional result requires an exact elaborated type with no undischarged RH
or sufficient-bound premise, plus verification of its actual Mathlib target.
Theorem-node status `proved` can still describe a valid conditional theorem;
`hard_blocked` prevents it from promoting a target proposition. The theorem-node
label alone is not an assertion of an unconditional supplier.

## Verification of this repair

- `python3 -m unittest discover -s scripts -p test_decl_graph.py -v`: 13 tests
  pass, including the new source and synthetic elaborated-ingestion regressions.
  Synthetic extractor records test the reporting pipeline; they are not Lean
  compilation receipts.
- `python3 -m unittest scripts/test_ci_cache_contract.py -v`: 24 tests pass.
- `python3 scripts/check_documentation.py`: relative links pass across 468 documents.
- `git diff --check`: pass.

No mathematical Lean declaration is changed by this repair. Hosted CI status
must be read on the published PR; these local Python results are not a claim
that its future hosted run has passed.

## Research correction

The [native-bound directive](../docs/RHLEAN_NATIVE_BOUND_SEMANTIC_ACCEPTANCE_20261123.md)
requires every further construction to name the native premise it independently
discharges. It retains real geometric work and explicit open obligations while
removing full upstream reconstruction as the default task. It makes no claim
that RH_Lean's coordinates already supply the remaining bound.
