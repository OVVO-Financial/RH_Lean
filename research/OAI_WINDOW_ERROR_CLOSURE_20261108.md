# Positive-error closure of the complete OAI boundary

Claims: `20261108-analytic-3/EC1-EC3`, independently accepted with scope in
`20261108-referee-3`. Implementation status: PROVED_IN_LEAN at exact proof
head `77ee815846d6d534c866f0752aa33b84c385610a`, green and unmerged in #1119.

## Exact Target And Proof Plan

For every original `HighData (1/1000000)` record D satisfying
`D.ell i <= detectorMesh (1/1000000) D.t / 200`, put m equal to the actual
minimum of its finite slot list. Prove

```text
HeckeZeroSupremum.beta <= 7/8 - (7/8)*m.
MertensGrowthAtMost (7/8 - (7/8)*m).
```

The previous exact complete theorem gives `beta <= 7/8-(7/8)*m+D.e`.
The new constructor replaces D.e by any e with `0<e<=D.e`, recertifies
all six affected budgets, and keeps every other data field unchanged.
Compare minimum values in both directions, not chosen minimum indices.
Apply the existing complete theorem to the new record. Under a putative
positive numerical gap d, choose `e=min(D.e,d/2)` and contradict the gap.

Dependencies: the original pinned HighData declaration, existing
`native_beta_le_window_saturated_minimum_of_fine`, original source/count
existence, full LOW/HIGH/principal comparison, and native Mertens transfer.
No new moment estimate, desired-bound premise, or classical axiom is added.

## Source And Quantifiers

The original `SourceData.first` requires `FirstTail (4*e) S`. An old source
cannot be reused by assertion at a smaller e. The existing complete theorem
constructs a new finite S, its modulus, source corrections, masks and count
parameters for every new positive e. Its full compensated LOW and HIGH
share that same new source. No source with e=0 is used. No uniformity of
asymptotic constants as e tends to zero or infinite-mask limit is required.

The result is a complete quantitative consequence, not an identity or an
assumed source estimate. The same-D ceiling improves by exactly D.e.
The growth theorem retains every positive exponent loss. Spending D.e/2
gives a fixed power strictly below the previous exact same-D ceiling.

The existing near-uniform witness with fixed N=nearUniformSlotCount and
m>=1/(8*N) supplies the conservative explicit boundary
`7/8-7/(64*N)`. This is not a claim that coarse displayed 1/N differences
measure every unrounded source gain. No slot-count optimization is done.

## Validation And Remaining Gap

[Run 42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910),
[job 128949473700](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700),
passed on the literal proof head. All 14 current-head checks passed. New
warning-fatal source, seven exact-type examples, seven printed axiom lists
and five live source/dependency/axiom closures were verified. Every terminal
uses only propext, Classical.choice and Quot.sound. The initial final-scalar
linarith failure was repaired by direct order transitivity without changing
any statement, hypothesis or validation requirement. No local Lean was run.

GitHub Actions compiled on Lean 4.34.1 and pinned Mathlib, warnings fatal,
and checked the exact public types and permitted axioms. The dependency
audit found the positive-error reconstruction, fresh source existence,
complete probe/principal comparison and genuine native arithmetic transfer
in the live proof-value closure. Existing total-mass audits remain intact.

This does not prove finite A, zero-log amplification, canonical VF or RH.
The unchanged fixed-slot window condition still bounds each actual reserve
strictly below 7*m/8. Referee SG's geometry-changing improvement is a
separate, not yet independently accepted paper claim and is not implemented
here. A further gain needs its own complete, source-faithful proof.
