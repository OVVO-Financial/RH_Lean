# RH_Lean formalization checklist

This file is the mandatory closeout record for every pull request in `RH_Lean`.

`FORMALIZATION_SEQUENCE.md` is the single source of truth for theorem dependency order. This checklist records the execution rules, visible completion status, and append-only PR ledger.

A PR is not complete unless this file is updated on the same branch before the substantive merge-gating CI run. Do not add a post-green documentation-only commit merely to record CI status.

## 1. Non-negotiable proof rules

Every PR must preserve all of the following:

- no `sorry`, `admit`, new axioms, line-leading opaque constants, or theorem substitutes;
- no weakened statements, changed indexing, hidden assumptions, or circular RH premises;
- use Lean 4 and mathlib `v4.24.0` and inspect version-sensitive APIs before proof work;
- use modulus `2 * r`, never `r`, for the quadratic prime phase;
- keep prime-3 rational cell-mask energy separate from the complex quadratic phase;
- keep the full signed shell sum inside the norm and retain every cross-shell Gram term;
- keep theorem-predicted subtraction separate from true orthogonal projection;
- introduce numerical finite-range claims only through the proved certificate checker;
- keep accepted-certificate validity separate from mathematical realization;
- do not infer the sharp constant `4` from residual size alone; retain the signed interaction;
- keep prefix signed-interaction control separate from uniform local-window control;
- never infer a translated local-window inequality by subtracting two prefix inequalities;
- use the manuscript's uniform local criterion
  `V_loc(N,H) ≪_ε H N^(2+ε)` for `1 ≤ H ≤ N` in the RH bridge;
- do not substitute the weaker global `O(N^(3+ε))` average for that local criterion;
- keep exact signal recombination separate from energy identities: if
  `S = S_low + S_high`, the total/high criterion equivalence must use norm
  inequalities plus the proved low-sector bound, not subtraction of energies;
- use the exact manuscript endpoint `X_n = (n+1)^2 - 1` for the concrete square-prefix sequence;
- expose the final external input exactly as
  `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`;
- do not reintroduce an abstract start-sequence realization or project-specific RH bridge into the final concrete theorem;
- expose every remaining analytic implication, equivalence, and realization as an ordinary typed premise;
- do not describe a conditional bridge as an unconditional proof of RH;
- treat every warning as a CI failure because the project builds with `--wfail`.

## 2. Per-PR execution checklist

Copy this task list into the PR description and prepopulate it before merge-gating CI:

- [ ] Confirm the preceding PR is green and merged; read current `main`.
- [ ] Read the canonical sequence and checklist.
- [ ] Select exactly one dependency-bounded theorem or corrective layer.
- [ ] State what the PR proves, what it corrects, what it excludes, and what remains.
- [ ] Inspect exact theorem names and signatures at mathlib `v4.24.0`.
- [ ] Branch from current `main` as `agent/<focused-description>`.
- [ ] Implement the smallest stable module or correction.
- [ ] Import every new theorem module from `RHLean.lean`.
- [ ] Prepopulate both formalization documents and the PR body.
- [ ] Pass `bash scripts/audit_assumptions.sh`.
- [ ] Pass `lake build RHLean --wfail` with no warnings.
- [ ] Fix only exact compiler or CI diagnostics.
- [ ] After three failed substantive attempts, request the complete job log as a diagnostic delimiter and continue until green.
- [ ] Do not add a documentation-only commit after green CI.
- [ ] Merge only after green CI and explicit authorization.
- [ ] Begin the next PR only after confirming the merge on current `main`.

## 3. Required closeout record

Each PR description and checklist update must identify:

- PR number and title;
- theorem or corrective layer completed;
- principal new or changed modules;
- central proved statements;
- exact error or architectural mismatch corrected;
- invariants protected;
- CI commands that gate merge;
- remaining analytic or realization obligations.

## 4. Successful PR ledger

A checked entry visible on `main` means the PR reached `main` through the required process. The ledger is append-only.

- [x] **#1** — Initialized Lean 4/Lake, pinned mathlib `v4.24.0`, added CI/source audit, Fermat coordinates, and fixed packets.
- [x] **#2** — Added the exact dyadic-cell paper section.
- [x] **#3** — Integrated the dyadic theorem material into the paper branch.
- [x] **#4** — Added deterministic manuscript integration for the exact dyadic cell theorem.
- [x] **#5** — Proved exact Möbius doubling on odd inputs.
- [x] **#6** — Proved exact four-slot Möbius compression.
- [x] **#7** — Proved universal prime-3 activation and its deterministic cycle.
- [x] **#8** — Proved squared complex factor recovery.
- [x] **#9** — Corrected the architecture to modulus `2r` and separated cell-mask and prime-phase mechanisms.
- [x] **#10** — Replaced shellwise smallness with full signed Gram control and explicit block-contraction architecture.
- [x] **#11** — Proved square residues modulo `24`.
- [x] **#12** — Proved the prime-square wrapper modulo `24`.
- [x] **#13** — Proved quadratic numerator periodicity.
- [x] **#14** — Defined and proved quadratic exponent congruence modulo `2r`.
- [x] **#15** — Proved prime square classes `1` or `9` modulo `40`.
- [x] **#16** — Proved the quadratic shift-by-`r` arithmetic dichotomy.
- [x] **#17** — Proved exact cofactor parabola identities.
- [x] **#18** — Proved exact conformality identities for the complex square map.
- [x] **#19** — Proved the two-sheeted complex square fiber theorem and positive-branch injectivity.
- [x] **#20** — Established `FORMALIZATION_SEQUENCE.md` as the canonical dependency roadmap.
- [x] **#21** — Defined the corrected complex quadratic phase and proved exact `2r` periodicity.
- [x] **#22** — Proved the exact shift-by-`r` complex sign law.
- [x] **#23** — Defined the reduced quadratic Gauss factor over `(ZMod (2 * r))ˣ` and its totient normalization.
- [x] **#24** — Proved exact small-modulus resonance at moduli `6` and `24`.
- [x] **#25** — Established the mandatory closeout checklist and refreshed the Phase I checkpoint.
- [x] **#26** — Added explicit completion markers to the checklist and canonical roadmap.
- [x] **#27** — Proved the exact rational prime-3 cell-mask mean and squared mean-mode energy.
- [x] **#28** — Proved exact `2ab` displacement, monotonicity, and vertical-window lifetime criteria.
- [x] **#29** — Proved exact reduced square-class phase support modulo `40`.
- [x] **#30** — Proved the exact height-shell Gram identity with all signed off-diagonal terms retained.
- [x] **#31** — Proved true projection orthogonality and Pythagorean decomposition while separating predicted subtraction.
- [x] **#32** — Defined the scale-dependent resonant projection skeleton and exact algebraic recombination.
- [x] **#33** — Exposed the four resonant/nonresonant block maps and exact affine recurrence.
- [x] **#34** — Proved the abstract weighted block-contraction closure.
- [x] **#35** — Defined the explicitly indexed actual residual and packaged the leakage state.
- [x] **#36** — Formalized exact resonant cancellation for compatible Möbius cofactor pairs.
- [x] **#37** — Proved low-height, endpoint, boundary, rowwise, and weighted forcing estimates.
- [x] **#38** — Formalized the complete joint index, exact recombination, and full signed joint Gram interface.
- [x] **#39** — Added the sound executable finite-range certificate checker.
- [x] **#40** — Connected accepted data to actual joint energies and proved the uniform residual-energy bound.
- [x] **#41** — Proved the exact actual-start prefix signed-frame theorem with explicit signed absorption.
- [x] **#42** — Formalized an axiom-free conditional global-prefix RH bridge; later identified as insufficient for the manuscript's uniform local criterion.
- [x] **#43** — Corrected the bridge to uniform local windows, proved the exact local frame layer and `H = 1` extraction, and preserved all remaining classical/realization obligations explicitly.
- [x] **#44** — Proved the exact geometric low/high reduction: translated-window low bound, total↔high local criterion, and high-sector criterion↔RH through the explicit bridge.
- [x] **#45** — Closed the project-specific Mertens adapter: concrete `M(x)`, exact `X_n=(n+1)^2-1`, square interpolation, pointwise/local conversion, direct concrete geometry theorem, and zero-friction future mathlib hook.
- [x] **#49** — Proved the exact normalized ordered cofactor expansion, the `-1/2` tripling coefficient law, and child-plus-twice-parent cancellation over `ℚ` and `ℂ`.
- [x] **#51** — Realized the exact square-prefix Mertens value as a normalized ordered sum over `ActualCofactorChannel`, with the lower Möbius factor separated to match `actualResidualEntry`.
- [x] **#52** — Defined the exact manuscript height selector `|Y| ≤ Λ n`, constructed finite low/high normalized channel supports, and proved exact signal-level recombination.

## 5. Theorem-layer completion checklist

### Phase I — corrected complex quadratic-phase layer

- [x] **1. Complex quadratic phase API** — PR #21.
- [x] **2. Exact shift-by-`r` sign law** — PR #22.
- [x] **3. Corrected reduced quadratic Gauss factor** — PR #23.
- [x] **4. Exact small-modulus resonance** — PR #24.

### Phase II — exact combinatorial and geometry layers

- [x] **5. Prime-3 cell-mask mean energy** — PR #27.
- [x] **6. `2ab` displacement and lifetime geometry** — PR #28.
- [x] **7. Reduced square-class phase support modulo `40`** — PR #29.

### Phase III — exact signed Hilbert/Gram machinery

- [x] **8. Height-shell Gram identity** — PR #30.
- [x] **9. Orthogonal residual** — PR #31.
- [x] **10. Scale-dependent resonant projection skeleton** — PR #32.
- [x] **11. Explicit resonant/nonresonant leakage operator** — PR #33.
- [x] **12. Abstract weighted affine Lyapunov closure** — PR #34.

### Phase IV — number-theoretic closure

- [x] **13. Actual residual decomposition** — PR #35.
- [x] **14. Resonant Möbius cofactor cancellation** — PR #36.
- [x] **15. Low-height, endpoint, and boundary estimates** — PR #37.
- [x] **16. Full joint signed Gram control** — PR #38.
- [x] **17. Certified finite-range checker** — PR #39.
- [x] **18. Uniform full residual bound** — PR #40.
- [x] **19. Actual-start prefix signed-frame theorem** — PR #41.
- [x] **20. Explicit global conditional bridge** — PR #42; insufficient as the local RH criterion.

### Phase V — corrected localization

- [x] **21. Uniform local signed-frame and corrected RH criterion** — PR #43.

### Phase VI — geometric criterion equivalence

- [x] **22. Exact low/high geometric reduction** — PR #44.

### Phase VII — concrete Mertens closure

- [x] **23. Concrete square-prefix Mertens adapter and direct mathlib hook** — PR #45.

### Phase VIII — normalized cofactor realization

- [x] **24. Normalized ordered cofactor expansion and exact tripling scaling** — PR #49.
- [x] **25. Concrete square-prefix cofactor-channel realization** — PR #51.
- [x] **26. Exact high/low height partition and finite channel supports** — PR #52.
- [ ] **27. Farey mode action, shell assignment, and contiguous packet-window derivation**.
- [ ] **28. Concrete `ActualResidualData` constructor and exact high-sector recombination**.
- [ ] **29. Tripling-compatible packet transport and full signed defect identity**.

## 6. Current checkpoint

Principal definitions in `RHLean.Proof.NormalizedCofactorExpansion`:

- `distinctPrimeCount`;
- `alphaWeightRat`;
- `normalizedCofactorWeightRat`;
- `orderedCoprimeFactorPairs`;
- `normalizedFiberExpansionRat`.

Principal definitions in `RHLean.Proof.ConcreteSquarePrefixCofactorRealization`:

- `actualChannelOfPair`;
- `normalizedChannelAmplitudeRat`;
- `normalizedChannelAmplitude`;
- `squarePrefixCofactorExpansionRat`.

Principal definitions in `RHLean.Proof.SquarePrefixHeightPartition`:

- `squarePrefixHeightCutoff`;
- `IsLowHeightChannel` and `IsLowHeightPair`;
- `squarePrefixCofactorPairs`;
- `squarePrefixLowHeightPairs` and `squarePrefixHighHeightPairs`;
- `squarePrefixCofactorChannels`;
- `squarePrefixLowHeightChannels` and `squarePrefixHighHeightChannels`;
- `squarePrefixLowHeightExpansionRat` and `squarePrefixHighHeightExpansionRat`.

Principal theorems added by PRs #49, #51, and #52:

- `normalizedFiber_eq_moebius_rat`;
- `normalizedFiberExpansion_cast_eq_mertens`;
- `normalized_tripling_scaling_rat`;
- `normalized_cancellation_identity`;
- `lowerMoebius_mul_normalizedChannelAmplitudeRat`;
- `squarePrefixCofactorExpansionRat_eq_normalizedFiberExpansionRat`;
- `squarePrefixCofactorExpansion_cast_eq_squarePrefixMertens`;
- `squarePrefixLowHeightPairs_union_highHeightPairs`;
- `squarePrefixLowHeightPairs_disjoint_highHeightPairs`;
- `squarePrefixLowHeightChannels_union_highHeightChannels`;
- `squarePrefixLowHeightChannels_disjoint_highHeightChannels`;
- `squarePrefixCofactorExpansionRat_eq_low_add_high`;
- `squarePrefixMertens_eq_lowHeight_add_highHeight`.

The exact arithmetic channel realization and exact manuscript height partition are now complete. They do not yet define shell assignment, denominator-mode action, packet support, or a concrete `ActualResidualData` value.

## 7. Remaining obligations

- derive shell assignments and the Farey denominator-mode action;
- derive contiguous packet starts and packet lengths;
- construct concrete `ActualResidualData` without opaque support or amplitude fields;
- prove exact high-sector recombination and tripling-compatible packet transport;
- prove the high-sector signed-Gram and local prediction-energy estimates;
- construct the concrete finite-range realization, asymptotic contraction, exact start, and local signed-interaction control;
- import or formalize the classical theorem
  `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`.

Merge-gating commands remain:

```bash
bash scripts/audit_assumptions.sh
lake build RHLean --wfail
```
