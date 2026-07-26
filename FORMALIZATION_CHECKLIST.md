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
- for death shells, count divisor fibers over every integer height in the half-open shell window; never replace that sum by the divisor count of one endpoint;
- a death-process estimate alone does not control the survivor discrepancy `birth - death`; retain both endpoint obligations;
- any cofactor-parity decomposition must be finite, include the `ω(c)=0` class, and restrict the identity `μ(cq)=-μ(c)` to nonzero Möbius support;
- treat every warning as a CI failure because the project builds with `--wfail`.

## 2. Per-PR execution checklist

Copy this task list into the PR description and prepopulate it before merge-gating CI:

- [ ] Confirm the preceding dependency PR is green; read current `main` and the green head when stacking.
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
- [ ] Begin the next dependency-bounded PR after the preceding PR is green; stack explicitly until it reaches `main`.

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
- [x] **#52** — Defined the exact `|Y| ≤ Λ n` height partition, finite pair/channel supports, and exact low/high signal recombination.
- [x] **#53** — Defined the finite reduced Farey modes, exact tripling phase action, entry-shell assignment, and contiguous ordered-channel packet windows.
- [x] **#54** — Chose the exact source-entry shell, constructed concrete high-sector `ActualResidualData`, defined singleton source-entry amplitudes, and proved exact high-sector recombination without collapsing ordered orientations.
- [x] **#55** — Constructed concrete contiguous transport data and proved the complete tripling signed defect: finite boundary prefix plus explicit phase mismatch on the shared window; also restored the full branch-wide merge-gating workflow.
- [x] **#56** — Decomposed the complete high support into retained new-prime bases, injective tripled children, and explicit unpaired channels; proved the raw-family multiplicity correction and complete all-mode contribution identity.
- [x] **#57** — Proved the concrete transport residual equals the complete high family and instantiated its exact shell/cofactor/mode/row signed joint Gram identity; kept the uniform analytic estimate explicit and open.
- [x] **#60** — Added the native largest-prime-factor canonical square-block decomposition, exact recombination with `squarePrefixMertens`, explicit low-increment control interface, and the conditional `(HS) ↔ RH` theorem.
- [x] **#62** — Proved the exact coherent-mean and centered-covariance decomposition of canonical high-sector local energy, including the `H=1` collapse and the conditional conjunction↔RH bridge.
- [x] **#63** — Added the exact square-block smooth-minus-transport decomposition, cumulative Mertens realization, complete signed joint Gram energy, and conditional criterion↔RH bridge.
- [x] **#64** — Added the corrected `K^(1+ε)` increment-energy premise and proved its finite-Cauchy–Schwarz hierarchy to the existing cumulative local criterion, Gram premise, and conditional RH statement.
- [x] **#65** — Added the generic deterministic baseline transport approximation, exact transport error, blockwise baseline decomposition, cumulative decomposition, and square-prefix Mertens identity; no prime-count realization or analytic estimate is claimed.
- [x] **#67** — Added generic finite partial moments, the exact degree-one signed-sum and absolute-mass identities, guarded balance-ratio form, and the permanent multi-route roadmap.
- [x] **#68** — Added real canonical square-block increments, exact complex-cast and cumulative Mertens bridges, and the elementary total-variation bound.
- [x] **#69** — Added the denominator-free degree-one partial-moment balance premise and proved it implies the protected pointwise and uniform-local criteria and conditionally RH.
- [x] **#72** — Moved the canonical arithmetic core into `Analysis`, proved sharp low-height occupancy on nonzero Möbius support, isolated `m=1`, constructed unconditional low-increment control, removed the internal low-sector hypothesis from the native high-sector bridge, and passed the paper/Analysis boundary check, source audit, and full `RHLean --wfail` build.
- [x] **#73** — Established and enforced the paper/Analysis source-boundary contract.
- [x] **#74** — Moved the paper-facing canonical high-sector criterion and typed RH bridge from `Proof` to `Analysis` without changing theorem APIs.
- [x] **#75** — Moved the paper height partition into `Analysis` and repaired paper source references.
- [x] **#76** — Moved the superseded bridge track into `Proof`.
- [x] **#77** — Moved proof-technology modules into `Proof`.
- [x] **#78** — Added exact canonical high-sector height-shell reconstruction.
- [x] **#79** — Added the exact cumulative moving-height flow.
- [x] **#80** — Added exact birth-high absorption on the stacked branch.
- [x] **#81** — Promoted the birth-high absorption bridge to `main`.
- [x] **#82** — Added the exact `2ab` lifetime-overlap kernel.
- [x] **#83** — Added the exact lifetime active-set bridge.
- [x] **#84** — Added the honest two-premise lifetime local-energy criterion.
- [x] **#85** — Added the lifetime endpoint decomposition `active = birth - death`.
- [x] **#86** — Added death-process arithmetic and the exact half-open shell predicate.
- [x] **#87** — Proved that each death increment equals its death-shell Möbius mass.
- [x] **#88** — Published the death-process reduction and reproducible exploratory data.
- [x] **#89** — Proved shell-cardinality control of death increments and exact bias/centering decompositions.
- [x] **#92** — Added the complete verified Fermat sieve, including both mod-four lanes and the factor-five cases.
- [ ] **#93** — Adds the exact injection of every positive-cutoff death shell into divisor fibers over the full integer shell window, the resulting divisor-sum cardinality bound, and its death-process consequences.

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
- [x] **27. Reduced Farey modes, exact phase action, entry shells, and contiguous packet windows** — PR #53.
- [x] **28. Concrete high-height shell choice, `ActualResidualData` constructor, amplitudes, and exact high-sector recombination** — PR #54.
- [x] **29. Tripling-compatible packet transport and full signed defect identity** — PR #55.

### Phase IX — complete high-family analytic interface

- [x] **30. Complete tripling-pair/unpaired-channel decomposition and exact multiplicity correction** — PR #56.
- [x] **31. Concrete complete-family shell/channel/mode/row Gram realization** — PR #57.

### Phase X — native canonical high-sector criterion

- [x] **32. Native largest-prime-factor canonical decomposition and `(HS) ↔ RH` bridge** — PR #60.
- [x] **33. Canonical coherent-mean / centered-covariance split** — PR #62.
- [x] **34. Exact square-block smooth-minus-transport Gram identity** — PR #63.
- [x] **35. Strong square-block increment-energy hierarchy** — PR #64.
- [x] **36. Generic deterministic transport baseline decomposition** — PR #65.
- [x] **37. Generic finite partial moments and degree-one balance identity** — PR #67.
- [x] **38. Real canonical square-block increments and total-variation bound** — PR #68.
- [x] **39. Degree-one partial-moment balance sufficient criterion** — PR #69.
- [x] **40. Canonical low-height occupancy and realized low-sector control** — PR #72.

### Phase XI — height-shell reconstruction and lifetime/death flow

- [x] **41. Exact canonical high-sector height-shell reconstruction** — PR #78.
- [x] **42. Cumulative moving-height flow** — PR #79.
- [x] **43. Birth-high absorption bridge** — PRs #80 and #81.
- [x] **44. Exact lifetime-overlap kernel** — PR #82.
- [x] **45. Lifetime active-set bridge** — PR #83.
- [x] **46. Honest lifetime local-energy criterion** — PR #84.
- [x] **47. Lifetime endpoint decomposition** — PR #85.
- [x] **48. Death-process arithmetic shell structure** — PR #86.
- [x] **49. Death increment equals shell mass** — PR #87.
- [x] **50. Shell-cardinality transfer and centering** — PR #89.
- [x] **51. Complete Fermat sieve constraints** — PR #92.
- [ ] **52. Exact death-shell divisor-fiber bound** — PR #93.

## 6. Current formalization frontier

The exact combinatorial, geometric, signed-Gram, residual, canonical low-occupancy, lifetime-flow, death-shell identity, and shell-cardinality transfer layers are machine checked. On the PR #93 branch the next exact finite layer is the divisor-fiber injection

```text
#S_t ≤ ∑_{k in I_{Λ,t}} τ(k),
```

where `I_{Λ,t}` is the complete finite set of integer heights in the half-open shell window. A one-endpoint bound by `τ(2Λ(t+1))` is not a valid substitute.

The remaining theorem-level obligations are:

1. prove the native canonical high-sector estimate `(HS)`;
2. supply or import the classical Mertens-energy equivalence with RH as a theorem of exactly the required proposition type;
3. formalize the exact finite cofactor-`ω` parity decomposition on nonzero Möbius support, including `ω(c)=0`;
4. prove a genuine divisor-window asymptotic or a stronger cancellation estimate for the death shells;
5. control the endpoint survivor discrepancy `birth - death`, since death-process control alone is insufficient;
6. optionally prove stronger sufficient routes such as the square-block increment-energy or partial-moment balance premises.

Until those items are discharged, the repository remains an axiom-free conditional reduction rather than an unconditional proof of RH.
