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
- exact `2ab` source transfer, square-root inversion, and prime-first Fubini are realization theorems, not contraction estimates;
- low-to-high prime transport must retain prime density and the full signed scale-transfer discrepancy; raw Euclidean interval scaling is not an analytic substitute;
- dyadic compression preserves the full signed process: it replaces common suffixes by explicit boundary packets but is not itself an operator contraction;
- the compressed high transport family is the `P+(m)>R` part of the complete odd annulus, not the full annulus;
- a transport-only energy premise must not be labeled the protected RH criterion without separate smooth-complement or signed-interaction control;
- finite correlation, regression, and baseline-fit claims are diagnostics unless accepted through an explicit certificate checker;
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
- [x] **#93** — Added the exact injection of every positive-cutoff death shell into divisor fibers over the full integer shell window, the resulting divisor-sum cardinality bound, and its death-process consequences.
- [x] **#94** — Proved the exact finite cofactor-`ω` parity decomposition of each positive-cutoff death increment, including `ω(c)=0` and removal of zero Möbius terms.
- [x] **#95** — Formalized exact `2ab` source transfer, square-root inversion, prime-dilation Fubini, baseline-scaled low plus full discrepancy, and the reproducible finite-range experiment without claiming an asymptotic estimate.
- [x] **#96** — Proved exact dyadic parent/child packet cancellation, complete odd-cofactor transport reindexing, canonical source coordinates and signs, explicit boundary classification, and the complete odd dyadic-annulus Mertens identity.

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
- [x] **52. Exact death-shell divisor-fiber bound** — PR #93.
- [x] **53. Exact finite cofactor-`ω` parity decomposition** — PR #94.

### Phase XII — exact `2ab` scale transfer

- [x] **54. Exact source and finite-family `entered = smooth - transport` realization** — PR #95.
- [x] **55. Canonical dynamic smooth-minus-transport and exact `2ab` dilation** — PR #95.
- [x] **56. Baseline-scaled low plus complete signed discrepancy identity** — PR #95.
- [x] **57. Finite cofactor-first/prime-first transport Fubini identity** — PR #95.

### Phase XIII — exact dyadic transport compression

- [x] **58. Odd-parent/doubled-child packet cancellation and residual boundary packet** — PR #96.
- [x] **59. Complete lower-cofactor prefix compression and transport reindexing** — PR #96.
- [x] **60. Canonical high-source side conditions, largest-prime identity, and source sign** — PR #96.
- [x] **61. Complete odd dyadic-annulus realization of square-prefix Mertens** — PR #96.

## 6. Current formalization frontier

The exact combinatorial, geometric, signed-Gram, residual, canonical low-occupancy, lifetime-flow, death-shell, `2ab` scale-transfer, and dyadic-compression layers are machine checked. The merged exact identities now include

```text
entered = smooth - transport,
squarePrefixMertens = squareRootSmoothMass - squareRootTransportMass,
iota_R(x)=R^2/x,
cofactor-first transport pairs = prime-first lower-cofactor fibers,
parent packet + doubled-child packet = dyadic boundary packet,
T_R = sum_{R<q≤X, q prime} sum_{c odd, X<2cq≤2X} mu(c),
-T_R = the corresponding canonical source-sign sum,
M(B) = sum_{m odd, B<2m≤2B} mu(m).
```

The reproducible `2ab` experiment verifies its finite identities with zero integer error through `R=10000`; those numerical results remain diagnostics rather than asymptotic theorems. The transport-only high subset is not substituted for the complete annulus or the full `A-T` residual.

The remaining theorem-level obligations are:

1. prove the native canonical high-sector estimate `(HS)`, or a sufficient route implying the protected pointwise/local criterion;
2. supply or import the classical Mertens-energy equivalence with RH as a theorem of exactly the required proposition type;
3. formalize the reciprocal kernel `K_R(d)`; the prime-first finite fiber and its odd dyadic compression are now machine checked;
4. prove a cancellation-aware dyadic smooth/high joint estimate or signed scale-transfer discrepancy estimate, retaining the born-smooth remainder and full interaction;
5. prove a genuine divisor-window asymptotic or a stronger cancellation estimate for the death shells;
6. control the endpoint survivor discrepancy `birth - death`, since death-process control alone is insufficient;
7. optionally prove stronger sufficient routes such as the square-block increment-energy or partial-moment balance premises.

Until those items are discharged, the repository remains an axiom-free conditional reduction rather than an unconditional proof of RH.


## Append-only reconciliation: PRs #172 and #173

### PR #172 — research route registry

- [x] `RESEARCH_ROUTE_REGISTRY.md` added.
- [x] Exact identities are separated from tested/open analytic routes.
- [x] Spectral-gap, positive-Gram, and no-overshoot obligations remain explicitly open.
- [x] No theorem module or root import was introduced by this documentation-only PR.

### PR #173 — Euler–CRT roughness recursion

- [x] `RHLean/Analysis/EulerCRTRoughnessRecursion.lean` added.
- [x] `RHLean.Analysis.EulerCRTRoughnessRecursion` imported by `RHLean.lean`.
- [x] Exact rough Möbius wheel recursion compiled.
- [x] Exact rough Mertens wheel recursion compiled.
- [x] Boundary audit passed on the merged PR.
- [x] Assumption audit passed on the merged PR.
- [x] `lake build RHLean --wfail` passed on the merged PR.
- [ ] No extension-compatible quadratic inequality has been proved.
- [ ] No completed-endpoint bound has been proved.
- [ ] No interior no-overshoot theorem has been proved.

### Current next dependency

- [x] Exact `30 -> 210` signed child operator audited.
- [x] Exact arithmetic compatibility quotient identified as 14-dimensional.
- [x] Self-similar Hamming-level diagonal flip-energy ansatz eliminated by an exact separating certificate.
- [ ] Audit the full mask-specific diagonal family on the 14-dimensional quotient.
- [ ] If diagonal feasibility fails, produce an exact rational dual certificate before moving to genuinely off-diagonal forms.
- [ ] Any feasible rule must be tested for extension closure on the 31-dimensional `210 -> 2310` quotient.

## Append-only reconciliation: PRs #175, #176, #177

### PR #175 — formalization document reconciliation

- [x] `FORMALIZATION_SEQUENCE.md` root inventory rederived from the live `RHLean.lean` import surface (145 theorem modules).
- [x] PRs #172 and #173 recorded in this ledger.
- [x] Euler–CRT slice placed before any extension-compatible spectral, Gram, endpoint, or no-overshoot estimate.
- [x] Documentation only; no Lean source or theorem statement changed.

### PR #176 — mask-specific diagonal Gram audit

- [x] `research/MASK_SPECIFIC_DIAGONAL_30_210.md` added.
- [x] `scripts/MaskSpecificDiagonalAudit/verify.py` added (standard library only).
- [x] Exact rational dual certificate: any non-circular diagonal family needs parent budget `>= 368/3`.
- [x] No Lean source, axiom surface, or protected-chain import changed.
- [ ] Classification narrowed by the later dichotomy audit: the certificate refutes the seed constant `2`, not the diagonal family. See below.

### PR #177 — off-diagonal quotient tautology

- [x] `research/OFFDIAGONAL_QUOTIENT_TAUTOLOGY_30_210.md` added.
- [x] `scripts/OffDiagonalQuotientTautology/verify.py` added (standard library only).
- [x] Rank-one off-diagonal form shown feasible with exact parent budget `25/6 < 16`.
- [x] No Lean source, axiom surface, or protected-chain import changed.
- [ ] `V_210` misidentified as the null space of `chi_31`; the missing mask is `15`. Verdict "not quotient-stable" withdrawn. See below.

## Append-only: Gram/Lyapunov dichotomy cycle

### Research artifacts

- [x] `research/GRAM_LYAPUNOV_DICHOTOMY.md` added.
- [x] `scripts/GramLyapunovDichotomy/verify.py` added (standard library only; recomputes every prior published row rather than importing it).
- [x] Zero-direct-square dichotomy proved exactly.
- [x] Missing full-old-wheel-mask lemma proved exactly and checked at three consecutive primorial extensions.
- [x] Tautology regeneration proved at `30 -> 210`, `210 -> 2310`, `2310 -> 30030`.
- [x] Trajectory-pinning sandwich proved exactly; band factors below 5 through `(30030, 510510]`.
- [x] PR #176 reclassified from CLOSED to OPEN AT A LARGER CONSTANT (`c >= 46/3`).
- [x] PR #177 `V_210` misidentification confirmed and corrected.
- [x] `RESEARCH_ROUTE_REGISTRY.md` records the closed sub-route.
- [ ] Growth of the required constant `c_k` across two consecutive extensions: NOT TESTED.

### Lean slice — VERIFIED by PR #178 / CI run #697

- [x] `roughInterval` and `roughInterval_wheel_recursion` added to `RHLean/Analysis/EulerCRTRoughnessRecursion.lean`.
- [x] `scripts/check_paper_analysis_boundary.sh` passed.
- [x] `scripts/audit_assumptions.sh` passed.
- [x] `lake build RHLean --wfail` passed. Lean verification run **#697** (`30728380660`) on PR #178, head `85d1d28454713ac712fad0860b08d8c07b27d0f8`, merge commit `43a6262b6d356597074a7fafb58ca602e82b8d61`, merged 2026-08-02.
- [x] `roughInterval` and `roughInterval_wheel_recursion` are therefore classified **LEAN-FORMALIZED**.

The provisional "NOT RUN / must not be treated as formalized" marking recorded when
this slice was written is superseded: it reflected a session runtime whose network
policy blocked `release.lean-lang.org`, preventing local compilation, and a
`pull_request`-triggered `lean.yml` that produced no run on a bare branch push.
Both were resolved by opening PR #178.

### Current next dependency

- [x] Audit the full mask-specific diagonal family on the 14-dimensional quotient (PR #176).
- [x] Test genuinely off-diagonal forms (PR #177).
- [x] Determine whether the declared next family is non-empty: it is not (dichotomy).
- [ ] Reproduce the PR #176 dual construction at `210 -> 2310` and report the required constant `c_k` at two consecutive extensions.
- [ ] Solve the state-closure problem: an induction state preserved by prime extension on which parent and child bounds concern the same object.

## Append-only: required-constant growth test

### Research artifacts

- [x] `research/DIAGONAL_REQUIRED_CONSTANT_GROWTH.md` added.
- [x] `scripts/DiagonalConstantGrowth/verify.py` added (standard library only; embeds two-sided exact rational certificates).
- [x] LP dual shown equivalent to the PR #176 certificate structure; `368/3` reproduced as the exact optimum of its own test family.
- [x] Exact dual certificate at `30 -> 210`: `b_1 >= 7819/216`, so `c_1 >= 7819/1728 = 4.5248843...`.
- [x] Exact primal certificate at `210 -> 2310`: `b_2 <= 23511351/250000`, so `c_2 <= 7837117/4000000 = 1.9592793...`.
- [x] Predeclared growth test discharged: the required constant FALLS, ratio at most `0.4330`.
- [x] Same direction reproduced by four independent test families.
- [x] PR #176 confirmed **OPEN AT A LARGER CONSTANT** by direct measurement.
- [x] State-closure obstruction identified exactly as an interval mismatch (wheel-depth recursion versus per-block budget).
- [ ] `c_3` at `2310 -> 30030`: NOT COMPUTED — the floating-point LP breaks down at that dynamic range.
- [ ] True minimal constants (full quantified constraints, not a finite test family): NOT DETERMINED.
- [ ] State closure itself: STILL OPEN.

### Lean

- [x] No Lean source, axiom surface, or protected theorem-chain import changed by this cycle.

### Current next dependency

- [x] Reproduce the PR #176 dual construction at `210 -> 2310` and report `c_k` at two consecutive extensions.
- [ ] Recompute `c_3` with exact or better-conditioned arithmetic to extend the growth test to a third extension.
- [ ] Solve the prime-extension state-closure problem: an induction state on which the parent and child bounds concern the same object, bridging wheel-depth recursion and per-block budget.
