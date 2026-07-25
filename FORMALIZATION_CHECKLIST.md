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
- [ ] **#72** — Moves the canonical arithmetic core into `Analysis`, proves sharp low-height occupancy on nonzero Möbius support, isolates `m=1`, constructs unconditional low-increment control, and removes the internal low-sector hypothesis from the native high-sector bridge.

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
- [x] **31. Concrete complete-family joint Gram realization** — PR #57.
- [ ] **32. Uniform full-family signed Gram estimate with all cross interactions retained** — optional sufficient strategy, not the minimal bridge.

### Phase X — native canonical bridge and cumulative smooth/transport hierarchy

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [x] **34. Canonical coherent-mean and centered-covariance decomposition** — PR #62.
- [x] **35. Exact square-block smooth/transport joint Gram realization** — PR #63.
- [x] **36. Strong square-block increment-energy sufficient hierarchy** — PR #64.
- [ ] **37. Generic deterministic baseline transport split** — PR #65.
- [ ] **38. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **39. Native canonical uniform local high-sector estimate `(HS)`**.

### Phase XI — finite signed-moment routes

- [ ] **40. Generic finite partial moments with the degree-one signed-sum identity and guarded ratio form**.
- [ ] **41. Sign-valued degree collapse for `{-1,0,1}` sequences**.
- [ ] **42. Real square-block increments and exact complex-cast bridge**.
- [ ] **43. Elementary square-block total-variation bound**.
- [ ] **44. Degree-one partial-moment balance sufficient criterion**.
- [ ] **45. Common-normalized signed empirical discrepancy sufficient criterion**.

### Phase XII — baseline energy and descriptive block structure

- [ ] **46. Exact baseline main/error signed joint-energy identity**.
- [ ] **47. Strong diagonal baseline-main plus baseline-error sufficient criterion**.
- [ ] **48. Generic finite atomic block bridge**.
- [ ] **49. Generic implied logarithmic-base transform**.
- [ ] **50. Deterministic Viole function definitions and midpoint interpolation**.
- [ ] **51. Correct Viole asymptotic expansion and explicit third-order bias**.

### Phase XIII — prime-count transport realization

- [ ] **52. Exact canonical largest-prime-factor transport reindexing into prime/cofactor pairs**.
- [ ] **53. Restricted pulled-back prime-interval realization with exact endpoints**.
- [ ] **54. Two-index baseline interval discrepancy identity**.
- [ ] **55. Triangular Möbius transport operator and finite Cauchy–Schwarz bounds**.
- [ ] **56. Cancellation-aware transport large-sieve premise as a sufficient route**.

### Phase XIV — further energy and weighted-moment routes

- [ ] **57. Increment coherent-mean and centered-energy decomposition**.
- [ ] **58. Weighted signed Möbius power-moment identities**.
- [ ] **59. Finite certificate checkers for partial moments, baselines, prime blocks, and transport operators**.

## 6. Current checkpoint

Principal definitions in `RHLean.Proof.ConcreteSquarePrefixHighResidual`:

- `zeroFareyModeLabel`;
- `squarePrefixHighShell`;
- `squarePrefixHighSourcePacketStart`;
- `squarePrefixHighSourcePacketLength`;
- `squarePrefixHighResidualAmplitude`;
- `squarePrefixHighResidualData`.

Principal theorems added by PR #54:

- `squarePrefixHighHeightExpansionRat_eq_pairSum`;
- `squarePrefixHighHeightExpansion_eq_channelSum`;
- `squarePrefixHighSourcePacket_range`;
- `squarePrefixHighResidualPacket_eq`;
- `actualResidual_squarePrefixHighResidualData_eq_channelSum`;
- `actualResidual_squarePrefixHighResidualData_eq_highHeightExpansion`.

Principal definitions in `RHLean.Proof.TriplingPacketTransport`:

- `normalizedFareyTransportEntry`;
- `normalizedFareyTransportPacket`;
- `squarePrefixHighTransportAmplitude`;
- `squarePrefixHighTransportData`;
- `triplingPhaseTransport`;
- `triplingBoundaryPacket`;
- `triplingTransportedBasePacket`;
- `triplingSignedDefect`;
- `SquarePrefixHighTriplingPair`;
- `squarePrefixHighTriplingModeContribution`;
- `squarePrefixHighTriplingModeDefect`.

Principal theorems added by PR #55:

- `actualResidualEntry_squarePrefixHighTransportData_ownShell`;
- `actualResidualPacket_squarePrefixHighTransportData_ownShell`;
- `orderedChannelEntryShell_le_tripled`;
- `normalizedFareyTransportPacket_eq_boundary_add_common`;
- `normalizedFareyTransportEntry_phaseAligned_cancel`;
- `normalizedFareyTransportEntry_add_two_tripled_eq_phaseDefect`;
- `normalizedFareyTransportPacket_add_two_tripled_eq_signedDefect`;
- `actualResidualPacket_squarePrefixHighTransportData_tripling_signedDefect`;
- `squarePrefixHighTriplingModeContribution_eq_defect`;
- `squarePrefixHighTriplingModeContribution_energy_eq_defect`.

Principal definitions in `RHLean.Proof.CompleteHighFamilyDecomposition`:

- `squarePrefixHighTriplingBases`;
- `squarePrefixHighTriplingChildren`;
- `squarePrefixHighTriplingCovered`;
- `squarePrefixHighUnpairedChannels`;
- `squarePrefixHighChannelModeContribution`;
- `squarePrefixHighTransportFamilyContribution`;
- `squarePrefixHighRetainedDefectContribution`;
- `squarePrefixHighRetainedChildCorrection`;
- `squarePrefixHighUnpairedModeContribution`.

Principal theorems added by PR #56:

- `tripledCofactorChannel_injective`;
- `squarePrefixHighTriplingBases_disjoint_children`;
- `squarePrefixHighTriplingCovered_union_unpaired`;
- `squarePrefixHighUnpairedChannels_reason`;
- `sum_squarePrefixHighHeightChannels_eq_pairs_add_unpaired`;
- `squarePrefixHighTransportFamilyContribution_eq_pair_add_unpaired`;
- `squarePrefixHighChannelModeContribution_add_two_tripled_eq_defect`;
- `squarePrefixHighChannelModeContribution_add_tripled_eq_defect_sub_tripled`;
- `squarePrefixHighRetainedPairContribution_eq_defect_sub_childCorrection`;
- `squarePrefixHighTransportFamilyContribution_eq_full_decomposition`.

Principal definitions in `RHLean.Proof.ConcreteHighFamilyJointGram`:

- `squarePrefixHighFullFamilyJointGramEnergy`;
- `SquarePrefixHighFullFamilyJointGramEstimateAt`;
- `SquarePrefixHighFullFamilyJointGramBoundedBy`.

Principal theorems added by PR #57:

- `actualResidualPacket_squarePrefixHighTransportData_offShell`;
- `squarePrefixHighTransportModeSum_eq`;
- `actualResidual_squarePrefixHighTransportData_eq_familyContribution`;
- `squarePrefixHighTransportFamily_energy_eq_jointGram`;
- `squarePrefixHighFullDecomposition_energy_eq_jointGram`;
- `squarePrefixHighTransportFamily_energy_le_of_jointGramEstimate`;
- `squarePrefixHighTransportFamily_energy_le_of_uniform_jointGramControl`.

Principal definitions in `RHLean.Proof.CanonicalHighSectorBridge`:

- `canonicalLargestPrimeFactor`;
- `canonicalCofactor`;
- `canonicalHeightTwice`;
- `canonicalSquareBlock`;
- `canonicalLowIncrement`;
- `canonicalHighIncrement`;
- `canonicalLowPrefix`;
- `canonicalHighPrefix`;
- `CanonicalLowIncrementControl`;
- `canonicalSquarePrefixGeometricPartition`;
- `CanonicalHighUniformLocalBoundedStatement`.

Principal theorems added by PR #60:

- `canonicalTotalIncrement_eq_low_add_high`;
- `canonicalTotalPrefix_eq_low_add_high`;
- `canonicalTotalPrefix_eq_squarePrefixMertens`;
- `squarePrefixMertens_eq_canonicalLow_add_high`;
- `norm_canonicalLowPrefix_le`;
- `canonicalLowPrefix_energy_le`;
- `canonicalHighUniformLocalBounded_iff_partition`;
- `canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded`;
- `canonicalHighUniformLocalBounded_iff_riemannHypothesis`.

Principal definitions in `RHLean.Proof.CanonicalHighSectorCovariance`:

- `localWindowSum`;
- `localWindowMean`;
- `localCoherentMeanEnergy`;
- `localCenteredCovarianceEnergy`;
- `SequenceUniformLocalBoundedStatement`;
- `CoherentMeanUniformLocalBoundedStatement`;
- `CenteredCovarianceUniformLocalBoundedStatement`;
- `CanonicalHighCoherentMeanUniformLocalBoundedStatement`;
- `CanonicalHighCenteredCovarianceUniformLocalBoundedStatement`.

Principal theorems added by PR #62:

- `localSequenceEnergy_eq_coherentMean_add_centeredCovariance`;
- `localCenteredCovarianceEnergy_one`;
- `localCoherentMeanEnergy_one`;
- `sequenceUniformLocalBounded_iff_coherentMean_and_centeredCovariance`;
- `canonicalHighUniformLocalBounded_iff_coherentMean_and_centeredCovariance`;
- `canonicalHighCoherentMean_and_centeredCovariance_iff_riemannHypothesis`.

Principal definitions in `RHLean.Proof.SquareBlockSmoothTransportGram`:

- `squareBlockSmoothIncrement`;
- `squareBlockTransportIncrement`;
- `squareBlockSmoothPrefix`;
- `squareBlockTransportPrefix`;
- `squareBlockSmoothTransportResidual`;
- `squareBlockLocalSmoothEnergy`;
- `squareBlockLocalTransportEnergy`;
- `squareBlockLocalSmoothTransportInteraction`;
- `squareBlockSmoothTransportJointEnergy`;
- `SquareBlockSmoothTransportGramBound`.

Principal theorems added by PR #63:

- `canonicalTotalIncrement_eq_smooth_sub_transport`;
- `canonicalTotalPrefix_eq_smooth_sub_transport`;
- `squareBlockSmoothTransportResidual_eq_squarePrefixMertens`;
- `squareBlockSmoothTransportJointEnergy_eq_localResidualEnergy`;
- `squareBlockSmoothTransportJointEnergy_eq_squarePrefixLocalEnergy`;
- `squareBlockSmoothTransportJointEnergy_eq_coherentMean_add_centeredCovariance`;
- `squareBlockSmoothTransportGramBound_iff_squarePrefixUniformLocalBounded`;
- `squareBlockSmoothTransportGramBound_iff_riemannHypothesis`.

Principal definition in `RHLean.Proof.SquareBlockIncrementEnergy`:

- `SquareBlockIncrementEnergyBoundedStatement`.

Principal theorems added by PR #64:

- `squareBlockSmoothTransportResidual_eq_sum_increment`;
- `norm_squareBlockSmoothTransportResidual_sq_le_of_incrementEnergy`;
- `squarePrefixCurrentPointwiseBounded_of_incrementEnergy`;
- `squarePrefixUniformLocalBounded_of_incrementEnergy`;
- `squareBlockSmoothTransportGramBound_of_incrementEnergy`;
- `riemannHypothesis_of_squareBlockIncrementEnergy`.

Principal definitions in `RHLean.Proof.SquareBlockTransportBaseline`:

- `squareBlockEndpointReal`;
- `squareBlockBaselineTransportApprox`;
- `squareBlockBaselineTransportError`;
- `squareBlockBaselineMainIncrement`;
- `squareBlockBaselineMainPrefix`;
- `squareBlockBaselineTransportErrorPrefix`.

Principal theorems added by PR #65:

- `squareBlockTransportIncrement_eq_baselineApprox_add_error`;
- `canonicalTotalIncrement_eq_baselineMain_sub_error`;
- `squareBlockSmoothTransportResidual_eq_baselineMain_sub_error`;
- `squarePrefixMertens_eq_baselineMain_sub_error`.

The native largest-prime-factor canonical sequence is compiled separately from the normalized ordered-pair/Farey family. Its exact block increments and cumulative low/high prefixes recombine to `squarePrefixMertens`, and `CanonicalHighUniformLocalBoundedStatement Λ` is proved equivalent to the total local criterion and, from the ordinary `ClassicalMertensRHCriterion` argument, to RH. No project axiom is introduced.

The generic baseline layer is only an exact coordinate decomposition of the native transport. It does not identify transport with a prime-counting interval sum, select `Li` or the Viole function, or infer an analytic estimate.

The complete future criterion lattice and dependency gates are recorded in `MULTIROUTE_FORMALIZATION_PLAN.md`.

## 7. Remaining obligations

- prove the manuscript's elementary canonical low-block estimate and construct `CanonicalLowIncrementControl Λ` with manuscript bound `⌊Λ⌋` for nontrivial sources, with the isolated `m=1` term handled separately or absorbed by `⌊Λ⌋+1`;
- prove the native canonical uniform local high-sector estimate `CanonicalHighUniformLocalBoundedStatement Λ` — `(HS)`;
- import or formalize the classical theorem
  `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`;
- optionally prove an exact realization from the normalized Farey/transport family to the native canonical high sequence, then establish its full signed Gram estimate as a sufficient route to `(HS)`;
- optionally prove the new partial-moment, signed-discrepancy, baseline-energy, prime-interval, transport-operator, weighted-moment, and finite-certificate routes in the order recorded by `MULTIROUTE_FORMALIZATION_PLAN.md`;
- keep every new route one-way into the compiled pointwise/local criteria unless a reverse implication is separately proved.

Merge-gating commands remain:

```bash
bash scripts/audit_assumptions.sh
lake build RHLean --wfail
```
