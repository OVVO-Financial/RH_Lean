# RH_Lean formalization checklist

This file is the mandatory closeout record for every pull request in `RH_Lean`.

`FORMALIZATION_SEQUENCE.md` remains the single source of truth for theorem dependency order. This checklist records the exact execution process, non-negotiable proof rules, visible completion status, and the append-only ledger of successful PRs.

A PR is not complete unless this file is updated on the same branch. Because a checked ledger entry reaches `main` only when that PR is merged, every `[x]` entry visible on `main` records a successful PR.

The closeout state must be prepopulated on the implementation branch before the substantive CI run intended to gate merge. Do not create a post-green documentation-only commit merely to record that CI passed. Once the substantive checks are green, merge the already-prepopulated branch unless a substantive correction is required.

## 1. Non-negotiable proof rules

Every PR must preserve all of the following:

- no `sorry`, `admit`, new axioms, line-leading opaque constants, or theorem substitutes;
- no weakened theorem statements, changed indexing, hidden assumptions, or circular RH premises;
- no use of RH, an equivalent form of RH, or a result whose proof assumes RH before the final bridge;
- use the exact pinned Lean/mathlib toolchain, currently Lean 4 and mathlib `v4.24.0`;
- inspect APIs at the pinned mathlib tag before writing version-sensitive proofs;
- use modulus `2 * r`, never modulus `r`, for the quadratic prime phase;
- keep the prime-3 rational cell-mask energy separate from the complex quadratic prime-phase factor;
- keep the full signed shell sum inside the norm and retain cross-shell Gram terms;
- keep theorem-predicted rank-one subtraction separate from true orthogonal projection;
- introduce numerical finite-range claims only through a proved certificate checker;
- keep accepted-certificate validity separate from the mathematical realization that identifies checked data with actual theorem quantities;
- do not infer the sharp constant-`4` starting frame inequality from residual size alone; retain the signed prediction-residual interaction explicitly;
- treat every warning as a CI failure because the project builds with `--wfail`.

## 2. Per-PR execution checklist

Copy this task list into the pull-request description and prepopulate it on the implementation branch before the substantive merge-gating CI run:

- [ ] Confirm the preceding PR is green and merged; read the current `main` head.
- [ ] Read `FORMALIZATION_SEQUENCE.md` and this checklist.
- [ ] Select exactly one dependency-bounded theorem or documentation layer.
- [ ] State what the PR proves, what it does not prove, and the next dependency.
- [ ] Inspect exact theorem names and signatures at mathlib `v4.24.0`.
- [ ] Branch from current `main` as `agent/<focused-description>`.
- [ ] Implement the smallest stable module or documentation change.
- [ ] Import every new theorem module from `RHLean.lean`.
- [ ] Prepopulate `FORMALIZATION_SEQUENCE.md` with the completed layer, compiled inventory, checkpoint, and next dependency.
- [ ] Prepopulate this checklist with explicit `[x]` and `[ ]` status markers and the successful-PR ledger entry.
- [ ] Prepopulate the pull-request description with the execution checklist and closeout record.
- [ ] Pass `bash scripts/audit_assumptions.sh`.
- [ ] Pass `lake build RHLean --wfail` with no warnings.
- [ ] Fix only failures observed in exact CI logs.
- [ ] After three failed substantive attempts, request the complete job log as a diagnostic delimiter and continue until green.
- [ ] Do not add a documentation-only commit after green CI merely to record the result; GitHub check status is authoritative.
- [ ] If a substantive correction changes the branch after CI, update the prepopulated closeout state with that correction and rerun the required checks.
- [ ] Merge only after green CI and explicit authorization.
- [ ] Begin the next PR only after confirming the merge on current `main`.

## 3. Required PR closeout record

Each PR description and prepopulated checklist update must identify:

- PR number and title;
- theorem layer or documentation layer completed;
- principal new modules or files;
- central changes and proved statements;
- invariants protected;
- CI commands that gate merge;
- next dependency in `FORMALIZATION_SEQUENCE.md`.

The final CI result belongs in GitHub's check status and may also be recorded in the PR description without changing repository files. A green result never requires a follow-up documentation-only commit.

## 4. Successful PR ledger

This ledger is append-only. A checked entry visible on `main` means that PR reached `main` through the required review and CI process.

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
- [x] **#24** — Proved exact small-modulus resonance at moduli `6` and `24`, including the normalized `(a,r)=(1,3)` factor and its norm-one theorem.
- [x] **#25** — Established the mandatory closeout checklist and refreshed the Phase I checkpoint.
- [x] **#26** — Added explicit `[x]`/`[ ]` completion markers to the checklist and canonical roadmap.
- [x] **#27** — Proved the exact rational prime-3 cell-mask mean `1/3` and squared mean-mode energy `1/9` in a dedicated namespace.
- [x] **#28** — Proved exact `2ab` finite differences, linear common-shift displacement, monotonicity, and vertical-window lifetime criteria.
- [x] **#29** — Proved exact reduced square-class phase support modulo `40`, with eligible prime phases confined to the class-`1` and class-`9` modes.
- [x] **#30** — Proved the exact height-shell Gram identity with every off-diagonal real inner product retained and the full signed shell sum kept inside the norm.
- [x] **#31** — Defined the true orthogonal coefficient and residual, proved exact orthogonality and Pythagorean energy decomposition, and kept theorem-predicted subtraction separate.
- [x] **#32** — Defined the scale-dependent cutoff and canonical modulus-`2r` resonant modes, exposed the resonant span and extraction skeleton, and proved only exact algebraic recombination.
- [x] **#33** — Exposed the four resonant/nonresonant block maps and exact affine recurrence with low-height, endpoint, and boundary forcing kept explicit.
- [x] **#34** — Proved the abstract full weighted block-contraction closure with an explicit invariant bound and a decay-weighted forcing corollary.
- [x] **#35** — Defined the explicitly indexed actual residual, connected it to scale-dependent resonant extraction, proved declared-span membership and exact algebraic recombination, and packaged it as the separately typed state used by the leakage and Lyapunov layers.
- [x] **#36** — Formalized exact scale-dependent resonant cancellation for explicitly compatible odd/doubled Möbius cofactor pairs while retaining every denominator-mode and cofactor interaction.
- [x] **#37** — Proved low-height spacing-to-incidence, endpoint, boundary, rowwise, and weighted actual forcing estimates for the compiled leakage and Lyapunov interfaces.
- [x] **#38** — Formalized the complete shell/cofactor/mode/row joint index, exact recombination to the actual residual, and the full signed joint Gram control interface.
- [x] **#39** — Added the sound executable finite-range certificate checker, exact metadata and payload validation, and the accepted-certificate import boundary.
- [x] **#40** — Connected accepted finite-range data to actual joint energies through an explicit realization, packaged asymptotic full-joint recurrence control, and proved the uniform actual residual-energy bound.
- [x] **#41** — Defined the exact actual-start configuration, retained its signed prediction-residual interaction, and derived the sharp constant-`4` finite-prefix frame inequality from uniform residual control plus explicit signed absorption.

## 5. Theorem-layer completion checklist

### Phase I — corrected complex quadratic-phase layer

- [x] **1. Complex quadratic phase API** — PR #21.
- [x] **2. Exact shift-by-`r` sign law** — PR #22.
- [x] **3. Corrected reduced quadratic Gauss factor** — PR #23.
- [x] **4. Exact small-modulus resonance** — PR #24.

### Phase II — remaining exact combinatorial and geometry layers

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

- [x] **13. Resonant/nonresonant decomposition of the actual residual** — PR #35.
- [x] **14. Explicit resonant cancellation across Möbius-weighted cofactor channels** — PR #36.
- [x] **15. Low-height spacing, incidence, endpoint, and boundary estimates** — PR #37.
- [x] **16. Joint Gram control** — PR #38.
- [x] **17. Certified finite-range certificate checker** — PR #39.
- [x] **18. Uniform full residual bound** — PR #40.
- [x] **19. Actual-start signed-frame theorem** — anticipated PR #41.
- [ ] **20. RH bridge** — next dependency.

## 6. Current checkpoint

Anticipated PR #41, **Formalize the actual-start signed-frame theorem**, completes Phase IV item 19 on the implementation branch.

- Principal new module: `RHLean.Analysis.ActualStartSignedFrame`.
- Principal structures:
  - `ActualStartConfiguration`;
  - `ActualStartSignedFrameControl`.
- Principal definitions:
  - `actualStartFrameEnergy`;
  - `actualStartPredictionFrameEnergy`;
  - `actualStartResidualFrameEnergy`;
  - `actualStartSignedInteraction`.
- Principal theorems:
  - `actualStart_energy_identity_at`;
  - `actualStart_frame_energy_identity`;
  - `actualStart_residualFrameEnergy_le`;
  - `actualStart_signedFrame_of_uniform_residual_bound`;
  - `actualStart_signedFrame`.
- Exact starting configuration:

  ```text
  actual(M) = 2 * prediction(M) + actualResidual(M).
  ```

- Exact finite-prefix signed identity:

  ```text
  actualFrameEnergy(N)
    = 4 * predictionFrameEnergy(N)
      + residualFrameEnergy(N)
      + signedPredictionResidualInteraction(N).
  ```

- Uniform residual accumulation:

  ```text
  residualFrameEnergy(N)
    ≤ N * affineInvariantBound.
  ```

- Explicit signed absorption:

  ```text
  signedPredictionResidualInteraction(N)
    ≤ -N * affineInvariantBound.
  ```

- Final frame conclusion:

  ```text
  actualFrameEnergy(N) ≤ 4 * predictionFrameEnergy(N)
  ```

  for every finite prefix `N`.
- Protected invariants:
  - the theorem-predicted coefficient `2` is an exact starting identity, not an orthogonal coefficient claim;
  - the residual is the compiled actual residual controlled through the full signed joint Gram;
  - the prediction-residual cross term remains signed and visible;
  - the sharp constant `4` is not inferred from residual size alone;
  - all finite-range realization and asymptotic-control instances remain explicit;
  - no componentwise shell, cofactor, row, or denominator-mode positivity estimate is introduced;
  - no RH premise or equivalent statement appears.
- Deliberate exclusions:
  - no numerical run is imported;
  - no automatic certificate realization or asymptotic contraction is claimed;
  - no orthogonality or Pythagorean identity is asserted for the theorem-predicted coefficient;
  - no RH bridge is stated.
- Pinned API inspection:
  - exact compiled signatures were checked for `norm_add_sq`, `norm_smul`, `Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_le_sum`, `shellReInner`, and `uniform_actualResidual_energy_bound` against Lean 4 / mathlib `v4.24.0`.
- Merge-gating validation commands: `bash scripts/audit_assumptions.sh` and `lake build RHLean --wfail`.

## 7. Next dependency

The next focused PR is unchecked item **20: RH bridge**.

It must use the completed actual-start signed-frame theorem without introducing RH or an equivalent statement as a premise. The exact bridge theorem and every external equivalence used by it must be inspected and stated explicitly before implementation.
