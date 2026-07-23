# RH_Lean formalization checklist

This file is the mandatory closeout record for every pull request in `RH_Lean`.

`FORMALIZATION_SEQUENCE.md` remains the single source of truth for theorem dependency order. This checklist records the exact execution process, non-negotiable proof rules, and the append-only ledger of successful PRs.

A theorem PR is not complete unless this file is updated on the same branch. Because the new ledger entry reaches `main` only when that PR is merged, every entry visible on `main` records a successful PR.

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
- treat every warning as a CI failure because the project builds with `--wfail`.

## 2. Exact PR process

Every formalization PR follows this order.

1. **Confirm the base.** Verify that the preceding PR is green and merged, then read the current `main` head.
2. **Read the roadmap.** Read `FORMALIZATION_SEQUENCE.md` and this checklist before selecting work.
3. **Select one dependency-bounded layer.** Choose the next theorem layer, not a collection of unrelated results.
4. **State scope before implementation.** Record what the PR proves, what it deliberately does not prove, and the next dependency.
5. **Inspect pinned APIs.** Check exact theorem names and signatures at mathlib `v4.24.0`; do not rely on a newer snapshot.
6. **Branch from current `main`.** Use an `agent/<focused-description>` branch.
7. **Implement the smallest stable module.** Prefer exact algebraic statements before analytic estimates and generic lemmas before number-theoretic instantiations.
8. **Wire the compiled root.** Import every new theorem module from `RHLean.lean`.
9. **Update project state.** Update `FORMALIZATION_SEQUENCE.md` whenever the compiled inventory or current checkpoint changes.
10. **Update this checklist.** Append the PR ledger entry and revise the current checkpoint and next dependency.
11. **Run the source audit.** `bash scripts/audit_assumptions.sh` must pass.
12. **Run the warning-fatal build.** `lake build RHLean --wfail` must pass with no warnings.
13. **Fix only observed failures.** Read the exact CI log, make a focused correction, and rerun CI; do not guess at APIs.
14. **Merge only after green CI.** The assistant does not merge unless explicitly instructed.
15. **Begin the next PR only after merge confirmation.** Re-read `main`, the sequence, and this checklist before continuing.

## 3. Required PR closeout record

Each PR description and checklist update must identify:

- PR number and title;
- theorem layer or documentation layer completed;
- principal new modules or files;
- central proved statements;
- invariants protected;
- CI command and final result;
- next dependency in `FORMALIZATION_SEQUENCE.md`.

## 4. Successful PR ledger

This ledger is append-only. An entry visible on `main` means that PR reached `main` through the required review and CI process.

| PR | Successful layer |
|---:|---|
| #1 | Initialized Lean 4/Lake, pinned mathlib `v4.24.0`, added CI/source audit, Fermat coordinates, and fixed packets. |
| #2 | Added the exact dyadic-cell paper section. |
| #3 | Integrated the dyadic theorem material into the paper branch. |
| #4 | Added deterministic manuscript integration for the exact dyadic cell theorem. |
| #5 | Proved exact Möbius doubling on odd inputs. |
| #6 | Proved exact four-slot Möbius compression. |
| #7 | Proved universal prime-3 activation and its deterministic cycle. |
| #8 | Proved squared complex factor recovery. |
| #9 | Corrected the architecture to modulus `2r` and separated cell-mask and prime-phase mechanisms. |
| #10 | Replaced shellwise smallness with full signed Gram control and explicit block-contraction architecture. |
| #11 | Proved square residues modulo `24`. |
| #12 | Proved the prime-square wrapper modulo `24`. |
| #13 | Proved quadratic numerator periodicity. |
| #14 | Defined and proved quadratic exponent congruence modulo `2r`. |
| #15 | Proved prime square classes `1` or `9` modulo `40`. |
| #16 | Proved the quadratic shift-by-`r` arithmetic dichotomy. |
| #17 | Proved exact cofactor parabola identities. |
| #18 | Proved exact conformality identities for the complex square map. |
| #19 | Proved the two-sheeted complex square fiber theorem and positive-branch injectivity. |
| #20 | Established `FORMALIZATION_SEQUENCE.md` as the canonical dependency roadmap. |
| #21 | Defined the corrected complex quadratic phase and proved exact `2r` periodicity. |
| #22 | Proved the exact shift-by-`r` complex sign law. |
| #23 | Defined the reduced quadratic Gauss factor over `(ZMod (2 * r))ˣ` and its totient normalization. |
| #24 | Proved exact small-modulus resonance at moduli `6` and `24`, including the normalized `(a,r)=(1,3)` factor and its norm-one theorem. |
| Checklist policy PR | Establishes this mandatory closeout checklist and refreshes the canonical sequence after Phase I. |

## 5. Current checkpoint

Phase I of the corrected complex quadratic-phase layer is complete:

- complex quadratic phase API: complete;
- exact shift-by-`r` sign law: complete;
- reduced quadratic Gauss factor over `(ZMod (2 * r))ˣ`: complete;
- exact small-modulus resonance and norm-one coherence at `(a,r)=(1,3)`: complete.

The prime-3 complex phase result remains strictly separate from the rational cell-mask mean energy.

## 6. Next dependency

The next focused PR is **Phase II, item 5: prime-3 cell-mask mean energy**.

It must:

- introduce the dedicated cell-mask namespace/module;
- prove the exact rational-valued mean-energy statement;
- preserve type separation from the complex prime-phase factor;
- avoid treating `1/9` as a bound on the normalized quadratic Gauss factor.
