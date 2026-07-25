# Paper / Analysis Boundary

This repository uses the source hierarchy as an epistemic boundary.

## `RHLean/Analysis/`

`Analysis/` contains the Lean formalization of mathematics that is part of the paper:

- exact arithmetic identities and realizations;
- canonical factor and square-block geometry;
- exact low/high, smooth/transport, projection, residual, and Gram identities appearing in the manuscript;
- the square-prefix pointwise/local/Mertens equivalence spine;
- paper-stated conditional interfaces, with every unresolved premise explicit;
- proved elementary estimates stated in the paper, including canonical low-height occupancy.

The paper may reference Lean source files only under `RHLean/Analysis/`.

## `RHLean/Proof/`

`Proof/` contains active attempts to prove, strengthen, or replace the unresolved estimates:

- candidate sufficient conditions not adopted into the paper;
- baseline, partial-moment, prime-interval, large-sieve, and operator attack routes;
- experimental decompositions and conjectural interfaces;
- bridge theorems whose mathematical content is not yet part of the manuscript.

A result moves from `Proof/` to `Analysis/` only when the corresponding mathematics is incorporated into the paper and the dependency direction remains acyclic.

## Dependency invariant

An `Analysis` module must never import a `Proof` module. `Proof` may import `Analysis`.

The CI script `scripts/check_paper_analysis_boundary.sh` enforces:

1. no `RHLean/Analysis/**/*.lean` file imports `RHLean.Proof.*`;
2. no paper TeX source references Lean files or modules under `Proof`, `Arithmetic`, `Geometry`, `Kernel`, `CellMask`, or `Verification`;
3. paper-facing Lean source references use only `RHLean/Analysis/` or `RHLean.Analysis.*`.

## Stacked migration sequence

The repository is being reorganized through green, merge-in-order pull requests:

1. establish and enforce this boundary;
2. move manuscript arithmetic and small-prime modules into `Analysis/`;
3. move manuscript geometry, fibre, and fixed-packet modules into `Analysis/`;
4. move manuscript exact realization, height partition, transport, and signed-Gram modules into `Analysis/`;
5. move or wrap the manuscript certificate interface under `Analysis/`;
6. update the paper's Lean inventory and status language so it references only `Analysis/` sources;
7. retain post-paper attack routes under `Proof/`.

Each pull request must pass the assumption audit and `lake build RHLean --wfail` before the next stacked branch begins.
