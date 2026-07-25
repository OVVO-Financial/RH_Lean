from __future__ import annotations

from pathlib import Path

ROOT = Path(".")
OLD_FILE = Path("RHLean/Proof/SquarePrefixHeightPartition.lean")
NEW_FILE = Path("RHLean/Analysis/SquarePrefixHeightPartition.lean")

REPLACEMENTS = {
    "RHLean.Proof.SquarePrefixHeightPartition": "RHLean.Analysis.SquarePrefixHeightPartition",
    "RHLean/Proof/SquarePrefixHeightPartition.lean": "RHLean/Analysis/SquarePrefixHeightPartition.lean",
    "RHLean.Proof.CanonicalHighSectorBridge": "RHLean.Analysis.CanonicalHighSectorBridge",
    "RHLean/Proof/CanonicalHighSectorBridge.lean": "RHLean/Analysis/CanonicalHighSectorBridge.lean",
}

BOUNDARY_DOC = """# Paper / Analysis Boundary

This repository uses the source hierarchy as a content boundary.

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

`Proof/` contains active proof technology, superseded bridge tracks, and attempts to prove, strengthen, or replace unresolved estimates:

- candidate sufficient conditions not adopted into the paper;
- baseline, partial-moment, prime-interval, large-sieve, resonant, Gram, Lyapunov, and operator attack routes;
- experimental decompositions and conjectural interfaces;
- bridge theorems whose mathematical content is not part of the current manuscript.

A file is classified by whether its mathematical content is represented in the current paper, not solely by which implementation modules it imports. Lean's module graph must remain acyclic, but a paper-facing `Analysis` module may import supporting proof-technology declarations when the paper-facing theorem is packaged there.

## CI invariant

The CI script `scripts/check_paper_analysis_boundary.sh` enforces that no paper TeX source references Lean files or modules under `Proof`, `Arithmetic`, `Geometry`, `Kernel`, `CellMask`, or `Verification`. Paper-facing Lean source references must use only `RHLean/Analysis/` or `RHLean.Analysis.*`.

Every reclassification must also pass the assumption audit and `lake build RHLean --wfail`, which verify that the resulting import graph is valid and the project still compiles.

## Stacked migration sequence

The repository is being reorganized through green, merge-in-order pull requests:

1. classify paper-described mathematics under `Analysis/`;
2. classify proof technology and superseded bridge tracks under `Proof/`;
3. update every import, inventory, checklist, and paper module-path reference;
4. retain explicit unresolved premises and avoid changing theorem statements during architectural moves.

Each pull request must pass the assumption audit and `lake build RHLean --wfail` before the next stacked branch begins.
"""

BOUNDARY_CHECK = """#!/usr/bin/env bash
set -euo pipefail

if grep -RInE --include='*.tex' 'RHLean/(Proof|Arithmetic|Geometry|Kernel|CellMask|Verification)/|RHLean\\.(Proof|Arithmetic|Geometry|Kernel|CellMask|Verification)\\.' paper; then
  echo 'Paper Lean references must point only to RHLean/Analysis.' >&2
  exit 1
fi

echo 'Paper / Analysis boundary check passed.'
"""


def replace_all_paths() -> None:
    suffixes = {".lean", ".md", ".tex", ".sh"}
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in suffixes:
            continue
        text = path.read_text()
        updated = text
        for old, new in REPLACEMENTS.items():
            updated = updated.replace(old, new)
        if updated != text:
            path.write_text(updated)


def move_module() -> None:
    if OLD_FILE.exists():
        if NEW_FILE.exists():
            raise RuntimeError(f"destination already exists: {NEW_FILE}")
        NEW_FILE.parent.mkdir(parents=True, exist_ok=True)
        OLD_FILE.rename(NEW_FILE)
    elif not NEW_FILE.exists():
        raise RuntimeError("neither old nor new SquarePrefixHeightPartition path exists")


def verify() -> None:
    offenders: list[str] = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in {".lean", ".md", ".tex", ".sh"}:
            continue
        text = path.read_text()
        for old in REPLACEMENTS:
            if old in text:
                offenders.append(f"{path}: {old}")
    if offenders:
        raise RuntimeError("stale module paths remain:\n" + "\n".join(offenders))


def main() -> None:
    move_module()
    replace_all_paths()
    Path("PAPER_ANALYSIS_BOUNDARY.md").write_text(BOUNDARY_DOC)
    Path("scripts/check_paper_analysis_boundary.sh").write_text(BOUNDARY_CHECK)
    verify()


if __name__ == "__main__":
    main()
