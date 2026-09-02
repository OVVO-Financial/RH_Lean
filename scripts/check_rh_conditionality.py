#!/usr/bin/env python3
"""Report which RH-facing theorems are still conditional on an assumed criterion.

`#print axioms` is necessary but **not sufficient** for the terminal acceptance
test.  `ClassicalMertensRHCriterion` is a structure taken as an ordinary theorem
*argument*, not an axiom, so a theorem that assumes it has a perfectly clean
axiom printout while remaining conditional on an unproved classical equivalence.

This script makes that visible mechanically.  It scans every declaration's
signature -- the text between the declaration keyword and the `:=` that begins
its proof -- and reports the ones that carry a flagged open hypothesis.

Usage:

    python3 scripts/check_rh_conditionality.py                 # report
    python3 scripts/check_rh_conditionality.py --list          # full listing
    python3 scripts/check_rh_conditionality.py \\
        --require-unconditional theoremName                    # acceptance test

The acceptance test for a terminal RH theorem is BOTH of:

  1. `--require-unconditional <name>` passes, i.e. the classical equivalence has
     actually been instantiated rather than assumed; and
  2. `#print axioms <name>` reports only the standard logical axioms.

Neither implies the other.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SOURCE_ROOT = Path("RHLean")

# Hypotheses whose presence in a signature makes the conclusion conditional on
# something this repository does not prove.
FLAGGED = ("ClassicalMertensRHCriterion",)

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|structure|abbrev)\s+([A-Za-z_][\w'.]*)",
    re.M,
)


def signature(block: str) -> str:
    """Everything before the proof begins."""
    cut = block.find(":=")
    return block if cut < 0 else block[:cut]


def scan() -> list[tuple[str, int, str, tuple[str, ...]]]:
    findings: list[tuple[str, int, str, tuple[str, ...]]] = []
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        starts = [(m.start(), m.group(2)) for m in DECL.finditer(text)]
        for i, (pos, name) in enumerate(starts):
            end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
            sig = signature(text[pos:end])
            hits = tuple(f for f in FLAGGED if f in sig and f != name)
            if hits:
                line = text.count("\n", 0, pos) + 1
                findings.append((str(path), line, name, hits))
    return findings


def main(argv: list[str]) -> int:
    if not SOURCE_ROOT.is_dir():
        print(f"ERROR: {SOURCE_ROOT}/ not found; run from the repository root.")
        return 2

    findings = scan()
    want_list = "--list" in argv
    required = None
    if "--require-unconditional" in argv:
        idx = argv.index("--require-unconditional")
        if idx + 1 >= len(argv):
            print("ERROR: --require-unconditional needs a declaration name.")
            return 2
        required = argv[idx + 1]

    by_name = {name: (path, line, hits) for path, line, name, hits in findings}

    if required is not None:
        if required in by_name:
            path, line, hits = by_name[required]
            print(f"CONDITIONAL: {required} ({path}:{line}) assumes "
                  f"{', '.join(hits)}.")
            print("The classical equivalence is assumed, not proved, so this "
                  "declaration is not a closed RH theorem regardless of its "
                  "axiom printout.")
            return 1
        print(f"{required} carries no flagged open hypothesis.")
        print("Remember this is only half the acceptance test; also run "
              f"`#print axioms {required}`.")
        return 0

    print(f"Declarations conditional on an assumed criterion: {len(findings)}")
    print(f"Flagged hypotheses: {', '.join(FLAGGED)}")
    if want_list:
        print()
        for path, line, name, hits in findings:
            print(f"  {path}:{line}: {name}  [{', '.join(hits)}]")
    else:
        print("Re-run with --list for the full listing.")
    print()
    print("These are reductions, not proofs of their conclusions. A clean")
    print("`#print axioms` on any of them does NOT make it unconditional: the")
    print("criterion is a parameter, not an axiom.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
