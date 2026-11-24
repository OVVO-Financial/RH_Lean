#!/usr/bin/env python3
"""Report historical criterion-bearing declarations, or require exact kernel type evidence.

The source scan is a navigation aid ONLY. The old --require-unconditional
mode wrongly succeeded for nonexistent or unrelated declarations and could
miss every open premise other than ClassicalMertensRHCriterion.

Usage:
    python3 scripts/check_rh_conditionality.py --list
    python3 scripts/check_rh_conditionality.py --require-unconditional FULL_NAME --kernel-jsonl lean-decl-graph.jsonl

The latter checks the literal closed root RH type in a fresh elaborated dump.
It is necessary but not sufficient: independently verify the exact commit,
proof term, transitive axiom audit, and mathematical supplier semantics.
No missing kernel evidence can produce success.
"""

from __future__ import annotations

import json
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


def exact_terminal_type(required: str, dump: Path) -> tuple[bool, str]:
    try:
        records = [json.loads(line) for line in dump.read_text(encoding="utf-8").splitlines() if line]
    except (OSError, ValueError) as exc:
        return False, f"Cannot read kernel evidence: {exc}"
    if not records or any("kernelTypeAudit" not in r for r in records):
        return False, "Missing fresh kernel type audit metadata"
    matches = [r for r in records if r.get("name") == required]
    if len(matches) != 1:
        return False, "Exact fully qualified declaration not found uniquely in kernel dump"
    r = matches[0]
    a = r["kernelTypeAudit"]
    if (r.get("kind") != "theorem" or a.get("binders") != 0
        or a.get("form") != "named" or a.get("targets") != ["RiemannHypothesis"]
        or a.get("premises") != [] or a.get("blocked") is not False
        or a.get("returnsRH") is not True or a.get("exactRH") is not True):
        return False, "Declaration is not an exact closed theorem of root RiemannHypothesis"
    return True, "Exact closed root RH type only; verify provenance, axioms and independent supplier semantics"


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

    if required is not None:
        if "--kernel-jsonl" not in argv:
            print("ERROR: --require-unconditional requires a fresh --kernel-jsonl dump; a source scan cannot certify an endpoint.")
            return 2
        idx = argv.index("--kernel-jsonl")
        if idx + 1 >= len(argv):
            print("ERROR: --kernel-jsonl needs a path.")
            return 2
        ok, message = exact_terminal_type(required, Path(argv[idx+1]))
        print(message)
        return 0 if ok else 1

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
