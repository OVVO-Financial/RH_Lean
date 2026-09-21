#!/usr/bin/env python3
"""Report research/ scratch that the compiled library has already absorbed.

`research/**.lean` is staging Lean outside the root import surface and the
authoritative declaration graph.  Selected research modules are kernel-elaborated
by dedicated CI workflows, but they are not promoted into the audited
`RHLean.lean` / `TerminalAxiomAudit` surface: they are not in the root manifest,
not a `lakefile.lean` target, and `scripts/decl_graph.py` never sees them.

So "elaborates" and "is library" are different questions here, and only the
second one this script can answer.  Work leaves the staging tree by being
promoted into `RHLean/`, and the scratch copy is easy to leave behind.  This
script finds those leftovers by comparing the two trees declaration by
declaration.

Two independent signals are reported per research file:

* **name twins** -- a research proof whose short name already names a proof in
  `RHLean/`;
* **signature twins** -- a research proof whose normalized statement signature
  (binders and numerals erased, constants resolved) matches one in `RHLean/`.

Neither is proof of duplication, and the script never says a file *is*
redundant.  A high score on both signals means "read these two files"; the
output prints the paths and line numbers so that is one step.  A file can also
legitimately restate a library theorem while building past it.

Usage:
    python3 scripts/research_overlap.py              # summary
    python3 scripts/research_overlap.py --verbose    # per-proof pairings
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

import rhlean_kg as kg

RESEARCH_ROOTS = (Path("research"), Path("experiments"))
MIN_PROOFS = 3
MIN_SIGNATURE_CONSTANTS = 2


def load_trees() -> tuple[list[kg.Declaration], list[kg.Declaration], kg.NameTable]:
    """Parse both trees and resolve them against one shared name table.

    The shared table matters: it is what lets a research proof's reference to a
    library constant resolve, so the two signature spaces are comparable.
    """

    library: list[kg.Declaration] = []
    for path, text in kg.load_sources():
        library.extend(kg.parse_module(path, text))

    research: list[kg.Declaration] = []
    for root in RESEARCH_ROOTS:
        if not root.is_dir():
            continue
        for path in sorted(root.rglob("*.lean")):
            text = path.read_text(encoding="utf-8", errors="replace")
            research.extend(kg.parse_module(path, text))

    table = kg.NameTable(library + research)
    kg.resolve_references(library + research, table)
    return library, research, table


def analyse() -> dict[str, object]:
    library, research, table = load_trees()

    by_signature: dict[str, list[kg.Declaration]] = defaultdict(list)
    by_short_name: dict[str, list[kg.Declaration]] = defaultdict(list)
    for decl in library:
        if not decl.is_proof:
            continue
        signature, constants = kg.normalized_signature_parts(decl, table)
        if constants >= MIN_SIGNATURE_CONSTANTS:
            by_signature[signature].append(decl)
        by_short_name[decl.short_name].append(decl)

    files: dict[str, dict[str, object]] = {}
    for decl in research:
        if not decl.is_proof:
            continue
        row = files.setdefault(
            decl.path, {"proofs": 0, "name_twins": 0, "signature_twins": 0, "pairs": []}
        )
        row["proofs"] = int(row["proofs"]) + 1

        signature, constants = kg.normalized_signature_parts(decl, table)
        twin = None
        if constants >= MIN_SIGNATURE_CONSTANTS and signature in by_signature:
            row["signature_twins"] = int(row["signature_twins"]) + 1
            twin = by_signature[signature][0]
        if decl.short_name in by_short_name:
            row["name_twins"] = int(row["name_twins"]) + 1
            twin = twin or by_short_name[decl.short_name][0]
        if twin is not None:
            row["pairs"].append(  # type: ignore[union-attr]
                {
                    "research": f"{decl.path}:{decl.line}",
                    "research_name": decl.short_name,
                    "library": f"{twin.path}:{twin.line}",
                    "library_name": twin.short_name,
                }
            )

    for row in files.values():
        n = int(row["proofs"])
        row["overlap"] = (
            max(int(row["name_twins"]), int(row["signature_twins"])) / n if n else 0.0
        )

    return {
        "library_proofs": sum(1 for d in library if d.is_proof),
        "research_proofs": sum(1 for d in research if d.is_proof),
        "research_files": len(files),
        "files": files,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--json", type=Path, help="write the full analysis")
    parser.add_argument(
        "--threshold",
        type=float,
        default=0.5,
        help="report files at or above this overlap fraction (default 0.5)",
    )
    parser.add_argument(
        "--min-proofs",
        type=int,
        default=MIN_PROOFS,
        help=f"ignore files with fewer proofs (default {MIN_PROOFS})",
    )
    parser.add_argument("--verbose", action="store_true", help="list the pairings")
    args = parser.parse_args()

    result = analyse()
    files: dict[str, dict] = result["files"]  # type: ignore[assignment]

    print("Research scratch already present in the compiled library")
    print("========================================================")
    print(f"library named proofs  : {result['library_proofs']:,}")
    print(f"research named proofs : {result['research_proofs']:,}")
    print(f"research files         : {result['research_files']:,}")
    print()
    print("A twin is a research proof whose short name, or whose normalized")
    print("statement signature, already occurs in RHLean/. That is a reason to")
    print("read both files, not a finding that the research copy is redundant:")
    print("a file may legitimately restate a library theorem on its way past it.")
    print()

    ranked = sorted(
        (
            (row["overlap"], path, row)
            for path, row in files.items()
            if int(row["proofs"]) >= args.min_proofs
            and float(row["overlap"]) >= args.threshold
        ),
        key=lambda r: (-float(r[0]), r[1]),
    )
    if not ranked:
        print("no research file meets the threshold")
    else:
        print(f"{'proofs':>6} {'name':>5} {'sig':>5} {'overlap':>8}  file")
        for overlap, path, row in ranked:
            print(
                f"{int(row['proofs']):6d} {int(row['name_twins']):5d} "
                f"{int(row['signature_twins']):5d} {overlap:7.0%}  {path}"
            )
        if args.verbose:
            for _overlap, path, row in ranked:
                print(f"\n{path}")
                for pair in row["pairs"]:
                    print(f"  research {pair['research']}  {pair['research_name']}")
                    print(f"  library  {pair['library']}  {pair['library_name']}")

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(result, indent=1, sort_keys=True) + "\n", encoding="utf-8"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
