#!/usr/bin/env python3
"""Check that RHLean.lean imports exactly the modules present on disk.

This is the cheap half of what `lake exe mk_all` does.  mk_all regenerates the
root manifest and CI then asks whether the regenerated file differs from the
committed one; that answer is worth about twenty seconds of every hosted build,
because reaching it means installing Lean, restoring Mathlib and building the
mk_all executable before the check can run at all.

The property that actually matters -- a module exists under RHLean/ but is
absent from the root manifest, so it is never compiled and its `sorry`s never
surface -- is a comparison between a directory listing and a list of import
lines.  Running it here lets the audit job reject that in about a second, in
parallel with the build, instead of ninety seconds into it.

`lake exe mk_all` remains the generator: scripts/local_ci.sh still runs it, and
it is what a developer uses to repair a stale manifest.  This script only
checks the result, so it deliberately mirrors mk_all's output shape for this
project -- one `import <module>` line per source file, sorted, and nothing
else.  If that shape ever changes, this check is what needs updating.
"""

from __future__ import annotations

import sys
from pathlib import Path

LIB = "RHLean"
MANIFEST = Path(f"{LIB}.lean")
SOURCE_ROOT = Path(LIB)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def main() -> int:
    if not SOURCE_ROOT.is_dir():
        print(f"ERROR: {SOURCE_ROOT}/ not found; run from the repository root.")
        return 2
    if not MANIFEST.is_file():
        print(f"ERROR: {MANIFEST} not found; run from the repository root.")
        return 2

    expected = sorted(module_name(p) for p in SOURCE_ROOT.rglob("*.lean"))

    found: list[str] = []
    for lineno, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if not line.startswith("import "):
            print(f"ERROR: {MANIFEST}:{lineno}: expected only import lines, found: {line}")
            return 1
        found.append(line[len("import "):].strip())

    missing = [m for m in expected if m not in set(found)]
    extra = [m for m in found if m not in set(expected)]

    if missing:
        print(f"ERROR: {len(missing)} module(s) exist under {SOURCE_ROOT}/ but are not imported")
        print(f"       by {MANIFEST}, so they are never compiled:")
        for m in missing:
            print(f"         {m}")
    if extra:
        print(f"ERROR: {len(extra)} import(s) in {MANIFEST} have no source file:")
        for m in extra:
            print(f"         {m}")
    if not missing and not extra and found != sorted(found):
        print(f"ERROR: {MANIFEST} lists every module but is not sorted.")
        missing = ["<unsorted>"]  # force a non-zero exit below

    if missing or extra:
        print()
        print("Repair it with:  lake exe mk_all")
        return 1

    print(f"{MANIFEST} imports all {len(expected)} modules under {SOURCE_ROOT}/, sorted.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
