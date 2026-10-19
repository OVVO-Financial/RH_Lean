#!/usr/bin/env python3
"""Source-exact first stage of the StrongPNT port to Lean/Mathlib 4.34.1.

Only update module import paths whose new target files are verified in the
pinned Mathlib tree. This does NOT port any theorem proof, add axioms or change
any lemma signature. In particular, do not use scripts/strongpnt_424 here.

The historical external source revision must remain the RHLean-pinned commit.
Unexpected source differences are fatal, never silently ignored.
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / ".lake/packages/StrongPNT/StrongPNT"
MATHLIB = ROOT / ".lake/packages/mathlib"
MANIFEST = ROOT / "lake-manifest.json"

EXPECTED_SOURCE = "2f5835c322314f55f1026ec2f139d704b7c45c69"

PATCHES = (
    (
        "PNT5_Strong.lean",
        "import Mathlib.Data.Real.Pi.Bounds\n",
        "import Mathlib.Analysis.Real.Pi.Bounds\n",
        "Mathlib/Analysis/Real/Pi/Bounds.lean",
    ),
    (
        "PNT5_Strong.lean",
        "import Mathlib.Data.Complex.ExponentialBounds\n",
        "import Mathlib.Analysis.Complex.ExponentialBounds\n",
        "Mathlib/Analysis/Complex/ExponentialBounds.lean",
    ),
    (
        "ZetaZeroFree.lean",
        "import Mathlib.Tactic.FunProp.Differentiable\n",
        "import Mathlib.Tactic.FunProp\n",
        "Mathlib/Tactic/FunProp.lean",
    ),
)


def main() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    pins = {p["name"]: p["rev"] for p in manifest["packages"]}
    if pins.get("StrongPNT") != EXPECTED_SOURCE:
        raise RuntimeError("StrongPNT is not pinned to the audited historical source")
    if pins.get("mathlib") != "d13f23b723b8a846827a245b89c10fc7d3f11612":
        raise RuntimeError("Mathlib v4.34.1 exact revision is required")

    # Check ALL input patches and replacement paths before modifying anything.
    content = {}
    for name, old, new, module in PATCHES:
        path = PKG / name
        if not (MATHLIB / module).is_file():
            raise RuntimeError(f"Replacement Mathlib module not found: {module}")
        source = content.setdefault(name, path.read_text(encoding="utf-8"))
        if source.count(old) == 1 and source.count(new) == 0:
            content[name] = source.replace(old, new, 1)
        elif source.count(old) == 0 and source.count(new) == 1:
            print(f"already applied: {name}: {new.strip()}")
        else:
            raise RuntimeError(
                f"Unexpected source match in {name}: "
                f"old={source.count(old)}, new={source.count(new)}"
            )

    for name, source in content.items():
        (PKG / name).write_text(source, encoding="utf-8")
        print(f"source-exact 4.34 import path pass: {name}")

    print("Only module paths changed; no theorem or axiom has been ported.")


if __name__ == "__main__":
    main()
