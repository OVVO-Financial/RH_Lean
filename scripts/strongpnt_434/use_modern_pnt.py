#!/usr/bin/env python3
"""Use the modern, pinned PNT+ theorem sources in the isolated Lean 4.34 runner.

RHLean's direct old StrongPNT consumers need only:
  * zero-free region 1/log |t|: PrimeNumberTheoremAnd.StrongPNT.ZetaZeroFree1;
  * finite-height zero-free box: PrimeNumberTheoremAnd.ZetaBounds.ZetaNoZerosInBox;
  * a smoothing integrability lemma: PrimeNumberTheoremAnd.MediumPNT.

The two zero-free statements have the same logical parameters as the historical
imports, and the strong PNT theorem is already proven in the modern PNT+ module.
The original corridor uses natural powers where the modern PNT+ interfaces
carry equivalent real powers. Real.rpow_natCast performs this exact conversion.
Each substitution is source-exact and scoped to the disposable CI checkout;
do NOT change statements or introduce axioms.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]
LOCK = ROOT / "lake-manifest.json"
PATCHES = [
  [
    "StrongMertensZetaKernel",
    "import StrongPNT.PNT5_Strong\n",
    "import PrimeNumberTheoremAnd.StrongPNT\n"
  ],
  [
    "StrongMertensSmoothingFinite",
    "import StrongPNT.PNT5_Strong\n",
    "import PrimeNumberTheoremAnd.StrongPNT\n"
  ],
  [
    "StrongMertensLogNineContour",
    "import StrongPNT.PNT5_Strong\n",
    "import PrimeNumberTheoremAnd.StrongPNT\n"
  ],
  [
    "StrongMertensLogNineBoundsCore",
    "import StrongPNT.PNT5_Strong\n",
    "import PrimeNumberTheoremAnd.StrongPNT\n"
  ],
  [
    "StrongMertensLogNineCorridor",
    "import StrongPNT.PNT4_ZeroFreeRegion\nimport StrongPNT.ZetaZeroFree\n",
    "import PrimeNumberTheoremAnd.StrongPNT\n"
  ],
  [
    "StrongMertensLogNineCorridor",
    "ZetaZeroFree_p\n",
    "ZetaZeroFree1\n"
  ],
  [
    "StrongMertensLogNineCorridor",
    "ZetaNoZerosInBox' 3",
    "ZetaNoZerosInBox 3"
  ],
  [
    "StrongMertensLogNineCorridor",
    "exact hZF s.re s.im hlarge hmem",
    "have hpow1 : Real.log |s.im| ^ (1 : ℝ) = Real.log |s.im| ^ (1 : ℕ) :=
          Real.rpow_natCast _ 1
        exact hZF s.re s.im hlarge (by simpa only [hpow1] using hmem)"
  ],
  [
    "StrongMertensLogNineCorridor",
    "exact hInv sigma t ht ⟨hlower, hupper⟩",
    "have hpow9 : Real.log |t| ^ (9 : ℝ) = Real.log |t| ^ (9 : ℕ) :=
      Real.rpow_natCast _ 9
    exact hInv sigma t ht ⟨(by simpa only [hpow9] using hlower),
      (by simpa only [hpow9] using hupper)⟩"
  ],
  [
    "StrongMertensLogNineCorridor",
    "exact hInv (strongMertensLogNineShift A T) t ht ⟨hlower, hupper⟩",
    "have hpow9 : Real.log |t| ^ (9 : ℝ) = Real.log |t| ^ (9 : ℕ) :=
      Real.rpow_natCast _ 9
    exact hInv (strongMertensLogNineShift A T) t ht
      ⟨(by simpa only [hpow9] using hlower),
       (by simpa only [hpow9] using hupper)⟩"
  ]
]
def main():
    packages = {x["name"]:x["rev"] for x in json.loads(LOCK.read_text())["packages"]}
    assert packages["mathlib"] == "d13f23b723b8a846827a245b89c10fc7d3f11612"
    assert packages["PrimeNumberTheoremAnd"] == "c39a751132c88b6e8080b74c74023fd95b3d8be0"
    if "StrongPNT" in packages:
        raise RuntimeError("Legacy StrongPNT package still in candidate lock")
    changes={}
    for name, old, new in PATCHES:
        path=ROOT / "RHLean" / "Analysis" / (name + ".lean")
        content=changes.setdefault(str(path),path.read_text(encoding="utf-8"))
        if content.count(old)==1 and content.count(new)==0:
            changes[str(path)]=content.replace(old,new,1)
        elif content.count(old)==0 and content.count(new)==1:
            continue
        else:
            raise RuntimeError(f"Unexpected text for {name}: {old!r}")
    for name,content in changes.items():
        Path(name).write_text(content,encoding="utf-8")
        print("Modern PNT+ source substitution:", Path(name).relative_to(ROOT))
    print("No theorem statement or assumption altered.")

if __name__ == "__main__":
    main()
