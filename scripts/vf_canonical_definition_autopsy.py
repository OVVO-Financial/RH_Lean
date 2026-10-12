#!/usr/bin/env python3
"""Full repository-source inventory of VF definitions and canonical sqrt2 migration.

Reads EVERY source file under RHLean/ and research/ rather than GitHub search
snippets; its output is an authoritative NAVIGATION map, not a Lean theorem
or a claim that 1:1 identities exist between all visual/fantasy variants.

Canonical real VF(x>=4) = vfMid(x)+sqrt(2).
Canonical integer step = floor(canonical VF(R^2)).
The old raw VF, c0-at-x=9, odd fractional site placement, channels,
floor-Li and fantasy proxies remain separate useful coordinates, never
definitionally equal. Every actual prime is Nat.Prime, unchanged.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
                  r"(def|abbrev|opaque|structure)\s+([A-Za-z0-9_'.]+)\b")
IMPORT = re.compile(r"^import\s+(.+)")
REQUIRED = {
    "vfMidBandMass", "vfMidFinishedMass", "vfMidLiveMass", "vfMid",
    "vfMidLogarithmicIntegralFromTwo", "vfMidPrimeCount",
    "vfMidPrimeError", "vfMidLiError",
    "vfMidAlignedMass", "vfMidAligned", "vfMidInitialAnchor",
    "vfMidAlignedIntegerBlockLevel", "vfMidChosenC0",
    "vfMidSqrtTwoVerticalPhase", "vfMidSqrtTwoIntegerLevel",
    "vfMidOddFractionalPrimeSeatWeight", "vfMidOddCandidateSeats",
    "vfCanonicalPhase", "vfCanonical",
    "vfCanonicalFinishedMass", "vfCanonicalIntegerLevel",
    "vfCanonicalPrimeError", "vfCanonicalLiError",
    "vfCanonicalSquareDefect", "VFCanonicalRealVonKochStatement",
    "VFCanonicalSquareVonKochStatement",
    "VFMidLiAllRealUniformBoundedStatement",
}
SENTINELS = {
    "research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean":
        ["theorem abs_vfMidLiError_le_uniform_allReal",
         "theorem vfMidLiAllRealUniformBounded"],
    "research/VF_CANONICAL_SQRT_TWO.lean":
        ["theorem abs_vfCanonicalLiError_le_uniform_allReal",
         "theorem vfCanonicalFinishedMass_succ",
         "theorem vfCanonicalSquareDefect_succ",
         "theorem vfCanonicalUpperLeftPhase_li_uniform"],
    "research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean":
        ["theorem vfCanonicalRealVonKoch_iff_legacy",
         "theorem vfCanonicalSquareVonKoch_iff_legacy",
         "theorem vfCanonicalSquareVonKoch_iff_primeLiVonKoch"],
    "research/VF_MID_LI_UNIFORM_QUADRATURE.lean":
        ["theorem abs_vfMidLiError_sq_le_uniform",
         "theorem sum_abs_vfMidBandQuadratureError_le_uniform"],
    "research/VF_MID_VON_KOCH_BRIDGE.lean":
        ["theorem vfMidLiError_eq_sq_add_live",
         "theorem abs_vfMidLiveQuadratureError_le",
         "theorem vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded"],
}

def family(name: str, path: str) -> str:
    n = name.lower()
    if n.startswith("vfcanonical"):
        return "CANONICAL sqrt2 public VF interface"
    if n.startswith("vfmid") and any(k in n for k in
           ("bandmass", "finishedmass", "livemass", "squarerootindex", "midpoint")):
        return "invariant raw square-band weight / base geometry"
    if n.startswith("vfmid") and any(k in n for k in
           ("chosen", "sqrttwo", "aligned", "c0", "initialanchor")):
        return "legacy phase / vertical alignment / rounded staircase"
    if "odd" in n and any(k in n for k in ("fractional", "seat", "composite")):
        return "physical odd-seat fractional placement, not real VF"
    if any(k in n for k in ("floorli", "fantasy", "proxy", "cluster")):
        return "counterfactual Li or fantasy proxy, not actual primes"
    if any(k in n for k in ("phasefan", "upperleft", "cornerm", "corner", "channel")):
        return "affine phase / corner / shifted fan"
    if any(k in n for k in ("error", "defect", "backlog", "transport", "owner")):
        return "signed arithmetic error / prime owner / recurrence"
    if "li" in n and "vf" in n:
        return "deterministic Li comparison / quadrature"
    if "vf" in n:
        return "other VF auxiliary/geometry: review source before migration"
    return "unrelated"

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--json",type=Path,default=Path("vf-canonical-definitions.json"))
    p.add_argument("--markdown",type=Path,default=Path("vf-canonical-definitions.md"))
    p.add_argument("--strict",action="store_true")
    args=p.parse_args()
    rows=[]
    files=0
    for folder in ("RHLean","research"):
        for src in sorted((ROOT/folder).rglob("*.lean")):
            files+=1
            rel=src.relative_to(ROOT).as_posix()
            for line_no,line in enumerate(src.read_text(encoding="utf-8").splitlines(),1):
                m=DECL.match(line)
                if not m:continue
                name=m.group(2)
                if not (name.startswith("VF") or name.startswith("vf")): continue
                rows.append({"path":rel,"line":line_no,"kind":m.group(1),
                             "name":name,"family":family(name,rel)})
    names={x["name"] for x in rows}
    missing=sorted(REQUIRED-names)
    absent=[]
    for path,tokens in SENTINELS.items():
        body=(ROOT/path).read_text(encoding="utf-8")
        for token in tokens:
            if token not in body: absent.append(f"{path}:{token}")
    count=Counter(x["family"] for x in rows)
    output={
        "policy":"Canonical public VF = vfMid + sqrt(2), x>=4. Legacy base stays frozen.",
        "normalization":"Li_2(x) = integral_2^x du/log u; standard li differs by li(2).",
        "counts":{"lean_files_scanned":files,"vf_definitions":len(rows),
                  "unique_names":len(names),"families":dict(sorted(count.items()))},
        "missing_required":missing,"missing_sentinels":absent,
        "full_source_occurrences":rows
    }
    args.json.write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8")
    lines=[
      "# Full-source VF definition autopsy",
      "",
      "**Canonical for any new public use: VF(x) = vfMid(x) + sqrt(2), x>=4.**",
      "Older Lean definitions persist as backward-compatible INTERNAL source",
      "coordinates; no old theorem may be reinterpreted as already being",
      "about the sqrt2-shifted VF until an exact phase-transport lemma is used.",
      "",
      f"Scanned {files} Lean source files in RHLean/ and research/,",
      f"found {len(rows)} VF-labelled definitions, {len(names)} distinct names.",
      "Exports were excluded to avoid counting duplicate copies as new proof.",
      "",
      "## Source-coordinate families","","| Family | Definitions |","| --- | ---: |",
    ]
    for k,v in sorted(count.items()):
        lines.append(f"| {k} | {v} |")
    lines.extend(["","## Required named coordinate definitions","","| Name | Exact source | Family |",
                  "| --- | --- | --- |"])
    for name in sorted(REQUIRED):
        candidate=[x for x in rows if x["name"]==name]
        for x in candidate[:3]:
            lines.append(f"| {name} | {x['path']}:{x['line']} | {x['family']} |")
        if not candidate: lines.append(f"| {name} | **MISSING** | unknown |")
    lines.extend(["","## Interpretation and migration contract","",
      "1. vfMid is the raw continuous ORIGINAL midpoint integral proxy.",
      "2. vfCanonical is the UNIQUE public real VF with fixed +sqrt(2).",
      "3. vfCanonicalFinishedMass is the real square endpoint; the integer",
      "   floor is vfCanonicalIntegerLevel, and is a DIFFERENT quantity.",
      "4. vfMidInitialAnchor=4-vfMidFinishedMass(3) is historically distinct",
      "   from sqrt(2). Its old finite anchor results are NOT silently",
      "   transferred to the new canonical phase.",
      "5. Odd fractional seat staircases, floor-Li proxies, corner phases,",
      "   frozen historical owner weights and theta errors are auxiliary",
      "   coordinates, not alternative public VF definitions.",
      "6. The old signed original owner ledger remains mathematically unchanged;",
      "   canonical endpoint defect equals raw original defect MINUS sqrt(2).",
      "7. All-real O(1) follows from prior square-endpoint O(1),",
      "   LIVE-TILE O(1), and the exact square/live decomposition. It",
      "   DOES NOT imply any finite A, finite C, or RH cancellation.",
      "8. Standard li(x) = Li_2(x)+li(2), a fixed independent vertical shift.",
      "9. All new RH endpoints require an actual-prime quantitative premise",
      "   and the classical von-Koch criterion as an explicit Lean argument.",
      "",
      "## Validation","","Missing required names: "+repr(missing),
      "Missing exact source sentinels: "+repr(absent),
      "The full per-definition list is emitted in the JSON artifact.",
      "",
    ])
    args.markdown.write_text("\n".join(lines),encoding="utf-8")
    print(json.dumps(output["counts"],indent=2))
    print(f"Missing required names: {missing}")
    print(f"Missing exact declaration sentinels: {absent}")
    return 1 if args.strict and (missing or absent) else 0

if __name__=="__main__":
    raise SystemExit(main())
