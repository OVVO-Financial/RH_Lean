#!/usr/bin/env python3
"""Read-only full-source risk census. Hits are review candidates, not verdicts.

Includes all tracked Lean files (native, research, exports, and verification).
The source parser is deliberately not a substitute for elaboration.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import rhlean_kg as kg

METRIC = r"(?:height|covol|volume|mass|rank|norm|degree|gain|period|gram|slope|loss|divisor|metric)"
GEOM = r"(?:geom|polar|period|cusp|lattice|measure|height|norm|mass|rank|degree|gain|slope|divisor|witness|certif)"
RH = re.compile(r"\b(?:RiemannHypothesis(?:Statement)?|riemannHypothesis)\b")
ENDPOINT = re.compile(r"(?:^|\.)(?:RiemannHypothesis|RiemannHypothesisStatement)$")
RISK_LINE = {
    "trust_escape_candidate": re.compile(r"\b(?:sorry|admit|native_decide|native_decide%|ofReduceBool|ofReduceNat|unsafe|implemented_by|axiom|run_tac)\b"),
    "metric_assignment_candidate": re.compile(r"\b[\w.]*" + METRIC + r"[\w.]*\s*:=\s*(?:0\b|1\b|True\b|trivial\b|fun\b|by\s+(?:rfl|trivial)\b|[\w.]*target[\w.]*|[\w.]*formula[\w.]*)", re.I),
    "vacuous_field_candidate": re.compile(r"\b[\w.]*" + GEOM + r"[\w.]*\s*(?::=|:)\s*(?:True\b|False\b|trivial\b|by\s+trivial\b|fun\b[^;\n]*=>\s*True\b)", re.I),
    "degenerate_geometry_candidate": re.compile(r"\b(?:inertia|ell|volume|vol|mass|rank|height|covol|degree|gain|dim|TT|T2|W)\s*:=\s*(?:0\b|⊤|⊥|∅|Fin\s+0\b|Empty\b|PUnit\b|Unit\b|fun\b[^;\n]*=>\s*0\b)"),
    "false_empty_premise_candidate": re.compile(r"[(\{⦃]\s*[\w'!?]+\s*:\s*(?:False|Empty|PEmpty|Fin\s+0)\b"),
    "ambient_hypothesis_candidate": re.compile(r"^\s*(?:include|variable|variables)\b.*(?:RiemannHypothesis|Bound|Certificate|Witness|Geometry|Growth|Gain|Slope|Mass|False|Fin\s+0)\b"),
}
def compact(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()

def scan_text(rel: str, source: str):
    clean, _ = kg.strip_lean_comments(source)
    findings = []
    def add(kind, line, detail):
        findings.append({"category":kind,"path":rel,"line":line,"detail":compact(detail)[:380]})
    for n, line in enumerate(clean.splitlines(), 1):
        for kind, pattern in RISK_LINE.items():
            if pattern.search(line):
                add(kind,n,line)
    declarations = kg.parse_module(Path(rel),source)
    for d in declarations:
        stmt, value = d.statement, d.value.strip()
        concl = compact(kg.statement_conclusion(stmt))
        hyp = compact(kg.statement_hypotheses(stmt))
        if d.kind in kg.PROOF_KINDS:
            if RH.search(stmt):
                if ENDPOINT.search(concl):
                    kind = ("rh_return_with_visible_premises" if re.search(r"[\(\[\{]|→",hyp)
                            else "rh_return_apparently_closed_review")
                else:
                    kind = "rh_statement_reference_review"
                add(kind,d.line,stmt)
            # Simple literal identities only; alpha/definitional equality needs Lean.
            for op in ("↔","=","→"):
                parts = concl.split(op)
                if len(parts)==2 and parts[0].strip()==parts[1].strip():
                    add("literal_reflexive_statement",d.line,stmt)
                    break
            colon = kg._split_top_level(stmt, ":")
            raw_body = compact(stmt[colon+1:]) if colon >= 0 else ""
            if re.fullmatch(r"[\w.'!?]+",raw_body) and re.search(
                r":\s*"+re.escape(raw_body)+r"\s*[\)\}\]]",hyp):
                add("literal_self_premise",d.line,stmt)
            if re.search(GEOM,d.name,re.I) and re.fullmatch(r"(?:by\s+)?(?:rfl|trivial|Iff\.rfl)",value):
                add("geometric_reflexive_proof_review",d.line,stmt)
        if d.kind in ("def","abbrev","opaque"):
            if d.name == "RiemannHypothesis":
                add("root_rh_shadow_candidate",d.line,stmt)
            if re.fullmatch(r"(?:fun\b.*?(?:=>|↦)\s*)?(?:True|False)",compact(value)):
                add("constant_truth_definition_review",d.line,stmt+" := "+value)
            if RH.search(stmt+" "+value):
                add("rh_definition_alias_review",d.line,stmt+" := "+value)
        if d.kind in ("structure","class") and re.search(
            GEOM+r"|bound|setting|data|hyp|bridge|condition",d.name,re.I):
            # Field-bearing structures may contain an actual required theorem.
            for offset,line in enumerate(stmt.splitlines()):
                if re.match(r"\s{2,}[\w.]+\s*:",line) and re.search(
                    GEOM+r"|RiemannHypothesis|bound|top|excluded|recover|cost|analytic|error|proof|valid",line,re.I):
                    add("certificate_field_review",d.line+offset,line)
    return len(declarations), findings

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--root",type=Path,default=Path("."))
    p.add_argument("--json",type=Path,required=True)
    p.add_argument("--label",default="checkout")
    args=p.parse_args()
    root=args.root.resolve()
    def git(*xs):
        return subprocess.check_output(["git","-C",str(root),*xs])
    ref=git("rev-parse","HEAD").decode().strip()
    paths=[x.decode() for x in git("ls-files","-z","--","*.lean").split(b"\0") if x]
    hits=[]; counts=Counter(); hashes=set(); failures=[]; scopes=Counter()
    declarations=0; lines=0
    for rel in sorted(paths):
        try:
            raw=(root/rel).read_bytes()
            source=raw.decode("utf-8")
            hashes.add(hashlib.sha256(raw).hexdigest())
            n, found=scan_text(rel,source)
            declarations+=n; lines+=len(source.splitlines())
            hits.extend(found)
            counts.update(x["category"] for x in found)
            scopes[rel.split("/")[0]]+=1
        except Exception as exc:
            failures.append({"path":rel,"error":str(exc)})
    report={"label":args.label,"commit":ref,"tracked_lean_files":len(paths),
            "scanned_lean_files":len(paths)-len(failures),"unique_source_bytes":len(hashes),
            "source_lines":lines,"parsed_declarations":declarations,
            "scope_file_counts":dict(scopes),"candidate_counts":dict(counts),
            "scan_failures":failures,"findings":hits,
            "status":"candidate census only; not semantic clearance"}
    args.json.parent.mkdir(parents=True,exist_ok=True)
    args.json.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print("SEMANTIC_CENSUS "+json.dumps({k:v for k,v in report.items() if k!="findings"},ensure_ascii=False),flush=True)
    bycat=defaultdict(list)
    for h in hits:
        bycat[h["category"]].append(h)
    for cat, findings in sorted(bycat.items()):
        if cat=="certificate_field_review":
            limit=5
        else:
            limit=10
        # Native source first; then research; exports often duplicate old sources.
        ordered=sorted(findings,key=lambda h:(not h["path"].startswith("RHLean/"),h["path"],h["line"]))
        seen=set()
        for h in ordered:
            if h["path"] in seen:
                continue
            seen.add(h["path"])
            print("CANDIDATE "+json.dumps(h,ensure_ascii=False),flush=True)
            if len(seen)>=limit:
                break
    if failures:
        raise SystemExit("Incomplete source census")
    if not paths:
        raise SystemExit("No tracked Lean files")
    # A new root shadow must never be silently accepted.
    if counts["root_rh_shadow_candidate"]:
        raise SystemExit("Root RH shadow candidate requires manual review")
if __name__=="__main__":
    main()
