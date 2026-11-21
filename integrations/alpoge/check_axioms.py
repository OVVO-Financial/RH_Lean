#!/usr/bin/env python3
"""Fail-closed parser for joint Alpoge/RHLean kernel axiom disclosures.

Unlike a grep that only checks 'sorry', this requires seeing and parsing
each new terminal theorem and rejects every axiom outside the three
standard Lean logical axioms. This does not itself replay the proof:
the prior lake env lean compilation does that, using Alpoge's exact pin.
"""
import re
import sys
from pathlib import Path

EXPECTED = (
    "RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_RH",
    "RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_DirichletHalf",
    "RHLean.AlpogeInterface.originalAlpoge_RH_and_nativeGz",
)
ALLOWED = {"propext", "Quot.sound", "Classical.choice", "choice"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_axioms.py AlpogeAxiomAudit.log")
text = Path(sys.argv[1]).read_text(encoding="utf-8")
for name in EXPECTED:
    escaped = re.escape(name)
    block = re.search(
        rf"'{escaped}' depends on axioms:\s*\[([^\]]*)\]",
        text,
    )
    if block:
        axioms = {a.strip() for a in block.group(1).split(",") if a.strip()}
        extra = axioms - ALLOWED
        if extra:
            raise SystemExit(f"FAIL: {name} uses nonstandard axioms: {sorted(extra)}")
        print(f"PASS: {name} uses only {sorted(axioms)}")
        continue
    if re.search(
        rf"'{escaped}' does not depend on any axioms",
        text,
    ):
        print(f"PASS: {name} uses no axioms")
        continue
    raise SystemExit(f"FAIL: no parseable kernel axiom report for {name}")
print("PASS: original RH+GRH proof and shared Gz certificate have no nonstandard axioms")
