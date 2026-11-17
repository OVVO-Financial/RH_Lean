#!/usr/bin/env python3
"""Fail closed on the complete public theorem and live axiom inventory."""

from pathlib import Path
import re

source = Path("research/HISTORICAL_DENSITY_MASK_OBSTRUCTION.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in source
expected = {
    "historicalDensityMask_cost_identity",
    "historicalDensityMask_cost_lower",
    "historicalDensityMask_cost_gt_one",
    "historicalDensityMask_no_contraction",
    "historicalDensityMask_cost_sharp",
}
assert set(re.findall(r"^theorem (\w+)", body, re.M)) == expected
types = Path("scripts/lean/historical_density_mask/ExactTypes.lean").read_text()
assert set(re.findall(r"^#print (\w+)", types, re.M)) == expected
assert len(re.findall(r"^example\b", types, re.M)) == 6
log = Path("historical-density-mask-audit.log").read_text()
passed = re.findall(r"PASS historical-density-mask RHLean.Analysis.(\w+):", log)
assert set(passed) == expected and len(passed) == len(expected), passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: all five public theorems, six exact types and live axiom audits")
