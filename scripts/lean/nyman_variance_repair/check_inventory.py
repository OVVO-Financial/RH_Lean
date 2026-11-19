"""Fail closed on exact declarations, type consumers, and live axiom output."""

from pathlib import Path
import re

source = Path("research/NYMAN_VARIANCE_REPAIR.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in body
expected = {"nyman_jordan_two_divisor_sum", "nyman_jordan_two_lower",
            "nyman_covariance_divisor_squares", "nyman_covariance_singleton_lower",
            "nyman_flat_same_support_repair"}
assert set(re.findall(r"^theorem (\w+)", body, re.M)) == expected
types = Path("scripts/lean/nyman_variance_repair/ExactTypes.lean").read_text()
assert set(re.findall(r"^#print (\w+)", types, re.M)) == expected
assert len(re.findall(r"^example\b", types, re.M)) == 6
log = Path("nyman-variance-repair-audit.log").read_text()
passed = re.findall(r"PASS nyman-variance-repair RHLean.Analysis.(\w+):", log)
assert set(passed) == expected and len(passed) == 5, passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: five public statements, six exact types, live dependencies and axioms")
