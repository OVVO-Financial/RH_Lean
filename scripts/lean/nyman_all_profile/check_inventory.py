"""Fail closed on exact source, consumer, and live axiom inventories."""

from pathlib import Path
import re

source = Path("research/NYMAN_ALL_PROFILE_COERCIVITY.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in source
expected = {"nyman_dual_profile_leakage", "nyman_all_profile_coercivity",
            "nyman_all_profile_restored_lower"}
assert set(re.findall(r"^theorem (\w+)", body, re.M)) == expected
types = Path("scripts/lean/nyman_all_profile/ExactTypes.lean").read_text()
assert set(re.findall(r"^#print (\w+)", types, re.M)) == expected
assert len(re.findall(r"^example\b", types, re.M)) == 5
log = Path("nyman-all-profile-audit.log").read_text()
passed = re.findall(r"PASS nyman-all-profile RHLean.Analysis.(\w+):", log)
assert set(passed) == expected and len(passed) == len(expected), passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: three public statements, five exact types, live dependencies and axioms")
