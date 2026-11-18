"""Fail closed on source, exact-type and live standard-axiom inventories."""

from pathlib import Path
import re

source = Path("research/NYMAN_THREE_PROFILE_COERCIVITY.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in source
expected = {"nyman_two_band_profile_source", "nyman_three_profile_coercivity",
            "nyman_three_profile_restored_lower"}
assert set(re.findall(r"^theorem (\w+)", body, re.M)) == expected
types = Path("scripts/lean/nyman_three_profile/ExactTypes.lean").read_text()
assert set(re.findall(r"^#print (\w+)", types, re.M)) == expected
assert len(re.findall(r"^example\b", types, re.M)) == 4
log = Path("nyman-three-profile-audit.log").read_text()
passed = re.findall(r"PASS nyman-three-profile RHLean.Analysis.(\w+):", log)
assert set(passed) == expected and len(passed) == len(expected), passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: three public statements, four exact types and all live axiom audits")
