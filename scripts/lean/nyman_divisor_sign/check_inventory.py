#!/usr/bin/env python3
"""Fail closed on exact public declarations and actual live axiom evidence."""

from pathlib import Path
import re

source = Path("research/NYMAN_DIVISOR_JUMP_SIGN_OBSTRUCTION.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in source
expected = {
    "nymanHighDivisorJump_210_profile",
    "nymanHighDivisorJump_210_opposite_signs",
    "nyman_210_long_middle_witness",
    "not_nyman_long_middle_parity_nonnegative",
    "nymanLogTail_210_opposite_steps",
    "nyman_flat_210_step_profile",
    "nyman_flat_210_opposite_steps",
}
assert set(re.findall(r"^theorem (\w+)", body, re.M)) == expected
types = Path("scripts/lean/nyman_divisor_sign/ExactTypes.lean").read_text()
assert set(re.findall(r"^#print (\w+)", types, re.M)) == expected
log = Path("nyman-divisor-sign-audit.log").read_text()
passed = re.findall(r"PASS nyman-divisor-sign RHLean.Analysis.(\w+):", log)
assert set(passed) == expected and len(passed) == len(expected), passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: exact seven-theorem public inventory and all live axiom audits")
