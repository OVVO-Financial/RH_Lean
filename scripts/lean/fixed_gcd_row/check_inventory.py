#!/usr/bin/env python3
"""Fail closed on source, theorem inventory, and actual axiom evidence."""

from pathlib import Path
import re

source = Path("research/EULER_FIXED_GCD_ROW_OBSTRUCTION.lean").read_text()
body = re.sub(r"/-.*?-/", "", source, flags=re.S)
body = re.sub(r"--.*", "", body)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", body)
assert "set_option autoImplicit false" in source
expected = {
    "eulerFixedGcdRowInt_cast", "eulerBilinearInt_cast",
    "eulerFixedGcdRowInt_139_six", "eulerBilinearInt_139",
    "mertensSummatory_19320", "eulerFixedGcdRow_six_witness",
    "not_pointwise_mertens_le_fixedGcdRow_six",
    "not_pointwise_centered_mertens_le_fixedGcdRow_six",
}
actual = set(re.findall(r"^theorem (\w+)", body, re.M))
assert actual == expected, (actual, expected)
log = Path("fixed-gcd-row-audit.log").read_text()
passed = re.findall(r"PASS fixed-gcd-row RHLean.Proof.(\w+):", log)
assert set(passed) == expected and len(passed) == len(expected), passed
assert "sorryAx" not in log and "admitAx" not in log
print("PASS: exact public theorem inventory and all eight axiom audits")
