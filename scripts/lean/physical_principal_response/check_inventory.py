"""Keep every public declaration in the new source under the exact-type/axiom checks."""
import re
from pathlib import Path

source = Path("research/oai_434/VF919PhysicalPrincipalResponse.lean").read_text()
expected = {
    "eventually_power_lower",
    "actual_window_all_delay_error",
    "actual_ray_principal_response",
}
actual = set(re.findall(r"^(?:theorem|lemma|def|abbrev)\s+(\w+)", source, re.M))
assert actual == expected, (actual, expected)
audit = Path("scripts/lean/physical_principal_response/Audit.lean").read_text()
types = Path("scripts/lean/physical_principal_response/ExactTypes.lean").read_text()
for name in sorted(expected):
    assert f"PhysicalPrincipalResponse.{name}" in audit, name
    assert f"#check {name}" in types, name
    print(f"PASS inventory {name}")
