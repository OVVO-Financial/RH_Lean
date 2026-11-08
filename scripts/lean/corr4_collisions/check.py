#!/usr/bin/env python3
"""Check the fixed public surface, then its CI-only exact types and axioms."""

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from scripts.audit_euler_fractional_axioms import audit_log

SOURCE = ROOT / "research/CORR4_CUTOFF_COLLISIONS_20261108.lean"
TYPES = ROOT / "scripts/lean/corr4_collisions/ExactTypes.lean"
NAMES = (
    "corr4_cutoff_placement",
    "corr4_collision_cross_eq",
    "corr4_offRay_collision_eq",
    "corr4_collision_cross_trichotomy",
    "corr4_offRay_collision_eq_of_parity",
    "corr4_offRay_sum_eq_image",
    "corr4_offRay_sum_le_twice_image",
    "corr4_offRay_mertens_energy_le_twice_image",
    "corr4_doubled_range_collision_witness",
)
EXPECTED = tuple("RHLean.Proof." + name for name in NAMES)


def static_check():
    source = SOURCE.read_text()
    clean = re.sub(r"/-.*?-/", "", source, flags=re.S)
    clean = re.sub(r"--.*", "", clean)
    names = tuple(re.findall(r"^theorem\s+(\w+)", clean, flags=re.M))
    if names != NAMES:
        raise ValueError(f"Unexpected public theorem surface: {names}")
    if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", clean):
        raise ValueError("Forbidden proof shortcut")
    if re.search(r"^\s*(?:noncomputable\s+)?def\s", clean, flags=re.M):
        raise ValueError("This source must not replace the original definitions")
    assertions = tuple(re.findall(r"#check \(@(\S+) :", TYPES.read_text()))
    audits = tuple(re.findall(r"#print axioms (\S+)", TYPES.read_text()))
    if assertions != EXPECTED or audits != EXPECTED:
        raise ValueError("Exact-type or axiom coverage mismatch")
    print("PASS static inventory: nine theorems, original definitions, nine fixed exact types")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--static", action="store_true")
    args = parser.parse_args()
    static_check()
    if args.static:
        return
    result = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", str(TYPES)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False,
    )
    (ROOT / "corr4-collisions-audit.log").write_text(result.stdout)
    print(result.stdout, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    audit_log(result.stdout, EXPECTED)
    print("PASS exact types and terminal axioms: all nine declarations; standard foundations only")


if __name__ == "__main__":
    main()
