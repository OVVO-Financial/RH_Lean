#!/usr/bin/env python3
"""Compile and fail-closed audit the eight original Euler source declarations."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "research.EULER_RANK_ONE_FRACTIONAL_ROWS_20261027"
EXPECTED = (
    "RHLean.Proof.eulerFloorBilinearQ_eq_continuous_sub_fractional",
    "RHLean.Proof.eulerContinuousBilinearQ_eq_reciprocal_square",
    "RHLean.Proof.eulerFloorBilinearQ_cast_eq_original",
    "RHLean.Proof.eulerFloorBilinearQ_eq_continuous_sub_diag_sub_twice_off",
    "RHLean.Proof.eulerFractionDiagonalQ_bounds",
    "RHLean.Proof.eulerRankOneFloorKernel_eq_coupled_fracs",
    "RHLean.Proof.eulerRankOneResidualQ_eq_floor_sub_linear",
    "RHLean.Proof.eulerRankOneFloorKernel_divisor_row",
)
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
RECORD = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\[\]]*)\]"
    r"|does not depend on any axioms)[ \t]*$",
    re.MULTILINE,
)
HEADER = re.compile(
    r"^'[^'\n]+' (?:depends on axioms:|does not depend on any axioms)",
    re.MULTILINE,
)


class AuditError(ValueError):
    """A compiler result or an axiom certificate is incomplete or unacceptable."""


def audit_log(text: str, expected: tuple[str, ...] = EXPECTED) -> dict[str, list[str]]:
    if not expected or len(set(expected)) != len(expected):
        raise AuditError("Expected declarations must be nonempty and unique")
    text = re.sub(r"\x1b\[[0-9;]*m", "", text).replace("\r\n", "\n")
    if re.search(r"\b(?:error|warning)(?:\([^\n)]*\))?:", text):
        raise AuditError("Lean emitted an error or warning")
    entries = list(RECORD.finditer(text))
    if len(entries) != len(HEADER.findall(text)):
        raise AuditError("Malformed or incomplete axiom output")
    names = Counter(entry[1] for entry in entries)
    if names != Counter(expected):
        raise AuditError(f"Axiom declaration coverage mismatch: {dict(names)}")
    result = {}
    for entry in entries:
        body = (entry[2] or "").strip()
        values = [value.strip() for value in body.split(",")] if body else []
        if any(not value for value in values) or len(values) != len(set(values)):
            raise AuditError(f"Malformed axiom list for {entry[1]}")
        unexpected = set(values) - ALLOWED
        if unexpected:
            raise AuditError(f"Nonstandard axioms for {entry[1]}: {sorted(unexpected)}")
        result[entry[1]] = sorted(values)
    return result


def audit_source() -> str:
    commands = [f"import \u00ab{MODULE}\u00bb", "set_option autoImplicit false"]
    for name in EXPECTED:
        commands.extend((f"#check {name}", f"#print axioms {name}"))
    return "\n".join(commands) + "\n"


def run_audit(output_dir: Path) -> dict[str, list[str]]:
    output_dir = output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    source = output_dir / "audit.lean"
    source.write_text(audit_source(), encoding="utf-8")
    # Capture both streams without a shell pipeline that can mask Lean's exit code.
    completed = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", str(source)],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", check=False,
    )
    (output_dir / "audit.log").write_text(completed.stdout, encoding="utf-8")
    print(completed.stdout, end="", flush=True)
    if completed.returncode != 0:
        raise AuditError(f"Lean exited with status {completed.returncode}")
    result = audit_log(completed.stdout)
    print(f"PASS: exact coverage of {len(result)} Euler declarations; standard axioms only")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    try:
        run_audit(args.output_dir)
    except (AuditError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
