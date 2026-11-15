#!/usr/bin/env python3
"""Inventory and fail-closed terminal-axiom audit for the universal envelope.

--source-only never invokes Lean. Executable audits require GitHub Actions,
where the workflow first builds the exact warning-fatal import closure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from audit_euler_fractional_axioms import AuditError, audit_log
from compile_research_import_closure import Closure
from proof_inventory import strip_lean_comments
from repo_index import imports_from


ROOT = Path(__file__).resolve().parents[1]
UNIVERSAL = "RHLean.Analysis.UniversalEnvelope"
OWNER = "RHLean.Analysis.OwnerPrefix"
SOURCES = {
    "ARITHMETIC": (UNIVERSAL, (
        "centered_le_succ_power", "historical_le_of_power",
        "powerBound_of_square_endpoint_power", "growthAtMost_of_envelopeBound",
        "rightmost_le_of_envelopeBound", "envelopeBound_of_mertens_half",
        "envelopeBound_zero_iff_mertens_half",
    )),
    "KERNEL": (UNIVERSAL, (
        "moebius_product_kernel_inversion", "divisorKernel_inversion",
        "potential_norm_le_reciprocal_history", "potential_norm_le_historical_sqrt",
    )),
    "OWNER_EQUIVALENCE": (OWNER, (
        "native_owner_zero_of_mertens_half", "mertens_half_of_native_owner_zero",
        "native_owner_zero_iff_mertens_half", "native_owner_zero_iff_criticalZeros",
    )),
    "ZERO_LOG": (UNIVERSAL, (
        "envelopeBound_one_zero_of_zeroLog", "zeroLog_of_mertens_half",
        "mertens_half_of_zeroLog", "zeroLog_iff_mertens_half",
        "zeroLog_iff_criticalZeros",
    )),
    "OWNER_FRACTIONAL": (OWNER, (
        "native_uniform_fractional_owner_one_of_mertens_half",
        "native_uniform_fractional_owner_iff_mertens_half",
        "native_uniform_fractional_owner_iff_criticalZeros",
        "native_owner_zero_iff_uniform_fractional_owner",
    )),
}
GROUPS = {
    "core": ("ARITHMETIC", "KERNEL", "OWNER_EQUIVALENCE", "ZERO_LOG"),
    "fractional": ("OWNER_EQUIVALENCE", "OWNER_FRACTIONAL"),
}
ACCEPTANCE = {
    "core": "research/UNIVERSAL_ENVELOPE_ACCEPTANCE.lean",
    "fractional": "research/UNIVERSAL_ENVELOPE_FRACTIONAL_ACCEPTANCE.lean",
}
PUBLIC = re.compile(
    r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev)\s+(?P<name>[\w']+)"
)
FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|constant|opaque|native_decide|unsafe|implemented_by|extern)\b"
)


def checked_source(path: Path) -> tuple[bytes, str]:
    raw = path.read_bytes()
    clean = strip_lean_comments(raw.decode("utf-8"))
    if match := FORBIDDEN.search(clean):
        raise AuditError(f"Forbidden proof shortcut {match[0]} in {path.relative_to(ROOT)}")
    return raw, clean


def source_audit(group: str, plan_ancestors: bool = True) -> tuple[dict, tuple[str, ...]]:
    sources = {}
    expected = []
    for short in GROUPS[group]:
        relative = f"research/UNIVERSAL_ENVELOPE_{short}.lean"
        namespace, required = SOURCES[short]
        raw, clean = checked_source(ROOT / relative)
        namespaces = re.findall(r"(?m)^namespace\s+(\S+)", clean)
        if namespaces != [namespace]:
            raise AuditError(f"Unexpected namespace layout in {relative}: {namespaces}")
        declarations = [(m["kind"], m["name"]) for m in PUBLIC.finditer(clean)]
        names = [name for _, name in declarations]
        if not declarations or len(set(names)) != len(names):
            raise AuditError(f"Missing or duplicate public declarations in {relative}")
        missing = set(required) - set(names)
        if missing:
            raise AuditError(f"Missing required declarations in {relative}: {sorted(missing)}")
        expected.extend(f"{namespace}.{name}" for _, name in declarations)
        sources[relative] = {
            "sha256": hashlib.sha256(raw).hexdigest(),
            "namespace": namespace,
            "public_declarations": [{"kind": kind, "name": name} for kind, name in declarations],
        }

    acceptance = ACCEPTANCE[group]
    raw, clean = checked_source(ROOT / acceptance)
    count = len(re.findall(r"(?m)^example\b", clean))
    if count < (10 if group == "core" else 4):
        raise AuditError(f"Missing exact-type acceptance examples in {acceptance}")
    # The established OAI pipeline materializes pinned anchored ancestors.
    # Static review of our new leaves can precede that generation; executable
    # verification always requires the complete materialized import plan.
    plan = Closure().plan([ROOT / acceptance]) if plan_ancestors else None
    if group == "core":
        assert plan is not None
        for entry in plan["modules"]:
            source = ROOT / entry["source"]
            if "/oai_434/" in entry["source"] or any(
                module.startswith("OAI.") for module in imports_from(source.read_text())
            ):
                raise AuditError(f"OAI source leaked into the independent core: {entry['source']}")
    inventory = {
        "schema": "rhlean-universal-envelope-audit/1",
        "group": group,
        "sources": sources,
        "acceptance": acceptance,
        "acceptance_sha256": hashlib.sha256(raw).hexdigest(),
        "exact_type_examples": count,
        "research_import_closure": plan,
        "ancestor_generation_pending": not plan_ancestors,
        "allowed_terminal_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "status": "SOURCE_INVENTORY_ONLY",
    }
    return inventory, tuple(expected)


def run_audit(group: str, output_dir: Path, source_only: bool, direct_lean: bool) -> None:
    inventory, expected = source_audit(group, plan_ancestors=(group == "core" or not source_only))
    if not source_only and os.environ.get("GITHUB_ACTIONS") != "true":
        raise AuditError("Lean execution is restricted to GitHub Actions; use --source-only locally")
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "inventory.json"
    json_path.write_text(json.dumps(inventory, indent=2) + "\n")
    if source_only:
        print(f"PASS: {group}: {len(expected)} public declarations inventoried; exact acceptance present; no Lean invoked")
        return

    module = ACCEPTANCE[group].removesuffix(".lean").replace("/", ".")
    commands = [f"import «{module}»", "set_option autoImplicit false"]
    for name in expected:
        commands.extend((f"#check {name}", f"#print axioms {name}"))
    source = output_dir / "Audit.lean"
    source.write_text("\n".join(commands) + "\n")
    log_path = output_dir / "audit.log"
    log_path.write_text("")
    executable = ["lean"] if direct_lean else ["lake", "env", "lean"]
    # Recheck every new leaf and its exact-type acceptance at this source head;
    # cached ancestors remain the responsibility of research-compile.
    for relative in (*inventory["sources"], ACCEPTANCE[group], str(source)):
        completed = subprocess.run(
            [*executable, "-DwarningAsError=true", relative], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
        )
        with log_path.open("a") as stream:
            stream.write(completed.stdout)
        print(completed.stdout, end="", flush=True)
        if completed.returncode:
            raise AuditError(f"Warning-fatal Lean check failed for {relative}: exit {completed.returncode}")
    inventory["axioms"] = audit_log(log_path.read_text(), expected)
    after, after_expected = source_audit(group)
    if after["sources"] != inventory["sources"] or after["acceptance_sha256"] != inventory["acceptance_sha256"] or after_expected != expected:
        raise AuditError("Audited source changed during verification")
    inventory["commit"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    inventory["status"] = "WARNING_FATAL_TYPES_AND_STANDARD_AXIOMS_VERIFIED"
    json_path.write_text(json.dumps(inventory, indent=2) + "\n")
    print(f"PASS: {group}: all {len(expected)} public declarations; exact types; standard terminal axioms only")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=GROUPS, default="core")
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--direct-lean", action="store_true", help="use the workflow's combined RH/OAI LEAN_PATH")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    destination = (args.output_dir or ROOT / f"universal-envelope-{args.group}-evidence").resolve()
    try:
        run_audit(args.group, destination, args.source_only, args.direct_lean)
    except (AuditError, OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
