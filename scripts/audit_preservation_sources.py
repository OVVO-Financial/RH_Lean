#!/usr/bin/env python3
"""Fail-closed inventory, source-dependency, and axiom audit for this reduction.

The source-only mode never runs Lean. Executable audits run only in GitHub
Actions after the warning-fatal import closure and exact-type acceptance files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from proof_inventory import strip_lean_comments


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts/lean/preservation_sources/inventory.json"
PUBLIC = re.compile(
    r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev)\s+(?P<name>[\w']+)"
)
FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|constant|opaque|native_decide|unsafe|implemented_by|extern)\b"
)


def source_audit(group: str) -> tuple[dict, dict]:
    manifest = json.loads(MANIFEST.read_text())
    spec = manifest["groups"][group]
    found = []
    sources = {}
    for source in spec["sources"]:
        path = ROOT / source["file"]
        raw = path.read_bytes()
        clean = strip_lean_comments(raw.decode())
        if match := FORBIDDEN.search(clean):
            raise ValueError(f"Forbidden proof shortcut {match[0]} in {path}")
        if "set_option autoImplicit false" not in clean:
            raise ValueError(f"Explicit binder policy absent in {path}")
        if re.search(r"set_option\s+warningAsError\s+false", clean):
            raise ValueError(f"Warning-fatal policy weakened in {path}")
        namespaces = re.findall(r"(?m)^namespace\s+(\S+)", clean)
        if namespaces != [source["namespace"]]:
            raise ValueError(f"Unexpected namespace layout in {path}: {namespaces}")
        actual = [(m["kind"], m["name"]) for m in PUBLIC.finditer(clean)]
        expected = [(d["kind"], d["name"]) for d in source["declarations"]]
        if len(actual) != len(set(actual)) or set(actual) != set(expected):
            raise ValueError(f"Public inventory mismatch in {path}: {actual} != {expected}")
        found.extend(f"{source['namespace']}.{name}" for _, name in actual)
        sources[source["file"]] = {
            "sha256": hashlib.sha256(raw).hexdigest(),
            "declarations": source["declarations"],
        }
    if len(found) != len(set(found)):
        raise ValueError("Duplicate full public names")
    for root, dependencies in spec["dependencies"].items():
        if root not in found or not dependencies:
            raise ValueError(f"Invalid source-dependency audit root: {root}")
    acceptance = ROOT / spec["exact_types"]
    raw = acceptance.read_bytes()
    clean = strip_lean_comments(raw.decode())
    if FORBIDDEN.search(clean):
        raise ValueError("Proof shortcut in exact-type acceptance")
    if len(re.findall(r"(?m)^example\b", clean)) < spec["minimum_examples"]:
        raise ValueError("Missing exact-type examples")
    registry = json.loads((ROOT / "docs/proof-obligations.json").read_text())
    nodes = {node["id"]: node for node in registry["nodes"]}
    for target in ("RH", "OPEN-FINITE-AC", "OPEN-AMPLIFICATION-SUBPOWER",
                   "OPEN-NATIVE-OWNER-FRACTIONAL", "OPEN-MU-LIFT"):
        if nodes[target]["logical_status"] != "OPEN":
            raise ValueError(f"Supporting result incorrectly closes {target}")
    evidence = {
        "schema": "rhlean-preservation-source-audit/1",
        "group": group,
        "sources": sources,
        "public_names": sorted(found),
        "exact_types": spec["exact_types"],
        "exact_types_sha256": hashlib.sha256(raw).hexdigest(),
        "source_dependencies": spec["dependencies"],
    }
    return spec, evidence


PREAMBLE = '''import Lean
import Lean.Util.CollectAxioms

open Lean

partial def sourceClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then sourceClosure env rest seen
    else
      let refs := if (`RHLean).isPrefixOf n || (`_private).isPrefixOf n then
        match env.find? n with
        | none => []
        | some info =>
          let valueRefs := match info.value? (allowOpaque := true) with
            | none => []
            | some value => value.getUsedConstants.toList
          info.type.getUsedConstants.toList ++ valueRefs
        else []
      sourceClosure env (refs ++ rest) (seen.insert n)

def main (_args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
'''


def audit_program(spec: dict, evidence: dict) -> str:
    modules = ",\n      ".join(
        '{ module := Name.mkSimple "' + module + '" }' for module in spec["modules"]
    )
    roots = ",\n    ".join("`" + name for name in evidence["public_names"])
    lines = [PREAMBLE,
             f"  let env ← importModules #[{modules}] Options.empty 1024 (loadExts := true)\n",
             "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]\n",
             f"  let roots : Array Name := #[{roots}]\n",
             "  for root in roots do\n",
             "    unless env.contains root do\n",
             '      throw (IO.userError s!"Missing public declaration: {root}")\n',
             "    let axs ← (Lean.collectAxioms root : CoreM (Array Name)).toIO'\n",
             '      { fileName := "<preservation-source-audit>", fileMap := default } { env := env }\n',
             "    for ax in axs do\n",
             "      unless allowed.contains ax do\n",
             '        throw (IO.userError s!"Unapproved axiom for {root}: {ax}")\n',
             "    let reached := sourceClosure env [root]\n"]
    for root, dependencies in spec["dependencies"].items():
        deps = ", ".join("`" + dependency for dependency in dependencies)
        lines += [f"    if root == `{root} then\n",
                  f"      for dependency in #[{deps}] do\n",
                  "        unless reached.contains dependency do\n",
                  '          throw (IO.userError s!"Missing original-source dependency for {root}: {dependency}")\n']
    lines += ['    IO.println s!"PASS preservation-source {root}: {axs}, closure={reached.size}"\n',
              "  return 0\n"]
    return "".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", choices=("owner", "euler"), required=True)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    spec, evidence = source_audit(args.group)
    print(f"PASS {args.group}: exact source inventory, types, and open-target statuses")
    if args.source_only:
        return
    if os.environ.get("GITHUB_ACTIONS") != "true":
        raise SystemExit("Lean execution is restricted to GitHub Actions; use --source-only locally")
    folder = ROOT / f"preservation-{args.group}-evidence"
    folder.mkdir(exist_ok=True)
    program = folder / "Audit.lean"
    program.write_text(audit_program(spec, evidence))
    result = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(program)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    (folder / "audit.log").write_text(result.stdout)
    print(result.stdout, end="")
    result.check_returncode()
    passed = re.findall(r"(?m)^PASS preservation-source ([\w.']+):", result.stdout)
    if sorted(passed) != evidence["public_names"]:
        raise ValueError("Missing, duplicate, or unexpected live axiom evidence")
    if "sorryAx" in result.stdout or "admitAx" in result.stdout:
        raise ValueError("Unapproved terminal axiom")
    evidence["head"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    evidence["verified_public_declarations"] = len(passed)
    (folder / "manifest.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS {args.group}: all {len(passed)} declarations and original-source dependencies")


if __name__ == "__main__":
    main()
