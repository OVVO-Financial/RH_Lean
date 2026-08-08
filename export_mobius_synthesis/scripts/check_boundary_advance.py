#!/usr/bin/env python3
"""Fail-closed PR gate for the Möbius synthesis analytic frontier.

The checker is intended to be executed from a trusted base-branch copy by the
GitHub Actions workflow. It compares the base and candidate frontier manifests,
requires strict quantitative progress for Lean-source changes, and emits a small
Lean file that type-checks the claimed witness against the canonical boundary
predicate.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

FRONTIER_PATH = "boundary/frontier.json"
CONTRACT_PATH = "RHLean/Analysis/MobiusSynthesisBoundary.lean"
LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
ALLOWED_KINDS = {"exact_reduction", "power_bound", "rh_scale"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class GateError(RuntimeError):
    pass


def run_git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise GateError(
            f"git {' '.join(args)} failed with exit code {proc.returncode}:\n{proc.stderr.strip()}"
        )
    return proc.stdout


def load_json_text(text: str, source: str) -> dict[str, Any]:
    try:
        value = json.loads(text)
    except json.JSONDecodeError as exc:
        raise GateError(f"invalid JSON in {source}: {exc}") from exc
    if not isinstance(value, dict):
        raise GateError(f"{source} must contain a JSON object")
    return value


def load_base_manifest(repo: Path, base_sha: str) -> dict[str, Any]:
    text = run_git(repo, "show", f"{base_sha}:{FRONTIER_PATH}")
    return load_json_text(text, f"{base_sha}:{FRONTIER_PATH}")


def load_head_manifest(repo: Path) -> dict[str, Any]:
    path = repo / FRONTIER_PATH
    if not path.is_file():
        raise GateError(f"candidate is missing required {FRONTIER_PATH}")
    return load_json_text(path.read_text(encoding="utf-8"), FRONTIER_PATH)


def changed_files(repo: Path, base_sha: str, head_sha: str) -> set[str]:
    text = run_git(repo, "diff", "--name-only", f"{base_sha}...{head_sha}")
    return {line.strip() for line in text.splitlines() if line.strip()}


def manifest_kind(manifest: dict[str, Any], which: str) -> str:
    certified = manifest.get("certified")
    if not isinstance(certified, dict):
        raise GateError(f"{which} manifest is missing object field 'certified'")
    kind = certified.get("kind")
    if kind not in ALLOWED_KINDS:
        raise GateError(
            f"{which} certified.kind must be one of {sorted(ALLOWED_KINDS)}, got {kind!r}"
        )
    return kind


def exponent_fraction(manifest: dict[str, Any], which: str) -> Fraction:
    certified = manifest["certified"]
    exponent = certified.get("exponent")
    if not isinstance(exponent, dict):
        raise GateError(f"{which} power_bound requires certified.exponent")
    numerator = exponent.get("numerator")
    denominator = exponent.get("denominator")
    if not isinstance(numerator, int) or isinstance(numerator, bool):
        raise GateError(f"{which} exponent numerator must be an integer")
    if not isinstance(denominator, int) or isinstance(denominator, bool) or denominator <= 0:
        raise GateError(f"{which} exponent denominator must be a positive integer")
    return Fraction(numerator, denominator)


def witness(manifest: dict[str, Any], which: str) -> tuple[str, str]:
    certified = manifest["certified"]
    witness_obj = certified.get("witness")
    if not isinstance(witness_obj, dict):
        raise GateError(f"{which} frontier requires certified.witness")
    module = witness_obj.get("module")
    theorem = witness_obj.get("theorem")
    if not isinstance(module, str) or not LEAN_IDENT_RE.fullmatch(module):
        raise GateError(f"{which} witness.module is not a valid Lean module name: {module!r}")
    if not isinstance(theorem, str) or not LEAN_IDENT_RE.fullmatch(theorem):
        raise GateError(f"{which} witness.theorem is not a valid Lean declaration name: {theorem!r}")
    return module, theorem


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def validate_common(base: dict[str, Any], head: dict[str, Any]) -> None:
    if base.get("schema_version") != 1 or head.get("schema_version") != 1:
        raise GateError("boundary frontier schema_version must remain 1")
    if base.get("frontier_id") != head.get("frontier_id"):
        raise GateError("frontier_id is immutable")
    if base.get("target") != head.get("target"):
        raise GateError(
            "the canonical open target is immutable in a boundary-advance PR; "
            "do not redefine the problem to make the gate pass"
        )


def validate_transition(
    base: dict[str, Any], head: dict[str, Any], changed: set[str]
) -> tuple[str, str, Fraction | None]:
    validate_common(base, head)
    base_kind = manifest_kind(base, "base")
    head_kind = manifest_kind(head, "candidate")

    if base_kind == "rh_scale":
        raise GateError(
            "the canonical RH-scale frontier is already certified; no weaker frontier transition is allowed"
        )

    module, theorem = witness(head, "candidate")
    witness_path = module_path(module)
    if witness_path not in changed:
        raise GateError(
            f"the witness module {witness_path} must be changed in the same PR as the frontier"
        )

    if head_kind == "rh_scale":
        return module, theorem, None

    if head_kind != "power_bound":
        raise GateError(
            "Lean-source research changes must move the frontier to power_bound or rh_scale; "
            "exact_reduction is not an advance"
        )

    candidate_exp = exponent_fraction(head, "candidate")
    if base_kind == "exact_reduction":
        if not candidate_exp < 1:
            raise GateError(
                "the first quantitative frontier must certify a genuine power saving: exponent < 1"
            )
    elif base_kind == "power_bound":
        base_exp = exponent_fraction(base, "base")
        if not candidate_exp < base_exp:
            raise GateError(
                f"candidate exponent {candidate_exp} is not strictly smaller than certified exponent {base_exp}"
            )
    else:
        raise GateError(f"unsupported base frontier kind {base_kind!r}")

    return module, theorem, candidate_exp


def lean_check_source(module: str, theorem: str, exponent: Fraction | None) -> str:
    lines = [
        "import RHLean.Analysis.MobiusSynthesisBoundary",
        f"import {module}",
        "",
        "open RHLean.Analysis.MobiusSynthesisBoundary",
        "",
    ]
    if exponent is None:
        lines.append(f"example : NonzeroResponseRHScale := {theorem}")
    else:
        lines.append(
            "example : NonzeroResponsePowerBound "
            f"(({exponent.numerator} : ℝ) / {exponent.denominator}) := {theorem}"
        )
    lines.append(f"#print axioms {theorem}")
    lines.append("")
    return "\n".join(lines)


def audit_axioms_log(path: Path) -> None:
    if not path.is_file():
        raise GateError(f"axiom audit log does not exist: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    if "does not depend on any axioms" in text:
        print("BOUNDARY AXIOM AUDIT: PASS (witness has no axiom dependencies)")
        return
    matches = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, flags=re.DOTALL)
    if not matches:
        raise GateError("could not locate Lean #print axioms output for the boundary witness")
    names: set[str] = set()
    for payload in matches:
        for item in payload.split(","):
            name = item.strip()
            if name:
                names.add(name)
    unexpected = names - ALLOWED_AXIOMS
    if unexpected:
        raise GateError(
            "boundary witness depends on nonstandard axioms: "
            + ", ".join(sorted(unexpected))
        )
    print(
        "BOUNDARY AXIOM AUDIT: PASS (only standard logical axioms: "
        + (", ".join(sorted(names)) if names else "none")
        + ")"
    )


def write_output(path: str | None, key: str, value: str) -> None:
    if not path:
        return
    with open(path, "a", encoding="utf-8") as handle:
        handle.write(f"{key}={value}\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".")
    parser.add_argument("--base-sha")
    parser.add_argument("--head-sha")
    parser.add_argument("--audit-axioms-log")
    parser.add_argument("--github-output")
    parser.add_argument("--lean-check-file", default="/tmp/mobius_boundary_witness.lean")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    try:
        if args.audit_axioms_log:
            audit_axioms_log(Path(args.audit_axioms_log))
            return 0
        if not args.base_sha or not args.head_sha:
            raise GateError("--base-sha and --head-sha are required for frontier evaluation")

        changed = changed_files(repo, args.base_sha, args.head_sha)
        source_changed = {
            path
            for path in changed
            if path == "RHLean.lean" or (path.startswith("RHLean/") and path.endswith(".lean"))
        }
        frontier_changed = FRONTIER_PATH in changed
        contract_changed = CONTRACT_PATH in changed

        if not source_changed:
            if frontier_changed:
                raise GateError(
                    f"{FRONTIER_PATH} changed without a Lean-source change; frontier claims require a proof witness"
                )
            write_output(args.github_output, "needs_lean", "false")
            print("BOUNDARY GATE: PASS (non-research change; certified analytic frontier unchanged)")
            return 0

        if contract_changed:
            raise GateError(
                f"{CONTRACT_PATH} is the canonical boundary contract and cannot be weakened or rewritten in the same PR"
            )

        if not frontier_changed:
            raise GateError(
                "Lean mathematical source changed but boundary/frontier.json did not. "
                "Equivalent identities, reindexings, alternate bases, and other representation-only changes "
                "do not advance the synthesis frontier."
            )

        base = load_base_manifest(repo, args.base_sha)
        head = load_head_manifest(repo)
        module, theorem, exponent = validate_transition(base, head, changed)

        check_path = Path(args.lean_check_file)
        check_path.write_text(lean_check_source(module, theorem, exponent), encoding="utf-8")
        write_output(args.github_output, "needs_lean", "true")
        write_output(args.github_output, "witness_check", str(check_path))

        if exponent is None:
            print(f"BOUNDARY GATE: STRUCTURAL PASS; candidate certifies RH scale via {theorem}")
        else:
            print(
                "BOUNDARY GATE: STRUCTURAL PASS; candidate strictly advances to "
                f"power exponent {exponent} via {theorem}"
            )
        print(f"Lean witness check written to {check_path}")
        return 0
    except GateError as exc:
        print("BOUNDARY GATE: FAIL", file=sys.stderr)
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
