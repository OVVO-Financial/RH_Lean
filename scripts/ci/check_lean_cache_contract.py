#!/usr/bin/env python3
"""Require pinned cache reuse and keep original-OAI replay explicitly manual.

Cache-path enforcement covers newly added/touched workflow YAML. The original-
OAI retirement rule scans every workflow, since a shared helper change can
activate an older workflow without touching its YAML. No GitHub API or
third-party YAML parser is needed.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys


def changed_workflows(base: str) -> list[Path]:
    diff = subprocess.run(
        ["git", "diff", "--diff-filter=AM", "--name-only", f"{base}...HEAD",
         "--", ".github/workflows"],
        check=True, capture_output=True, text=True,
    )
    return [
        Path(p) for p in diff.stdout.splitlines()
        if p.endswith((".yml", ".yaml")) and Path(p).is_file()
    ]


def yaml_block(src: str, key: str, indent: int = 0) -> str:
    """Read a block from the repository's block-style workflow YAML.

    This deliberately uses no optional YAML dependency. Unknown formatting
    cannot establish the explicit manual gate required below.
    """
    lines = src.splitlines()
    prefix = " " * indent + key + ":"
    for start, line in enumerate(lines):
        if not line.startswith(prefix):
            continue
        end = start + 1
        while end < len(lines):
            following = lines[end]
            if following.strip() and not following.lstrip().startswith("#"):
                if len(following) - len(following.lstrip()) <= indent:
                    break
            end += 1
        return "\n".join(lines[start:end])
    return ""


def original_oai_replay(src: str) -> bool:
    """Recognize upstream checkout/cache/build references regardless of YAML quotes."""
    return any(marker in src.lower() for marker in (
        "openai/math", "oai-434-shared-cache",
        "oai.numbertheory.",
    ))


def manual_only(triggers: str) -> bool:
    """Accept only an unambiguous dispatch-only trigger; unknown syntax fails closed."""
    if not triggers:
        return False
    header = triggers.splitlines()[0].split("#", 1)[0].strip()
    if header != "on:":
        return bool(re.fullmatch(r"on: *(?:workflow_dispatch|\[ *workflow_dispatch *\])", header))
    children = [line.split("#", 1)[0].rstrip() for line in triggers.splitlines()[1:]
                if line.strip() and not line.lstrip().startswith("#")
                and len(line) - len(line.lstrip()) <= 2]
    return len(children) == 1 and bool(re.fullmatch(r"  workflow_dispatch: *(?:\{\})?", children[0]))


def automatic_oai_jobs(src: str) -> list[str]:
    """Find original-OAI jobs that can run without an explicit manual opt-in."""
    if not original_oai_replay(src):
        return []
    triggers = yaml_block(src, "on")
    if manual_only(triggers):
        return []
    jobs = yaml_block(src, "jobs")
    names = re.findall(r"^  ([A-Za-z_][\w-]*):", jobs, re.MULTILINE)
    blocks = [(name, yaml_block(jobs, name, 2)) for name in names]
    # A quoted/flow-style job or a reference outside the recognized job blocks
    # cannot silently disappear from the audit.
    unmatched = jobs
    for _, body in blocks:
        unmatched = unmatched.replace(body, "", 1)
    unmatched += src.replace(jobs, "", 1) if jobs else src
    dispatch = yaml_block(triggers, "workflow_dispatch", 2)
    inputs = yaml_block(dispatch, "inputs", 4)
    unsafe = ["workflow (unrecognized structure)"] if original_oai_replay(unmatched) else []
    for name, body in blocks:
        if not original_oai_replay(body):
            continue
        gate = re.search(r"^    if: *\$\{\{ *(.*?) *\}\} *$", body, re.MULTILINE)
        match = None if gate is None else re.fullmatch(
            r"github\.event_name\s*==\s*'workflow_dispatch'\s*&&\s*inputs\.([A-Za-z_][\w]*)",
            gate.group(1).strip(),
        )
        option = "" if match is None else yaml_block(inputs, match.group(1), 6)
        boolean = re.search(r"^        type: *boolean *(?:#.*)?$", option, re.MULTILINE)
        default_off = re.search(r"^        default: *false *(?:#.*)?$", option, re.MULTILINE)
        if not (match and boolean and default_off):
            unsafe.append(name)
    return unsafe


def oai_retirement_problems(src: str) -> list[str]:
    return [
        f"original OpenAI job '{job}' requires an explicit workflow_dispatch "
        "boolean opt-in with default false; it must not run automatically"
        for job in automatic_oai_jobs(src)
    ]


def audit(path: Path) -> list[str]:
    src = path.read_text(encoding="utf-8")
    problems = oai_retirement_problems(src)
    # Composite callers don't spell 'lake build' but are still Lean jobs.
    is_lean = any(x in src for x in (
        "lake build", "lake env lean", "lake exe cache get",
        "./.github/actions/research-compile", "leanprover/lean4",
    ))
    if not is_lean:
        return problems
    # An isolated OAI project still needs its exact OAI toolchain. All
    # RHLean/native or combined jobs must use the shared pinned setup.
    original_oai = "openai/math" in src.lower()
    native = not original_oai or "check_shared_lean_packages.py" in src
    if native and "./.github/actions/lean-setup" not in src:
        problems.append("must use ./.github/actions/lean-setup (pinned Lean and Mathlib)")
    if "lake exe cache get" in src and "actions/cache/restore" not in src and (
        "./.github/actions/oai-434-shared-cache" not in src
    ):
        problems.append("cold-only 'lake exe cache get' lacks a reusable compiled OpenAI cache")
    if original_oai and (
        "actions/cache/restore" not in src
        and "./.github/actions/oai-434-shared-cache" not in src
    ):
        problems.append("original OpenAI checkout requires a compiled DAG restore path")
    if original_oai and "check_shared_lean_packages.py" in src and (
        "./.github/actions/oai-434-shared-cache" not in src
    ):
        problems.append("mixed RHLean/OpenAI jobs must use the shared unpatched-PNT cache")
    return problems


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--base", required=True, help="git ref for base branch, e.g. origin/main")
    args = p.parse_args()
    bad = 0
    changed = set(changed_workflows(args.base))
    all_paths = changed | set(Path(".github/workflows").glob("*.yml")) | set(
        Path(".github/workflows").glob("*.yaml"))
    for path in sorted(all_paths):
        problems = audit(path) if path in changed else oai_retirement_problems(
            path.read_text(encoding="utf-8"))
        if problems:
            for issue in problems:
                print(f"::error file={path}::{issue}")
            bad += len(problems)
        elif path in changed:
            print(f"cache contract accepted: {path}")
    print(f"Audited cache paths in {len(changed)} changed workflow(s) and original-OAI "
          f"retirement in all {len(all_paths)} workflow(s); violations={bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
