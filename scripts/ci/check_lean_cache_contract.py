#!/usr/bin/env python3
"""Require a reusable compiled-cache path on every newly added/touched Lean CI workflow.

Existing historical workflows are not bulk-rewritten: enforcement is activated
when their YAML changes, so additions cannot reintroduce cold-only OAI DAG
builds or ad-hoc Lean installation. No GitHub API or third-party YAML parser.
"""
from __future__ import annotations

import argparse
from pathlib import Path
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


def audit(path: Path) -> list[str]:
    src = path.read_text(encoding="utf-8")
    # Composite callers don't spell 'lake build' but are still Lean jobs.
    is_lean = any(x in src for x in (
        "lake build", "lake env lean", "lake exe cache get",
        "./.github/actions/research-compile", "leanprover/lean4",
    ))
    if not is_lean:
        return []
    # An isolated OAI project still needs its exact OAI toolchain. All
    # RHLean/native or combined jobs must use the shared pinned setup.
    original_oai = "repository: openai/math" in src
    native = not original_oai or "check_shared_lean_packages.py" in src
    problems: list[str] = []
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
    paths = changed_workflows(args.base)
    for path in paths:
        problems = audit(path)
        if problems:
            for issue in problems:
                print(f"::error file={path}::{issue}")
            bad += len(problems)
        else:
            print(f"cache contract accepted: {path}")
    print(f"Audited {len(paths)} changed workflow(s); violations={bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
