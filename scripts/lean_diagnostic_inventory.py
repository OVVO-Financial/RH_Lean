#!/usr/bin/env python3
"""Collapse a Lean build log into a deduplicated diagnostic inventory.

A `lake build` log for this project is several thousand lines.  Almost all of
it is a handful of distinct diagnostics repeated once per module rebuild, which
makes the tail of a CI log useless for answering the only question that matters
after a red run: *which source positions are still noisy?*

This script groups every `warning:`/`error:`/`info:` diagnostic by the source
file it points at, deduplicates identical `file:line:col` positions, and prints
one sorted line per position.  With `--gate PREFIX` it exits non-zero when any
diagnostic points into a source tree whose path starts with `PREFIX`, which is
how the workflow keeps the repository-owned StrongPNT 4.24 port silent.

Lean and Lake have emitted diagnostics in more than one shape over the years:

    warning: Foo/Bar.lean:12:4: This simp argument is unused:
    Foo/Bar.lean:12:4: warning: This simp argument is unused:
    error: Foo/Bar.lean:12:4: Type mismatch

so the position is matched wherever it sits on the line rather than assuming a
single formatter.  Lines with no `file:line:col` at all (`error: build failed`,
`Some required targets logged failures:`) carry no position to fix and are
skipped.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

# `path:line:col` where path ends in `.lean`.  Paths may be absolute (the
# `trace:` lines echo full runner paths) or repository relative.
POSITION = re.compile(r"(?P<path>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+)")
SEVERITY = re.compile(r"\b(?P<severity>warning|error|info):")

# Diagnostics whose text continues on following lines; only the first line
# carries the position, which is all the inventory reports.
SEVERITY_ORDER = {"error": 0, "warning": 1, "info": 2}
TARGET_STATUS = Path(".github/strong-mertens-k2-clean-status.txt")


def normalize(path: str) -> str:
    """Strip runner-specific prefixes so keys are stable across machines."""
    cleaned = path.lstrip("./")
    for marker in (".lake/packages/",):
        index = cleaned.find(marker)
        if index != -1:
            cleaned = cleaned[index + len(marker) :]
            head, _, tail = cleaned.partition("/")
            if tail.startswith(head + "/"):
                cleaned = tail
            else:
                cleaned = tail or cleaned
            break
    else:
        marker = "/RH_Lean/"
        index = cleaned.rfind(marker)
        if index != -1:
            cleaned = cleaned[index + len(marker) :]
    return cleaned


def collect(log: str) -> dict[str, set[tuple[int, int, str, str]]]:
    """Map source file -> {(line, col, severity, first line of message)}."""
    found: dict[str, set[tuple[int, int, str, str]]] = defaultdict(set)
    lines = log.splitlines()
    for index, raw in enumerate(lines):
        if raw.lstrip().startswith("trace:"):
            continue
        severity_match = SEVERITY.search(raw)
        if severity_match is None:
            continue
        severity = severity_match.group("severity")
        position = POSITION.search(raw)
        if position is None:
            continue
        message = raw[position.end() :].lstrip(": ").strip()
        message = SEVERITY.sub("", message, count=1).strip()
        if message.endswith(":"):
            message = f"{message} {continuation(lines, index)}".strip()
        found[normalize(position.group("path"))].add(
            (int(position.group("line")), int(position.group("col")), severity, message)
        )
    return found


def continuation(lines: list[str], index: int) -> str:
    """First indented, non-blank line after `index`, or the empty string."""
    for raw in lines[index + 1 : index + 4]:
        if not raw.strip():
            continue
        if raw[:1].isspace():
            return " ".join(raw.split())
        return ""
    return ""


def is_noise(entry: tuple[int, int, str, str]) -> bool:
    """Does this diagnostic represent linter churn a patch should remove?"""
    _line, _col, severity, message = entry
    if severity in ("warning", "error"):
        return True
    return message.startswith("Try this:")


def report(found: dict[str, set[tuple[int, int, str, str]]]) -> None:
    if not found:
        print("No Lean diagnostics with source positions in this build log.")
        return
    for path in sorted(found):
        entries = sorted(
            found[path], key=lambda e: (e[0], e[1], SEVERITY_ORDER.get(e[2], 9))
        )
        print(f"\n{path}  ({len(entries)} distinct)")
        for line, col, severity, message in entries:
            print(f"  {line}:{col}  {severity}: {message}")


def targeted_probe() -> int:
    """Temporary branch-only compiler probe used during the clean rebuild."""
    if not TARGET_STATUS.exists():
        return 0
    target = ""
    for line in TARGET_STATUS.read_text().splitlines():
        if line.startswith("target="):
            target = line.partition("=")[2].strip()
            break
    if not target:
        return 0
    print(f"\n=== targeted compiler probe: {target} ===")
    proc = subprocess.run(
        ["lake", "build", target],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    print(proc.stdout, end="")
    print(f"=== targeted compiler probe exit: {proc.returncode} ===")
    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="path to the captured lake build log")
    parser.add_argument(
        "--gate",
        action="append",
        default=[],
        metavar="PREFIX",
        help="fail when a diagnostic points at a source path starting with PREFIX",
    )
    args = parser.parse_args()

    if not args.gate:
        probe = targeted_probe()
        if probe != 0:
            return probe

    found = collect(args.log.read_text(errors="replace"))

    if not args.gate:
        print("Deduplicated Lean diagnostic inventory")
        print("=====================================")
        report(found)
        return 0

    offending = {}
    for path, entries in found.items():
        if not any(path.startswith(prefix) for prefix in args.gate):
            continue
        gated = {entry for entry in entries if is_noise(entry)}
        if gated:
            offending[path] = gated
    if offending:
        joined = ", ".join(args.gate)
        print(f"Diagnostics remain in gated sources ({joined}):")
        report(offending)
        print(
            "\nThese sources are rewritten by scripts/strongpnt_424/, so each "
            "position above is fixed by extending those patches."
        )
        return 1
    print(f"No diagnostics in gated sources ({', '.join(args.gate)}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
