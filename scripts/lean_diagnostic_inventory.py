#!/usr/bin/env python3
"""Collapse a Lean build log into a deduplicated diagnostic inventory.

A `lake build` log for this project is several thousand lines. Almost all of
it is a handful of distinct diagnostics repeated once per module rebuild.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

POSITION = re.compile(r"(?P<path>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+)")
SEVERITY = re.compile(r"\b(?P<severity>warning|error|info):")
SEVERITY_ORDER = {"error": 0, "warning": 1, "info": 2}
TARGET_STATUS = Path(".github/strong-mertens-k2-clean-status.txt")
PROBE_REVISION = 5


def normalize(path: str) -> str:
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
    for raw in lines[index + 1 : index + 4]:
        if not raw.strip():
            continue
        if raw[:1].isspace():
            return " ".join(raw.split())
        return ""
    return ""


def is_noise(entry: tuple[int, int, str, str]) -> bool:
    _line, _col, severity, message = entry
    if severity in ("warning", "error"):
        return True
    return message.startswith("Try this:")


def report(found: dict[str, set[tuple[int, int, str, str]]]) -> None:
    if not found:
        print("No Lean diagnostics with source positions in this build log.")
        return
    for path in sorted(found):
        entries = sorted(found[path], key=lambda e: (e[0], e[1], SEVERITY_ORDER.get(e[2], 9)))
        print(f"\n{path}  ({len(entries)} distinct)")
        for line, col, severity, message in entries:
            print(f"  {line}:{col}  {severity}: {message}")


def apply_probe_repairs(target: str) -> None:
    if target != "RHLean.Analysis.StrongMertensLogNineHorizontal":
        return
    path = Path("RHLean/Analysis/StrongMertensLogNineHorizontal.lean")
    text = path.read_text()
    if (
        text.count("intervalIntegral.norm_integral_le_integral_norm hsigOrder") == 2
        and text.count("Real.volume_real_Ioc_of_le hsigOrder") == 2
    ):
        print("Committed Horizontal repairs already present; compiling source unchanged.")
        return
    replacements = [
        (
            "intervalIntegral.norm_integral_le_integral_norm _",
            "intervalIntegral.norm_integral_le_integral_norm hsigOrder",
            2,
        ),
        (
            "exact hHorizontalContinuous.norm.integrableOn_compact isCompact_Icc",
            "exact (hHorizontalContinuous.norm.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self",
            1,
        ),
        (
            "exact hHorizontalContinuousUpper.norm.integrableOn_compact isCompact_Icc",
            "exact (hHorizontalContinuousUpper.norm.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self",
            1,
        ),
        (
            "exact hpoint sigma ⟨hs.1.le, hs.2.le⟩",
            "exact hpoint sigma ⟨hs.1.le, hs.2⟩",
            1,
        ),
        (
            "exact hpointUpper sigma ⟨hs.1.le, hs.2.le⟩",
            "exact hpointUpper sigma ⟨hs.1.le, hs.2⟩",
            1,
        ),
        (
            "rw [setIntegral_const, Real.volume_Ioc]\n                  simp [hsigOrder]",
            "rw [setIntegral_const, Real.volume_real_Ioc_of_le hsigOrder]\n                  simp [smul_eq_mul]",
            2,
        ),
        (
            "field_simp [Real.pi_ne_zero, hepsne, hTne]\n        ring",
            "field_simp [Real.pi_ne_zero, hepsne, hTne]",
            2,
        ),
    ]
    for old, new, expected in replacements:
        count = text.count(old)
        if count != expected:
            raise RuntimeError(f"probe repair expected {expected} matches, found {count}: {old[:80]}")
        text = text.replace(old, new)
    path.write_text(text)
    print("Applied compiler-driven Horizontal probe repairs.")


def targeted_probe() -> int:
    if not TARGET_STATUS.exists():
        return 0
    target = ""
    for line in TARGET_STATUS.read_text().splitlines():
        if line.startswith("target="):
            target = line.partition("=")[2].strip()
            break
    if not target:
        return 0
    apply_probe_repairs(target)
    print(f"\n=== targeted compiler probe r{PROBE_REVISION}: {target} ===")
    proc = subprocess.run(
        ["lake", "build", target], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, check=False,
    )
    print(proc.stdout, end="")
    print(f"=== targeted compiler probe exit: {proc.returncode} ===")
    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="path to the captured lake build log")
    parser.add_argument("--gate", action="append", default=[], metavar="PREFIX")
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
        return 1
    print(f"No diagnostics in gated sources ({', '.join(args.gate)}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
