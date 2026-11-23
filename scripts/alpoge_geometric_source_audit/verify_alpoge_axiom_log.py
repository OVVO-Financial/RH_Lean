#!/usr/bin/env python3
"""Require actual #print axioms receipts for every selected closed declaration."""

import argparse
import json
from pathlib import Path
import re


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    text = re.sub(r"\x1b\[[0-9;]*m", "", args.log.read_text())
    receipts = {}
    for match in re.finditer(r"'([^'\n]+)'\s+depends on axioms:\s*\[([^]]*)\]", text):
        receipts[match.group(1)] = sorted(set(x.strip() for x in match.group(2).split(",") if x.strip()))
    for match in re.finditer(r"'([^'\n]+)'\s+does not depend on any axioms", text):
        receipts[match.group(1)] = []
    allowed = set(manifest["allowed_terminal_axioms"])
    findings = []
    checked = {}
    for target in manifest["required_axiom_targets"]:
        if target not in receipts:
            findings.append({"target": target, "problem": "missing axiom receipt"})
            continue
        axioms = receipts[target]
        checked[target] = axioms
        forbidden = sorted(set(axioms) - allowed)
        if forbidden:
            findings.append({"target": target, "problem": "nonstandard axioms", "axioms": forbidden})
    report = {"status": "passed" if not findings else "failed", "targets": checked,
              "allowed_terminal_axioms": sorted(allowed), "findings": findings,
              "scope": "Axiom receipts only; successful fresh source build is separately required."}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if findings:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
