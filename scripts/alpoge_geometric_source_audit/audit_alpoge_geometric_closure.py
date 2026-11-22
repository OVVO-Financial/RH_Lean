#!/usr/bin/env python3
"""Audit and optionally materialize a pinned, source-only Lean import closure.

This script never invokes Lean, Lake, or elan.  It establishes source identity,
the selected import graph, and lexical absence of specified proof escapes.
Successful execution is NOT evidence that the Lean declarations compile.
The separate hosted build and axiom-log gate provide that evidence.
"""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def lean_code(text: str) -> str:
    """Blank nested comments and strings, retaining newlines and offsets."""
    out = list(text)
    i, depth, string = 0, 0, False
    markers = re.compile(r'/-|--|"')
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            match = markers.search(text, i + 1)
            if match is None:
                break
            i = match.start()
    if depth or string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def imports(code: str) -> list[str]:
    found = []
    for match in re.finditer(r"(?m)^\s*(?:(?:public|private)\s+)?import[ \t]+([^\n]+)", code):
        found.extend(match.group(1).split())
    return found


def tracked_blobs(repo: Path) -> dict[str, str]:
    raw = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", "-z", "HEAD"])
    result = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        meta, path = item.split(b"\t", 1)
        _mode, kind, blob = meta.split()
        if kind == b"blob":
            result[path.decode()] = blob.decode()
    return result


def scan(code: str, patterns: dict[str, str]) -> list[dict]:
    found = []
    for label, regex in patterns.items():
        for match in re.finditer(regex, code):
            found.append({"kind": label, "line": code.count("\n", 0, match.start()) + 1,
                          "token": match.group(0)})
    return found


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--manifest", type=Path, required=True)
    p.add_argument("--profile", default="closed-short-constructor")
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--export-source", type=Path,
                   help="New empty directory receiving verified sources/configs only")
    args = p.parse_args()
    repo = args.source.resolve()
    manifest = json.loads(args.manifest.read_text())
    manifest_dir = args.manifest.resolve().parent
    pin = manifest["upstream"]
    if git(repo, "rev-parse", "HEAD") != pin["commit"]:
        p.error("Source HEAD does not match the manifest pin")
    if git(repo, "rev-parse", "HEAD:src") != pin["src_tree"]:
        p.error("Source tree does not match the manifest pin")
    tracked = tracked_blobs(repo)
    findings: list[dict] = []
    configs = []
    for name, expected in pin["config_git_blobs"].items():
        path = repo / name
        actual = git_blob(path.read_bytes())
        configs.append({"path": name, "git_blob": actual})
        if tracked.get(name) != expected or actual != expected:
            findings.append({"kind": "config_hash_mismatch", "path": name})

    local = manifest["local_modules"]
    records: dict[str, dict] = {}
    sources: dict[str, Path] = {}
    external: dict[str, set[str]] = {}
    active: dict[str, set[str]] = {}
    meta_inventory = []
    deny_modules = manifest["denied_module_regexes"]
    allowed_external = set(manifest["allowed_external_roots"])

    def read_module(mod: str, parent: str) -> dict | None:
        if mod in records:
            return records[mod]
        if any(re.search(pattern, mod) for pattern in deny_modules):
            findings.append({"kind": "forbidden_terminal_import", "module": mod,
                             "imported_by": parent})
        if mod in local:
            path = manifest_dir / local[mod]["file"]
            relative = "@local/" + local[mod]["file"]
            expected = None
        else:
            relative = "src/" + mod.replace(".", "/") + ".lean"
            expected = tracked.get(relative)
            if expected is None:
                if mod.split(".", 1)[0] in allowed_external:
                    external.setdefault(mod, set()).add(parent)
                else:
                    findings.append({"kind": "missing_or_unapproved_import", "module": mod,
                                     "imported_by": parent})
                return None
            path = repo / relative
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if expected is not None and git_blob(data) != expected:
            findings.append({"kind": "source_hash_mismatch", "path": relative})
        if mod in local and digest != local[mod]["sha256"]:
            findings.append({"kind": "local_target_hash_mismatch", "path": relative})
        try:
            code = lean_code(data.decode("utf-8"))
        except (ValueError, UnicodeDecodeError) as error:
            findings.append({"kind": "parse_failure", "path": relative, "message": str(error)})
            return None
        dependencies = imports(code)
        for finding in scan(code, manifest["forbidden_code_patterns"]):
            findings.append({"module": mod, "path": relative, **finding})
        for finding in scan(code, manifest.get("inventory_code_patterns", {})):
            meta_inventory.append({"module": mod, "path": relative, **finding})
        record = {"module": mod, "path": relative, "git_blob": expected,
                  "sha256": digest, "bytes": len(data), "lines": len(data.splitlines()),
                  "imports": dependencies}
        records[mod] = record
        sources[mod] = path
        return record

    roots = manifest["profiles"][args.profile]
    for root in roots:
        seen: set[str] = set()
        queue = deque([(root, "@root")])
        while queue:
            mod, parent = queue.popleft()
            if mod in seen:
                continue
            seen.add(mod)
            rec = read_module(mod, parent)
            if rec is not None:
                queue.extend((imp, mod) for imp in rec["imports"])
        active[root] = seen.intersection(records)

    ordered = [records[mod] for mod in sorted(records)]
    seal = hashlib.sha256(json.dumps(ordered, ensure_ascii=False, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()
    report = {
        "schema_version": 1,
        "scope": "Static source identity/import audit. No Lean execution; not proof acceptance.",
        "upstream_commit": pin["commit"], "src_tree": pin["src_tree"],
        "profile": args.profile, "roots": roots,
        "status": "static_source_audit_passed" if not findings else "static_source_audit_failed",
        "source_modules": sum(rec["git_blob"] is not None for rec in ordered),
        "local_modules": sum(rec["git_blob"] is None for rec in ordered),
        "source_bytes": sum(rec["bytes"] for rec in ordered),
        "source_lines": sum(rec["lines"] for rec in ordered),
        "source_closure_sha256": seal,
        "root_counts": {root: {"modules": len(mods),
                               "bytes": sum(records[m]["bytes"] for m in mods),
                               "lines": sum(records[m]["lines"] for m in mods)}
                        for root, mods in active.items()},
        "configs": configs,
        "external_imports": [{"module": mod, "imported_by": sorted(parents)}
                             for mod, parents in sorted(external.items())],
        "findings": findings,
        "metaprogram_inventory": meta_inventory,
        "modules": ordered,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                      ("status", "source_modules", "local_modules", "source_bytes", "source_lines",
                       "source_closure_sha256", "root_counts", "findings")}, ensure_ascii=False, indent=2))
    if findings:
        return 1
    if args.export_source:
        export = args.export_source.resolve()
        if export.exists() and any(export.iterdir()):
            p.error("Export destination must be absent or empty")
        export.mkdir(parents=True, exist_ok=True)
        for mod, path in sources.items():
            dest = export / "src" / (mod.replace(".", "/") + ".lean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, dest)
        for name in pin["config_git_blobs"]:
            if name != "README.md":
                shutil.copyfile(repo / name, export / name)
        # Explicit audit target; default project targets (including Main) are never built.
        with (export / "lakefile.toml").open("a") as handle:
            handle.write('\n[[lean_lib]]\nname = "AlpogeGeometryAudit"\nroots = ' +
                         json.dumps([mod for mod in local if mod in records]) + '\n')
        (export / "source-audit-receipt.json").write_text(json.dumps({
            "upstream_commit": pin["commit"], "profile": args.profile,
            "source_closure_sha256": seal, "project_oleans_copied": 0}, indent=2) + "\n")
        print("Exported verified source only: " + str(export))
    return 0


if __name__ == "__main__":
    sys.exit(main())
