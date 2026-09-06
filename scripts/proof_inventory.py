#!/usr/bin/env python3
"""Inventory the primary RHLean Lean source tree.

This is deliberately dependency-free and cheap enough for CI.  It answers two
questions that are otherwise surprisingly hard to see in a large formalization:

* how large is the compiled proof surface?;
* how are the source modules connected by imports?

The inventory is source-level, not an elaborated theorem dependency graph.
Named proofs mean top-level `theorem` and `lemma` declarations after Lean
comments have been stripped.  The import graph is exact at module granularity.

By default the script prints a human-readable summary.  Optional JSON and DOT
outputs make the same inventory easy for research agents and graph tooling to
query without reparsing the repository.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Iterable

SOURCE_ROOT = Path("RHLean")
ROOT_MANIFEST = Path("RHLean.lean")

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom)\b"
)
NAMED_PROOF_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma)\s+([^\s(:{\[]+)"
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")


def strip_lean_comments(text: str) -> str:
    """Strip Lean `--` and nested `/- -/` comments while preserving newlines.

    String literals are retained so comment-looking text inside strings does not
    alter comment depth.  The output has the same number of newline characters
    as the input, which keeps declaration line numbers stable.
    """

    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    escaped = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue

        if ch == "-" and nxt == "-":
            # Preserve the newline but blank the rest of this physical line.
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def bucket(path: Path) -> str:
    parts = path.parts
    if len(parts) >= 2 and parts[0] == SOURCE_ROOT.name:
        return parts[1]
    return "root"


def source_files() -> list[Path]:
    if not SOURCE_ROOT.is_dir():
        raise SystemExit(f"ERROR: {SOURCE_ROOT}/ not found; run from repository root")
    files = sorted(SOURCE_ROOT.rglob("*.lean"))
    if ROOT_MANIFEST.is_file():
        files.append(ROOT_MANIFEST)
    return files


def imports_from(clean: str) -> list[str]:
    imports: list[str] = []
    for line in clean.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
    return imports


def internal_import_graph(module_files: list[Path], cleaned: dict[Path, str]) -> dict[str, list[str]]:
    modules = {module_name(p) for p in module_files}
    graph: dict[str, list[str]] = {}
    for path in module_files:
        src = module_name(path)
        graph[src] = sorted({m for m in imports_from(cleaned[path]) if m in modules})
    return graph


def reverse_graph(graph: dict[str, list[str]]) -> dict[str, list[str]]:
    rev: dict[str, list[str]] = {m: [] for m in graph}
    for src, deps in graph.items():
        for dep in deps:
            rev.setdefault(dep, []).append(src)
    for dep in rev:
        rev[dep].sort()
    return rev


def longest_import_depth(graph: dict[str, list[str]]) -> int:
    """Longest path length in the internal import DAG; cycles are tolerated."""

    memo: dict[str, int] = {}
    visiting: set[str] = set()

    def depth(node: str) -> int:
        if node in memo:
            return memo[node]
        if node in visiting:
            return 0
        visiting.add(node)
        d = 0
        for dep in graph.get(node, []):
            d = max(d, 1 + depth(dep))
        visiting.remove(node)
        memo[node] = d
        return d

    return max((depth(m) for m in graph), default=0)


def reachable_from(root: str, graph: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    q: deque[str] = deque([root])
    while q:
        node = q.popleft()
        if node in seen:
            continue
        seen.add(node)
        q.extend(graph.get(node, []))
    return seen


def build_inventory() -> dict[str, object]:
    files = source_files()
    module_files = [p for p in files if p != ROOT_MANIFEST]
    texts = {p: p.read_text(encoding="utf-8") for p in files}
    cleaned = {p: strip_lean_comments(texts[p]) for p in files}

    physical_lines = sum(len(texts[p].splitlines()) for p in files)
    module_physical_lines = sum(len(texts[p].splitlines()) for p in module_files)
    nonblank_lines = sum(
        sum(1 for line in texts[p].splitlines() if line.strip()) for p in files
    )
    code_lines = sum(
        sum(1 for line in cleaned[p].splitlines() if line.strip()) for p in files
    )

    decl_counts: Counter[str] = Counter()
    proof_rows: list[dict[str, object]] = []
    bucket_rows: dict[str, Counter[str]] = defaultdict(Counter)

    for path in module_files:
        raw_lines = texts[path].splitlines()
        clean_lines = cleaned[path].splitlines()
        b = bucket(path)
        bucket_rows[b]["files"] += 1
        bucket_rows[b]["physical_lines"] += len(raw_lines)
        bucket_rows[b]["code_lines"] += sum(1 for line in clean_lines if line.strip())
        for lineno, line in enumerate(clean_lines, 1):
            m = DECL_RE.match(line)
            if m:
                kind = m.group(1)
                decl_counts[kind] += 1
                bucket_rows[b][kind] += 1
            p = NAMED_PROOF_RE.match(line)
            if p:
                proof_rows.append(
                    {
                        "kind": p.group(1),
                        "name": p.group(2),
                        "module": module_name(path),
                        "path": str(path),
                        "line": lineno,
                    }
                )

    graph = internal_import_graph(module_files, cleaned)
    rev = reverse_graph(graph)
    internal_edges = sum(len(v) for v in graph.values())
    roots = sorted(m for m, deps in graph.items() if not deps)
    leaves = sorted(m for m, users in rev.items() if not users)
    top_fanout = sorted(
        ((m, len(users)) for m, users in rev.items()), key=lambda x: (-x[1], x[0])
    )[:20]

    root_imports = imports_from(cleaned.get(ROOT_MANIFEST, ""))
    root_set = set(root_imports)
    module_names = set(graph)
    manifest_missing = sorted(module_names - root_set)
    manifest_extra = sorted(root_set - module_names)

    result: dict[str, object] = {
        "scope": {
            "source_root": str(SOURCE_ROOT),
            "root_manifest": str(ROOT_MANIFEST),
            "excludes": ["export_*", ".lake", "scripts", "research", "docs"],
        },
        "source": {
            "library_modules": len(module_files),
            "lean_files_including_root_manifest": len(files),
            "physical_lines_modules": module_physical_lines,
            "physical_lines_including_root_manifest": physical_lines,
            "nonblank_lines_including_root_manifest": nonblank_lines,
            "comment_stripped_nonblank_lines": code_lines,
        },
        "declarations": dict(sorted(decl_counts.items())),
        "named_proofs": {
            "total_theorem_plus_lemma": decl_counts["theorem"] + decl_counts["lemma"],
            "theorem": decl_counts["theorem"],
            "lemma": decl_counts["lemma"],
            "examples": decl_counts["example"],
        },
        "imports": {
            "internal_edges": internal_edges,
            "longest_internal_import_depth": longest_import_depth(graph),
            "zero_internal_dependency_modules": len(roots),
            "zero_reverse_dependency_modules": len(leaves),
            "manifest_imports": len(root_imports),
            "manifest_missing_modules": manifest_missing,
            "manifest_extra_modules": manifest_extra,
            "top_reverse_dependency_fanout": [
                {"module": m, "direct_importers": n} for m, n in top_fanout
            ],
        },
        "buckets": {
            b: dict(sorted(counts.items())) for b, counts in sorted(bucket_rows.items())
        },
        "proofs": proof_rows,
        "module_import_graph": graph,
    }
    return result


def print_summary(inv: dict[str, object]) -> None:
    src = inv["source"]
    named = inv["named_proofs"]
    imports = inv["imports"]
    decls = inv["declarations"]

    print("RHLean primary-source proof inventory")
    print("====================================")
    print(f"Library modules:                     {src['library_modules']:,}")
    print(f"Lean files incl. root manifest:      {src['lean_files_including_root_manifest']:,}")
    print(f"Physical lines (modules):            {src['physical_lines_modules']:,}")
    print(f"Physical lines (incl. manifest):     {src['physical_lines_including_root_manifest']:,}")
    print(f"Nonblank lines (incl. manifest):     {src['nonblank_lines_including_root_manifest']:,}")
    print(f"Comment-stripped nonblank lines:     {src['comment_stripped_nonblank_lines']:,}")
    print()
    print(f"Named proofs (theorem + lemma):      {named['total_theorem_plus_lemma']:,}")
    print(f"  theorem:                           {named['theorem']:,}")
    print(f"  lemma:                             {named['lemma']:,}")
    print(f"  example:                           {named['examples']:,}")
    for kind in ("def", "abbrev", "structure", "class", "inductive", "instance", "axiom"):
        print(f"  {kind + ':':<35}{decls.get(kind, 0):,}")
    print()
    print(f"Internal module-import edges:        {imports['internal_edges']:,}")
    print(f"Longest internal import depth:       {imports['longest_internal_import_depth']:,}")
    print(f"Root manifest imports:               {imports['manifest_imports']:,}")
    print(f"Manifest missing modules:            {len(imports['manifest_missing_modules']):,}")
    print(f"Manifest extra modules:              {len(imports['manifest_extra_modules']):,}")
    print()
    print("By top-level source area")
    print("------------------------")
    for b, row in inv["buckets"].items():
        proofs = row.get("theorem", 0) + row.get("lemma", 0)
        print(
            f"{b:14} files={row.get('files', 0):4d}  "
            f"lines={row.get('physical_lines', 0):7d}  "
            f"code={row.get('code_lines', 0):7d}  proofs={proofs:6d}"
        )
    print()
    print("Top direct reverse-dependency fanout")
    print("------------------------------------")
    for row in imports["top_reverse_dependency_fanout"][:12]:
        print(f"{row['direct_importers']:4d}  {row['module']}")


def write_dot(path: Path, graph: dict[str, list[str]]) -> None:
    lines = ["digraph RHLeanImports {", "  rankdir=LR;"]
    for src in sorted(graph):
        if not graph[src]:
            lines.append(f'  "{src}";')
        for dep in graph[src]:
            lines.append(f'  "{src}" -> "{dep}";')
    lines.append("}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path, help="write full inventory JSON")
    parser.add_argument("--dot", type=Path, help="write internal module import graph as DOT")
    parser.add_argument("--no-summary", action="store_true", help="suppress human-readable stdout")
    args = parser.parse_args()

    inv = build_inventory()
    if not args.no_summary:
        print_summary(inv)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(inv, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.dot:
        write_dot(args.dot, inv["module_import_graph"])

    missing = inv["imports"]["manifest_missing_modules"]
    extra = inv["imports"]["manifest_extra_modules"]
    return 1 if missing or extra else 0


if __name__ == "__main__":
    raise SystemExit(main())
