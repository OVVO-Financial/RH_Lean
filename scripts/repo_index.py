#!/usr/bin/env python3
"""Search repository sources and navigate their project-scoped Lean import DAG.

Unlike decl_graph.py, this index includes research, documents, scripts, exports,
and optionally fetched Git refs. It records source occurrences, not proof status
or elaborated declaration dependencies. Nothing here certifies compilation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import rhlean_kg as kg

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "rhlean-repo-index/1"
DEFAULT_INDEX = Path("repo-index.json")
TEXT_SUFFIXES = {
    ".lean", ".md", ".py", ".sh", ".json", ".yml", ".yaml", ".toml",
    ".txt", ".c", ".h", ".awk", ".csv", ".tsv", ".tex", ".bib", ".html",
    ".js", ".css", ".svg",
}
SCOPES = ("library", "research", "docs", "scripts", "exports", "config", "other")
IMPORT_LINE = re.compile(r"^(?:(?:public|private)\s+)?import\s+(.+)$")
IMPORT_TOKEN = re.compile(r"(?:«[^»]+»|[\w']+)(?:\.(?:«[^»]+»|[\w']+))*")


def git(root: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    try:
        return subprocess.run(
            ["git", "-C", str(root), *args], input=input_bytes,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        ).stdout
    except subprocess.CalledProcessError as exc:
        raise ValueError(exc.stderr.decode("utf-8", errors="replace").strip()) from exc


def digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


# Capture the producer version at import time. If an editor changes this script
# during a long ref build, that older running process must not stamp its output
# with the new code's fingerprint.
PRODUCER_HASHES = [digest(Path(__file__).read_bytes()), digest(Path(kg.__file__).read_bytes()), digest((ROOT / "scripts" / "semantic_facets.json").read_bytes())]


def eligible(path: str) -> bool:
    return Path(path).suffix.lower() in TEXT_SUFFIXES or Path(path).name == "lean-toolchain"


def scope_for(path: str) -> str:
    if path == "RHLean.lean" or path.startswith("RHLean/"):
        return "library"
    if path.startswith("research/") and path.endswith(".lean"):
        return "research"
    if path.startswith("export_"):
        return "exports"
    if path.endswith((".md", ".tex", ".bib")):
        return "docs"
    if path.startswith(("scripts/", "experiments/", "numerics/")):
        return "scripts"
    if path.startswith(".github/") or path.endswith((".json", ".toml")) or Path(path).name == "lean-toolchain":
        return "config"
    return "other"


def ref_files(root: Path, commit: str) -> dict[str, bytes]:
    """Read a Git tree in one cat-file batch, without changing the checkout."""
    entries = {}
    for record in git(root, "ls-tree", "-rz", "--full-tree", commit).split(b"\0"):
        if not record:
            continue
        meta, raw_path = record.split(b"\t", 1)
        mode, kind, sha = meta.decode().split()
        path = raw_path.decode("utf-8")
        if kind == "blob" and mode in {"100644", "100755"} and eligible(path):
            entries[path] = sha
    shas = sorted(set(entries.values()))
    blob_data = git(root, "cat-file", "--batch", input_bytes=("\n".join(shas) + "\n").encode()) if shas else b""
    blobs = {}
    offset = 0
    for sha in shas:
        end = blob_data.index(b"\n", offset)
        actual, kind, size = blob_data[offset:end].decode().split()
        if actual != sha or kind != "blob":
            raise ValueError(f"unexpected Git blob response for {sha}")
        offset = end + 1
        blobs[sha] = blob_data[offset:offset + int(size)]
        offset += int(size) + 1
    return {path: blobs[sha] for path, sha in entries.items()}


def snapshots(root: Path, refs: list[str]) -> list[dict]:
    paths = sorted(set(git(root, "ls-files", "-z", "--cached", "--others", "--exclude-standard").decode().split("\0")) - {""})
    current = {
        path: (root / path).read_bytes() for path in paths
        if eligible(path) and (root / path).is_file() and not (root / path).is_symlink()
    }
    out = [{"view": "worktree", "commit": git(root, "rev-parse", "HEAD").decode().strip(), "dirty": bool(git(root, "status", "--porcelain")), "files": current}]
    for ref in dict.fromkeys(refs):
        if ref == "worktree":
            raise ValueError("worktree is reserved for the current checkout")
        commit = git(root, "rev-parse", "--verify", "--end-of-options", ref + "^{commit}").decode().strip()
        out.append({"view": ref, "commit": commit, "dirty": False, "files": ref_files(root, commit)})
    return out


def input_fingerprint(views: list[dict]) -> str:
    rows = [SCHEMA, *PRODUCER_HASHES]
    for view in views:
        rows.append(json.dumps([view["view"], view["commit"], view["dirty"]]))
        for path, raw in sorted(view["files"].items()):
            rows.append(json.dumps([view["view"], path, digest(raw)]))
    return digest("\n".join(rows).encode())


def imports_from(text: str) -> list[str]:
    """Parse the import preamble, including quoted names and multiple imports."""
    clean, _ = kg.strip_lean_comments(text)
    imports = []
    for line in clean.splitlines():
        line = line.strip()
        if not line or line in {"prelude", "module"}:
            continue
        match = IMPORT_LINE.fullmatch(line)
        if not match:
            break
        imports.extend(token.replace("«", "").replace("»", "") for token in IMPORT_TOKEN.findall(match.group(1)))
    return sorted(set(imports))


def project_for(path: str, projects: set[str]) -> str:
    for parent in Path(path).parents:
        if parent.as_posix() in projects:
            return parent.as_posix()
    return "."


def build_index(views: list[dict]) -> dict:
    files, declarations, modules, edges, omitted = {}, [], {}, {}, []
    facets = kg.load_facets(ROOT / "scripts" / "semantic_facets.json")
    for view in views:
        label = view["view"]
        projects = {str(Path(p).parent) for p in view["files"] if Path(p).name in {"lakefile.lean", "lakefile.toml"}}
        for path, raw in sorted(view["files"].items()):
            try:
                text = raw.decode("utf-8")
                if "\0" in text:
                    raise ValueError("contains NUL bytes")
            except (UnicodeDecodeError, ValueError):
                omitted.append({"view": label, "path": path, "reason": "not UTF-8 text"})
                continue
            file_id = f"{label}:{path}"
            entry = {"view": label, "commit": view["commit"], "dirty": view["dirty"], "path": path, "scope": scope_for(path), "sha256": digest(raw), "text": text}
            files[file_id] = entry
            if not path.endswith(".lean"):
                continue
            project = project_for(path, projects)
            relative = Path(path) if project == "." else Path(path).relative_to(project)
            module = ".".join(relative.with_suffix("").parts)
            module_id = f"{label}:{project}:{module}"
            modules[module_id] = {"view": label, "project": project, "module": module, "path": path, "scope": entry["scope"], "imports": imports_from(text)}
            for decl in kg.parse_module(Path(path), text):
                tags = kg.tag_declaration(decl.name, {"module": module, "kind": decl.kind, "shape": kg.statement_shape(decl.statement)}, facets)
                declarations.append({
                    "id": f"{file_id}:{decl.line}:{decl.name}", "file_id": file_id,
                    "name": decl.name, "kind": decl.kind, "line": decl.line,
                    "end_line": decl.end_line, "module_id": module_id,
                    "statement": decl.statement, "doc": decl.doc,
                    "facets": tags,
                })
    for module_id, module in modules.items():
        prefix = f"{module['view']}:{module['project']}:"
        edges[module_id] = sorted(prefix + dep for dep in module["imports"] if prefix + dep in modules)
        module["external_imports"] = [dep for dep in module["imports"] if prefix + dep not in modules]
        module["unresolved_local_imports"] = [dep for dep in module["external_imports"] if dep == "RHLean" or dep.startswith(("RHLean.", "research."))]
    components = kg.strongly_connected_components(edges, set(edges))
    cycles = [c for c in components if len(c) > 1 or c[0] in edges[c[0]]]
    return {
        "schema": SCHEMA, "input_fingerprint": input_fingerprint(views),
        "provenance": {"producer": "scripts/repo_index.py", "authority": "Source navigation only; no compilation or theorem-status certificate.", "refs": [v["view"] for v in views if v["view"] != "worktree"], "views": [{"view": v["view"], "commit": v["commit"], "dirty": v["dirty"]} for v in views]},
        "files": files, "declarations": declarations, "modules": modules,
        "module_import_graph": edges, "cyclic_components": cycles, "omitted": omitted,
    }


def load_index(root: Path, path: Path | None, refs: list[str]) -> dict:
    candidate = path or root / DEFAULT_INDEX
    saved = json.loads(candidate.read_text()) if candidate.is_file() else None
    selected_refs = refs or (saved or {}).get("provenance", {}).get("refs", [])
    views = snapshots(root, selected_refs)
    if saved and saved.get("schema") == SCHEMA and saved.get("input_fingerprint") == input_fingerprint(views):
        return saved
    if saved and path is not None:
        raise ValueError(f"stale index {path}; rebuild with repo_index.py build --index {path} and the same --ref options")
    if saved:
        print("note: stale repo-index.json; rebuilding from current source contents and refs", file=sys.stderr)
    return build_index(views)


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")


def write_dot(path: Path, data: dict, selected: set[str] | None = None) -> None:
    nodes = data["modules"]
    selected = set(nodes) if selected is None else selected
    lines = ["digraph RepositoryImports {", "  rankdir=TB;"]
    for node in sorted(selected):
        entry = nodes[node]
        label = f"{entry['view']} / {entry['project']}\n{entry['module']}"
        color = "darkorange" if entry["scope"] == "research" else "steelblue"
        lines.append(f"  {json.dumps(node)} [label={json.dumps(label)}, color={json.dumps(color)}];")
        for dep in data["module_import_graph"][node]:
            if dep in selected:
                lines.append(f"  {json.dumps(node)} -> {json.dumps(dep)};")
    lines.append("}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")


def report(data: dict) -> str:
    lines = ["# Repository source navigation", "", data["provenance"]["authority"], "", "| View | Commit | Files | Lean modules | Named declarations | Import edges |", "| --- | --- | ---: | ---: | ---: | ---: |"]
    for view in data["provenance"]["views"]:
        label = view["view"]
        modules = {m for m, e in data["modules"].items() if e["view"] == label}
        declarations = [d for d in data["declarations"] if d["module_id"] in modules]
        count = sum(e["view"] == label for e in data["files"].values())
        edge_count = sum(len(data["module_import_graph"][m]) for m in modules)
        state = " (modified)" if view["dirty"] else ""
        lines.append(f"| `{label}`{state} | `{view['commit']}` | {count} | {len(modules)} | {len(declarations)} | {edge_count} |")
    lines += ["", "## Current checkout coverage", "", "| Scope | Files |", "| --- | ---: |"]
    counts = Counter(e["scope"] for e in data["files"].values() if e["view"] == "worktree")
    lines += [f"| {scope} | {counts[scope]} |" for scope in SCOPES]
    lines += ["", f"Import cycles: {len(data['cyclic_components'])}. Non-text omissions: {len(data['omitted'])}.", "", "## Unresolved repository-local imports", ""]
    missing = [e for e in data["modules"].values() if e["unresolved_local_imports"]]
    lines += [f"- `{e['view']}:{e['path']}`: {', '.join(e['unresolved_local_imports'])}" for e in missing] or ["None."]
    return "\n".join(lines) + "\n"


def search(data: dict, query: str, *, kind: str = "all", scope: str = "all", view: str | None = None, regex: bool = False, carrier: str | None = None, role: str | None = None) -> list[dict]:
    vocabulary = kg.load_facets(ROOT / "scripts" / "semantic_facets.json")
    if carrier and carrier not in vocabulary["facets"]["carrier"]:
        raise ValueError(f"unknown carrier {carrier!r}; see scripts/semantic_facets.json")
    if role and role not in vocabulary["roles"]:
        raise ValueError(f"unknown role {role!r}; see scripts/semantic_facets.json")
    if view and view not in {v["view"] for v in data["provenance"]["views"]}:
        raise ValueError(f"view {view!r} is not indexed; include it with --ref")
    if kind == "file" and (carrier or role):
        raise ValueError("carrier/role filters apply to declarations; use --kind declaration or all")
    pattern = re.compile(query, re.IGNORECASE) if regex else None
    terms = query.casefold().split()
    if not query.strip():
        raise ValueError("search query must not be empty")
    def matches(text: str) -> bool:
        return bool(pattern.search(text)) if pattern else all(t in text.casefold() for t in terms)
    hits = []
    lines_by_file = {}
    def add(entry: dict, name: str, start: int, body: str, result_kind: str, doc: str = "") -> None:
        context = name + " " + entry["path"]
        if not matches(context + "\n" + doc + "\n" + body):
            return
        doc_only = not matches(context + "\n" + body)
        evidence = body.splitlines()
        target = next((i for i, line in enumerate(evidence) if matches(line)), None)
        if target is None:
            target = next((i for i, line in enumerate(evidence) if pattern.search(line)), None) if pattern else next((i for i, line in enumerate(evidence) if any(t in line.casefold() for t in terms)), None)
        line = start + target if target is not None and not doc_only else start
        excerpt = " ".join(doc.split()) if doc_only else evidence[target].strip() if target is not None else name or entry["path"]
        score = (100 if query.casefold() == name.casefold() else 0) + (40 if matches(name) else 0) + (20 if matches(entry["path"]) else 0) + (10 if result_kind == "declaration" else 0)
        hits.append({"kind": result_kind, "name": name, "view": entry["view"], "commit": entry["commit"], "dirty": entry["dirty"], "source_sha256": entry["sha256"], "scope": entry["scope"], "path": entry["path"], "line": line, "excerpt": excerpt[:220], "evidence": "attached doc (line anchors declaration)" if doc_only else "source", "score": score})
    accepted = {i: e for i, e in data["files"].items() if (scope == "all" or e["scope"] == scope) and (view is None or e["view"] == view)}
    if kind in {"all", "declaration"}:
        for decl in data["declarations"]:
            entry = accepted.get(decl["file_id"])
            if entry is None:
                continue
            tags = decl.get("facets", {})
            if carrier and carrier not in tags.get("facets", {}).get("carrier", []):
                continue
            if role and role not in tags.get("roles", []):
                continue
            # Search the full source occurrence, including proof bodies. A name
            # or statement match is not limited by the old 700-character preview.
            if decl["file_id"] not in lines_by_file:
                lines_by_file[decl["file_id"]] = entry["text"].splitlines()
            source_lines = lines_by_file[decl["file_id"]]
            body = "\n".join(source_lines[decl["line"] - 1:decl["end_line"]])
            add(entry, decl["name"], decl["line"], body, "declaration", decl["doc"])
    if kind in {"all", "file"} and not (carrier or role):
        for entry in accepted.values():
            add(entry, "", 1, entry["text"], "file")
    return sorted(hits, key=lambda h: (-h["score"], h["view"], h["path"], h["line"], h["name"]))


def add_common_arguments(parser) -> None:
    parser.add_argument("--index", type=Path, help="explicit saved index; reject stale contents")
    parser.add_argument("--ref", action="append", default=[], help="also index a fetched Git ref (repeatable; no checkout)")


def add_search_arguments(parser) -> None:
    add_common_arguments(parser)
    parser.add_argument("query", help="case-insensitive terms, all required; --regex enables a regex")
    parser.add_argument("--scope", choices=("all", *SCOPES), default="all")
    parser.add_argument("--kind", choices=("all", "declaration", "file"), default="all")
    parser.add_argument("--view", help="restrict results to worktree or one indexed ref")
    parser.add_argument("--carrier", help="heuristic carrier facet (declaration results only)")
    parser.add_argument("--role", help="heuristic statement role (declaration results only)")
    parser.add_argument("--regex", action="store_true")
    parser.add_argument("--limit", type=int, default=25)
    parser.add_argument("--json", action="store_true", help="print structured results")


def run_search(args) -> int:
    data = load_index(ROOT, args.index, args.ref)
    hits = search(data, args.query, kind=args.kind, scope=args.scope, view=args.view, regex=args.regex, carrier=args.carrier, role=args.role)
    selected = hits[:max(args.limit, 0)]
    if args.json:
        print(json.dumps({"total": len(hits), "results": selected, "provenance": data["provenance"]}, ensure_ascii=False))
    else:
        print(data["provenance"]["authority"])
        for hit in selected:
            state = " modified" if hit["dirty"] else ""
            print(f"[{hit['view']} @ {hit['commit'][:12]}{state}] {hit['scope']} / {hit['kind']} {hit['name']}")
            print(f"  {hit['path']}:{hit['line']}  {hit['excerpt']}")
        print(f"\n{len(hits)} matches; showing {len(selected)}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build", help="generate the complete source index and module DAG")
    add_common_arguments(build)
    build.add_argument("--dot", type=Path)
    build.add_argument("--report", type=Path)
    build.add_argument("--require-acyclic", action="store_true")
    query = sub.add_parser("search", help="search names, full statements/proofs, documents, and scripts")
    add_search_arguments(query)
    module = sub.add_parser("module", help="show imports and importers of a Lean module or source path")
    add_common_arguments(module)
    module.add_argument("name")
    module.add_argument("--view", default="worktree")
    module.add_argument("--project", default=".")
    module.add_argument("--transitive", action="store_true")
    module.add_argument("--dot", type=Path, help="write this module's dependency and importer subgraph")
    args = parser.parse_args()
    try:
        if args.command == "search":
            return run_search(args)
        if args.command == "build":
            data = build_index(snapshots(ROOT, args.ref))
            if args.require_acyclic and data["cyclic_components"]:
                raise ValueError(f"import cycles: {data['cyclic_components']}")
            write_json(args.index or ROOT / DEFAULT_INDEX, data)
            if args.dot:
                write_dot(args.dot, data)
            summary = report(data)
            if args.report:
                args.report.parent.mkdir(parents=True, exist_ok=True)
                args.report.write_text(summary)
            print(summary)
            return 0
        data = load_index(ROOT, args.index, args.ref)
        found = [m for m, e in data["modules"].items() if e["view"] == args.view and e["project"] == args.project and args.name in {m, e["module"], e["path"]}]
        if len(found) != 1:
            raise ValueError(f"expected one module, found {len(found)}; specify its exact path, --view and --project")
        node = found[0]
        edges = data["module_import_graph"]
        reverse = kg.invert(edges)
        imports = kg.reachable(edges, [node]) - {node} if args.transitive else set(edges[node])
        users = kg.reachable(reverse, [node]) - {node} if args.transitive else set(reverse.get(node, []))
        print(data["provenance"]["authority"])
        print(f"{node} ({data['modules'][node]['path']})")
        for label, nodes in (("Dependencies", imports), ("Importers", users)):
            print(f"\n{label}: {len(nodes)}")
            for other in sorted(nodes):
                print(f"  {data['modules'][other]['path']}")
        print(f"\nExternal imports: {', '.join(data['modules'][node]['external_imports']) or 'none'}")
        if args.dot:
            write_dot(args.dot, data, imports | users | {node})
        return 0
    except (ValueError, re.error) as exc:
        parser.error(str(exc))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
