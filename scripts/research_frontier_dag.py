#!/usr/bin/env python3
"""Validate the current research map and extract its source import closure.

This uses repo_index provenance and project-scoped import edges. It supplies
navigation, not a compilation certificate or a proof of any open input.
"""

import argparse
import json
from pathlib import Path

import repo_index


def frontier(data, manifest):
    if manifest.get("schema") != "rhlean-research-frontier/1":
        raise ValueError("unsupported research-frontier schema")
    modules = data["modules"]
    current = {m["path"]: key for key, m in modules.items()
               if m["view"] == "worktree" and m["project"] == "."}
    files = {f["path"] for f in data["files"].values()
             if f["view"] == "worktree"}
    tracks = manifest["tracks"]
    prs = [track["pr"] for track in tracks]
    if len(prs) != len(set(prs)):
        raise ValueError("duplicate PR in research-frontier map")
    selected = set()
    for track in tracks:
        paths = track["modules"] + track["documents"]
        for path in paths:
            if path not in files:
                raise ValueError(f"PR #{track['pr']}: missing indexed source {path}")
        seeds = {current[path] for path in track["modules"]}
        names = {d["name"].split(".")[-1] for d in data["declarations"]
                 if d["module_id"] in seeds}
        for name in track["sentinels"]:
            if name not in names:
                raise ValueError(f"PR #{track['pr']}: lost declaration {name}")
        selected.update(seeds)
    pending = list(selected)
    while pending:
        for dependency in data["module_import_graph"][pending.pop()]:
            if dependency not in selected:
                selected.add(dependency)
                pending.append(dependency)
    if any(set(cycle) & selected for cycle in data["cyclic_components"]):
        raise ValueError("research-frontier import closure contains a cycle")
    return selected


def report(data, manifest, selected):
    view = next(v for v in data["provenance"]["views"]
                if v["view"] == "worktree")
    state = " (modified checkout)" if view["dirty"] else ""
    edges = sum(len(set(data["module_import_graph"][key]) & selected)
                for key in selected)
    lines = ["# Current research frontier import DAG", "",
             manifest["authority"], "",
             f"Source checkout: `{view['commit']}`{state}.",
             f"Validated {len(manifest['tracks'])} tracks; dependency closure: "
             f"{len(selected)} local modules, {edges} importer-to-dependency edges.",
             "External package imports are outside this local closure.", "",
             "| PR | Track | Route | Evidence scope | Open input |",
             "| --- | --- | --- | --- | --- |"]
    for track in manifest["tracks"]:
        link = f"https://github.com/OVVO-Financial/RH_Lean/pull/{track['pr']}"
        lines.append(f"| [#{track['pr']}]({link}) | {track['name']} | "
                     f"{track['route']} | {track['evidence']} | {track['open']} |")
    lines.extend(["", "## Source entry points", ""])
    for track in manifest["tracks"]:
        paths = track["modules"] + track["documents"]
        links = ", ".join(f"[{Path(path).name}]({path})" for path in paths)
        lines.append(f"- #{track['pr']}: {links}")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path,
                        default=repo_index.ROOT / "docs/research-frontier.json")
    parser.add_argument("--dot", type=Path, default=Path("research-frontier.dot"))
    parser.add_argument("--report", type=Path, default=Path("research-frontier.md"))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    data = repo_index.load_index(repo_index.ROOT, None, [])
    selected = frontier(data, manifest)
    repo_index.write_dot(args.dot, data, selected)
    text = report(data, manifest, selected)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
