#!/usr/bin/env python3
"""Compile the transitive research.* import closure of one Lean source file.

Research modules are intentionally outside the RHLean lean_lib, so plain
`lake build RHLean` does not emit their .olean files.  CI workflows historically
listed these research files by hand.  This helper follows only explicit
`research.*` imports, compiles them in postorder, and writes the same module
names under .lake/build/lib/lean.

Non-research imports are left to Lake; callers should build RHLean first.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / ".lake" / "build" / "lib" / "lean"

QUOTED = re.compile(r"«(research\.[^»]+)»")
PLAIN = re.compile(r"\b(research\.[A-Za-z0-9_'.]+)\b")


def source_for(module: str) -> Path:
    if not module.startswith("research."):
        raise ValueError(module)
    rel = module.removeprefix("research.").replace(".", "/") + ".lean"
    return ROOT / "research" / rel


def module_for_source(path: Path) -> str:
    rel = path.resolve().relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def research_imports(path: Path) -> list[str]:
    found: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip()
        if not stripped.startswith("import "):
            continue
        for module in QUOTED.findall(line):
            if module not in found:
                found.append(module)
        scrubbed = QUOTED.sub("", line)
        for module in PLAIN.findall(scrubbed):
            if module not in found:
                found.append(module)
    return found


visiting: set[str] = set()
done: set[str] = set()


def compile_module(module: str) -> None:
    if module in done:
        return
    if module in visiting:
        raise RuntimeError(f"research import cycle at {module}")

    src = source_for(module)
    if not src.exists():
        raise FileNotFoundError(f"{module}: expected {src.relative_to(ROOT)}")

    visiting.add(module)
    for dep in research_imports(src):
        compile_module(dep)
    visiting.remove(module)

    out = BUILD / (module + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)

    # A prior step in the same job may already have emitted this module.
    # Git checkout refreshes source mtimes, so restored-cache oleans do not
    # accidentally pass this freshness check.
    if out.exists() and out.stat().st_mtime >= src.stat().st_mtime:
        print(f"[research-closure] fresh {module}", flush=True)
    else:
        print(f"[research-closure] emit  {module}", flush=True)
        subprocess.run(
            [
                "lake",
                "env",
                "lean",
                "-DwarningAsError=true",
                "-o",
                str(out),
                str(src),
            ],
            cwd=ROOT,
            check=True,
        )
    done.add(module)


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(
            "usage: compile_research_import_closure.py research/TARGET.lean"
        )
    target = (ROOT / sys.argv[1]).resolve()
    if not target.exists():
        raise SystemExit(f"target not found: {target}")
    compile_module(module_for_source(target))


if __name__ == "__main__":
    main()
