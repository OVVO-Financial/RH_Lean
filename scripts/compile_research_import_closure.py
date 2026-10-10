#!/usr/bin/env python3
"""Warning-fatal, content-addressed compilation of research import closures.

Research modules live outside lean_lib RHLean. Keep their historical dotted
output names, but reuse an olean only when its source, transitive research
imports, library sources, compiler configuration and output digest agree.
Checkout timestamps are deliberately irrelevant. A cache is compilation
reuse, not a substitute for the workflow's theorem/axiom acceptance checks.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

# Some existing workflows load this file with importlib from the repo root.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from repo_index import imports_from

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / ".lake" / "build" / "lib" / "lean"
SCHEMA = "rhlean-research-closure/2"
FLAGS = ["-DwarningAsError=true"]


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


PRODUCERS = [(p.name, digest(p.read_bytes())) for p in
             [Path(__file__), Path(__file__).with_name('repo_index.py'),
              Path(__file__).with_name('rhlean_kg.py')]]


def source_for(module: str, root: Path = ROOT) -> Path:
    if not module.startswith("research.") or any(
        part in {"", ".", ".."} for part in module.split(".")
    ) or "/" in module or "\\" in module:
        raise ValueError(f"invalid research module: {module}")
    return root / (module.replace(".", "/") + ".lean")


def module_for_source(path: Path, root: Path = ROOT) -> str:
    rel = path.resolve().relative_to(root.resolve())
    if rel.suffix != ".lean" or rel.parts[0] != "research":
        raise ValueError(f"expected a research/*.lean source: {path}")
    return ".".join(rel.with_suffix("").parts)


def research_imports(path: Path) -> list[str]:
    return [module for module in imports_from(path.read_text(encoding="utf-8"))
            if module.startswith("research.")]


def environment_key(root: Path) -> str:
    # Native definitions can change many imports away from a research target.
    # Include the full native surface; Lake checks/builds it separately.
    paths = {
        root / name for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json", "RHLean.lean")
    }
    paths.update((root / "RHLean").rglob("*.lean"))
    paths.update((root / "scripts" / "strongpnt_424").glob("*.py"))
    rows = [SCHEMA, FLAGS, PRODUCERS]
    rows.append([(p.relative_to(root).as_posix(), digest(p.read_bytes()) if p.is_file() else None)
                 for p in sorted(paths)])
    return digest(json.dumps(rows, sort_keys=True).encode())


def affected(plan: dict, changed: list[str]) -> bool:
    sources = {entry['source'] for entry in plan['modules']}
    return any(path in sources or path in {'RHLean.lean', 'lakefile.lean',
               'lake-manifest.json', 'lean-toolchain'}
               or path.startswith(('RHLean/', '.github/', 'scripts/'))
               for path in changed)


class Closure:
    def __init__(self, root: Path = ROOT, build: Path | None = None):
        self.root = root.resolve()
        self.build = build or self.root / ".lake" / "build" / "lib" / "lean"
        self.environment = environment_key(self.root)
        self.modules: dict[str, dict] = {}
        self.library: set[str] = set()
        self.visiting: set[str] = set()

    def visit(self, module: str) -> dict:
        if module in self.modules:
            return self.modules[module]
        if module in self.visiting:
            raise ValueError(f"research import cycle at {module}")
        source = source_for(module, self.root)
        raw = source.read_bytes()
        imports = imports_from(raw.decode("utf-8"))
        self.visiting.add(module)
        dependencies = [self.visit(dep) for dep in imports if dep.startswith("research.")]
        self.visiting.remove(module)
        self.library.update(dep for dep in imports if dep == "RHLean" or dep.startswith("RHLean."))
        key = digest(json.dumps([self.environment, module, digest(raw),
                                 [(d["module"], d["key"]) for d in dependencies]]).encode())
        entry = {"module": module, "source": source.relative_to(self.root).as_posix(),
                 "source-hash": digest(raw), "key": key}
        self.modules[module] = entry  # insertion order is dependency-first
        return entry

    def plan(self, targets: list[Path]) -> dict:
        roots = sorted({module_for_source(path, self.root) for path in targets})
        for module in roots:
            self.visit(module)
        return {"schema": SCHEMA, "environment": self.environment, "targets": roots,
                "library": sorted(self.library), "modules": list(self.modules.values())}

    def compile(self, force: bool = False) -> tuple[int, int]:
        emitted = cached = 0
        if environment_key(self.root) != self.environment:
            raise RuntimeError('compiler environment changed after planning; rerun')
        for module, entry in self.modules.items():
            source = self.root / entry["source"]
            out = self.build / (module + ".olean")
            record = self.build / (module + ".olean.json")
            if digest(source.read_bytes()) != entry['source-hash']:
                raise RuntimeError(f'{module}: source changed after planning; rerun')
            try:
                previous = json.loads(record.read_text(encoding="utf-8"))
                fresh = (previous.get("schema") == SCHEMA and previous.get("key") == entry["key"]
                         and previous.get("olean") == digest(out.read_bytes()))
            except (OSError, ValueError, AttributeError):
                fresh = False
            if fresh and not force:
                print(f"[research-closure] cached {module}", flush=True)
                cached += 1
                continue
            print(f"[research-closure] emit   {module}", flush=True)
            out.parent.mkdir(parents=True, exist_ok=True)
            record.unlink(missing_ok=True)
            try:
                subprocess.run(["lake", "env", "lean", *FLAGS, "-o", str(out), str(source)],
                               cwd=self.root, check=True)
                if digest(source.read_bytes()) != entry['source-hash']:
                    raise RuntimeError(f'{module}: source changed during compilation; rerun')
            except BaseException:
                out.unlink(missing_ok=True)
                raise
            metadata = {"schema": SCHEMA, "key": entry["key"], "olean": digest(out.read_bytes())}
            temporary = record.with_suffix(".json.tmp")
            temporary.write_text(json.dumps(metadata, sort_keys=True) + "\n", encoding="utf-8")
            temporary.replace(record)
            emitted += 1
        if environment_key(self.root) != self.environment:
            for module in self.modules:
                (self.build / (module + '.olean.json')).unlink(missing_ok=True)
            raise RuntimeError('compiler environment changed during compilation; rerun')
        print(f"[research-closure] compiled={emitted} cached={cached}", flush=True)
        return emitted, cached


def compile_module(module: str) -> None:
    # Kept for workflows which import this helper directly.
    closure = Closure(ROOT, BUILD)
    closure.visit(module)
    closure.compile()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", help="research/*.lean files (multiple roots share one traversal)")
    parser.add_argument("--plan", type=Path, help="write a dependency/cache plan without running Lean")
    parser.add_argument("--build-library", action="store_true", help="ask Lake to build the imported RHLean targets first")
    parser.add_argument("--force", action="store_true", help="compile every module, ignoring verified cache records")
    parser.add_argument("--affected-files", type=Path, help="classify a newline-separated changed-file list without running Lean")
    args = parser.parse_args()
    # Action inputs are data, never interpolated into shell code.
    targets = args.targets or os.environ.get("RHLEAN_RESEARCH_TARGETS", "").split()
    if not targets:
        parser.error("provide at least one research/*.lean target")
    closure = Closure()
    plan = closure.plan([(ROOT / target).resolve() for target in targets])
    if args.affected_files:
        changed = args.affected_files.read_text(encoding='utf-8').splitlines()
        value = 'true' if affected(plan, changed) else 'false'
        if output := os.environ.get('GITHUB_OUTPUT'):
            with open(output, 'a', encoding='utf-8') as stream:
                stream.write(f'affected={value}\n')
        print(f'[research-closure] affected={value}, {len(plan["modules"])} closure sources')
        return
    if args.plan:
        args.plan.write_text(json.dumps(plan, sort_keys=True) + "\n", encoding="utf-8")
        if output := os.environ.get("GITHUB_OUTPUT"):
            with open(output, "a", encoding="utf-8") as stream:
                stream.write(f"target-key={digest(json.dumps(plan['targets']).encode())}\n")
                stream.write(f"environment-key={plan['environment']}\n")
                stream.write(f"plan-key={digest(json.dumps(plan, sort_keys=True).encode())}\n")
        print(f"[research-closure] planned {len(plan['modules'])} modules, {len(plan['library'])} library targets")
        return
    if args.build_library and plan["library"]:
        subprocess.run(["lake", "build", *plan["library"]], cwd=ROOT, check=True)
    closure.compile(force=args.force)


if __name__ == "__main__":
    main()
