#!/usr/bin/env python3
"""Restore only the frozen project's import closure needed for Stage 1.

Use the frozen mirror's original manifest validator, source checks,
SHA-256-checked downloader and archive extraction mapping. Do not build
Main, recompile the original proof, change its pinned files, or fabricate
any missing dependency. The command-line Lean import is the ultimate
check that the conservative source closure is complete.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import urllib.request

GIB = 1024 ** 3
BATCH = 512
# The frozen submission uses ordinary one-line import commands. Recognize
# module-system modifiers too; fail closed on an unrecognized import name.
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.*)$", re.M)
EXCLUDED_ROOTS = {
    "Main",
    "Challenge",
    "Supplements.Kernels.MainTheorems",
    "Supplements.Kernels.MainTheoremsAll",
    "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion",
    "Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter",
}


def load_pins(upstream):
    spec = importlib.util.spec_from_file_location(
        "rh_frozen_pins", upstream / "scripts/restore-cache.py")
    pins = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pins)
    pins.check_project(upstream)
    return pins


def imports(text, name_pattern):
    """Conservatively include every literal import directive in a source.

    Frozen sources have no generated import commands. An apparent import
    in a comment is harmless over-inclusion, not an excuse to skip a real
    import. Validate every token; Lean itself must load the completed
    closure successfully before the job can pass.
    """
    result = []
    for match in IMPORT.finditer(text):
        body = match.group(1).split("--", 1)[0].strip()
        for word in body.split():
            if word == "all":
                continue
            if not name_pattern.fullmatch(word):
                raise ValueError(f"Unrecognized frozen import: {word!r}")
            result.append(word)
    return result


def closure(upstream, template, pins, rows):
    table = {row[0]: row for row in rows}
    roots = imports(template.read_text(), pins.MODULE)
    if EXCLUDED_ROOTS.intersection(roots):
        raise ValueError("Stage 1 directly imports an excluded terminal module")
    todo, seen, project, external = list(roots), set(), set(), set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        file = upstream / "src" / Path(*name.split(".")).with_suffix(".lean")
        if name not in table:
            if file.exists():
                raise ValueError(f"Frozen project dependency absent from manifest: {name}")
            external.add(name)
            continue
        if not file.is_file():
            raise ValueError(f"Pinned project dependency lacks source: {name}")
        project.add(name)
        todo.extend(imports(file.read_text(), pins.MODULE))
    selected = [row for row in rows if row[0] in project]
    if not selected:
        raise ValueError("Empty upstream dependency closure")
    # The actual proof-term dependency audit in ClosedRH.lean is unchanged.
    # Some mixed supplier/consumer modules may be imported transitively.
    return selected, roots, sorted(external), sorted(EXCLUDED_ROOTS & project)


def read_manifest(pins, cache):
    path = cache / "stage1-modules.jsonl.gz"
    if not path.is_file():
        request = urllib.request.Request(
            pins.URL, headers={"User-Agent": "RHLean-Stage1/1.0"})
        with urllib.request.urlopen(request, timeout=120) as response:
            contents = response.read()
        pins.manifest_rows(contents)
        tmp = path.with_suffix(".tmp")
        tmp.write_bytes(contents)
        tmp.replace(path)
    return pins.manifest_rows(path.read_bytes())


def fetch(upstream, cache, rows):
    mapping = cache / "stage1-outputs.jsonl"
    digests = cache / "stage1-sha256.json"
    mapping.write_text(json.dumps("2026-03-17") + "\n" + "".join(
        json.dumps([dep, archive]) + "\n" for _, dep, archive, _ in rows))
    digests.write_text(json.dumps({archive: sha for _, _, archive, sha in rows}))
    subprocess.run([
        sys.executable, "-I",
        str(upstream / "scripts/rh-buildq/fetch-artifacts.py"),
        str(mapping), str(cache), "--sha256", str(digests),
        "--verify-existing",
        "--base-url",
        "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/",
        "--user-agent", "RHLean-Stage1/1.0",
    ], cwd=upstream, check=True)


def disk(upstream, phase, minimum=3 * GIB):
    free = shutil.disk_usage(upstream).free
    print(f"STAGE1_DISK {phase}: {free / GIB:.2f} GiB free", flush=True)
    if free < minimum:
        raise OSError(
            f"Insufficient space during {phase}; {free / GIB:.2f} GiB remains. "
            "Use a larger authorized runner; proof checks cannot be skipped.")


def remove_build_extras(upstream, rows):
    # These are generated by the pinned cache restore, not proof objects.
    # Keep every .olean variant, IR signature, and compiled Lean IR.
    # Command-line 'lean -o' does not need editor .ilean indexes or C
    # sources; there is no Lake native-code build in this replay.
    build = upstream / ".lake/build"
    for name, *_ in rows:
        rel = Path(*name.split("."))
        for path in (
            build / "lib/lean" / rel.with_suffix(".ilean"),
            build / "ir" / rel.with_suffix(".c"),
        ):
            if path.is_symlink():
                raise ValueError(f"Unexpected symlink in generated output: {path}")
            path.unlink(missing_ok=True)


def restore(upstream, cache, pins, rows):
    env = os.environ.copy()
    for key in list(env):
        if key.startswith(("AWS_", "CLOUDFLARE_", "CF_")) or key == "LAKE_CACHE_KEY":
            env.pop(key)
    env["ELAN_TOOLCHAIN"] = pins.HEADER["toolchain"]
    env["RUST_MIN_STACK"] = str(max(int(env.get("RUST_MIN_STACK", "0")), 8388608))
    lean = Path(subprocess.check_output(
        ["elan", "which", "lean"], cwd=upstream, env=env, text=True).strip())
    leantar = str(lean.with_name("leantar"))
    count = len(rows)
    for start in range(0, count, BATCH):
        disk(upstream, f"before batch {start // BATCH + 1}")
        batch = rows[start:start+BATCH]
        # Original checks on every compressed archive and output path.
        jobs = pins.restore_jobs(upstream, cache, batch)
        for base in dict.fromkeys(base for job in jobs for base in job["base"]):
            Path(base).mkdir(parents=True, exist_ok=True)
        pins.clear_output_hashes(upstream, batch)
        subprocess.run(
            [leantar, "--jobs", "4", "-f", "-x", "-j", "-"],
            input=json.dumps(jobs), text=True, cwd=upstream, env=env, check=True)
        remove_build_extras(upstream, batch)
        # After verifying and unpacking, ensure all selected proof files
        # actually exist. Archive cache is retained for subsequent jobs.
        for name, *_ in batch:
            obj = upstream / ".lake/build/lib/lean" / Path(*name.split(".")).with_suffix(".olean")
            if not obj.is_file() or not obj.stat().st_size:
                raise ValueError(f"Missing restored proof object: {name}")
        print(f"STAGE1_RESTORED {min(start+BATCH,count)}/{count}", flush=True)
    disk(upstream, "import closure restored")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["fetch", "restore"])
    parser.add_argument("upstream", type=Path)
    parser.add_argument("template", type=Path)
    parser.add_argument("--report", required=True, type=Path)
    args = parser.parse_args()
    upstream, template = args.upstream.resolve(), args.template.resolve()
    cache = upstream / ".lake/cache"
    cache.mkdir(parents=True, exist_ok=True)
    pins = load_pins(upstream)
    rows = read_manifest(pins, cache)
    selected, roots, external, mixed = closure(upstream, template, pins, rows)
    report = {
        "frozen_manifest_modules": len(rows),
        "selected_project_modules": len(selected),
        "omitted_project_modules": len(rows)-len(selected),
        "direct_imports": roots,
        "external_imports": external,
        "transitively_imported_terminal_named_modules": mixed,
        "selected_modules": [row[0] for row in selected],
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("STAGE1_IMPORT_CLOSURE " + json.dumps({
        k: v for k,v in report.items() if k != "selected_modules"
    }), flush=True)
    if args.phase == "fetch":
        fetch(upstream, cache, selected)
        disk(upstream, "verified compressed closure downloaded")
    else:
        restore(upstream, cache, pins, selected)


if __name__ == "__main__":
    main()
