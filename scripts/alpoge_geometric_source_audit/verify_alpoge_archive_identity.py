#!/usr/bin/env python3
"""Compare the original release archive to every tracked source Git blob.

The comparison reads tar members without extracting them and never runs Lean.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    head = subprocess.check_output(["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip()
    if head != manifest["upstream"]["commit"]:
        raise SystemExit("Source HEAD differs from the manifest pin")
    with args.archive.open("rb") as handle:
        digest = hashlib.file_digest(handle, "sha256").hexdigest()
    provenance = manifest["provenance"]
    if digest != provenance["original_archive_sha256"] or args.archive.stat().st_size != provenance["original_archive_bytes"]:
        raise SystemExit("Original archive identity mismatch")
    raw = subprocess.check_output(["git", "-C", str(args.source), "ls-tree", "-r", "-z", "HEAD"])
    blobs = {}
    for item in raw.split(b"\0"):
        if item:
            meta, path = item.split(b"\t", 1)
            _mode, kind, blob = meta.split()
            if kind == b"blob":
                blobs[path.decode()] = blob.decode()
    seen, extra, different, configs = set(), [], [], []
    with tarfile.open(args.archive, "r|gz") as archive:
        for member in archive:
            if not member.isfile():
                continue
            name = member.name.removeprefix("./").removeprefix("lean/")
            if name in blobs:
                data = archive.extractfile(member).read()
                actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                seen.add(name)
                if actual != blobs[name]:
                    different.append({"path": name, "expected": blobs[name], "actual": actual})
                if not (name.startswith("src/") and name.endswith(".lean")):
                    configs.append(name)
            elif name.startswith("src/") and name.endswith(".lean"):
                extra.append(name)
    lean = {name for name in blobs if name.startswith("src/") and name.endswith(".lean")}
    missing = sorted(lean - seen)
    required_configs = {"lake-manifest.json", "lakefile.toml", "lean-toolchain"}
    missing_configs = sorted(required_configs - set(configs))
    report = {"upstream_git_commit": head,
              "archive_url": "https://github.com/CocoSgt/riemann-hypothesis-lean/releases/download/v2026-11-20/lean.tar.gz",
              "archive_size": args.archive.stat().st_size, "archive_sha256": digest,
              "lean_source_files_compared": len(lean.intersection(seen)),
              "tracked_lean_count": len(lean), "tracked_lean_missing_from_archive": missing,
              "archive_lean_missing_from_git": extra, "different_blob_hashes": different,
              "other_tracked_files_compared": sorted(configs), "missing_build_configs": missing_configs,
              "scope": "Byte identity only. No Lean execution."}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if missing or extra or different or missing_configs:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
