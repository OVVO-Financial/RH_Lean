#!/usr/bin/env python3
"""Apply the pinned OpenAI Lean 4.34.1 dependency patches exactly as upstream does.

`openai/math` ships `lean/patches/<package>-lean4341.patch` for every
third-party dependency that needs Lean 4.34.1 compatibility changes. Its
lakefile applies eleven of them during configuration elaboration, but the
remaining twelve (including rellich-kondrachov, PrimeNumberTheoremAnd and
StrongPNT) are applied only by its `post_update` hook, which runs on
`lake update` and never on `lake exe cache get`. A CI checkout that only
fetches the Mathlib cache therefore builds those dependencies unpatched.

This script reproduces that `post_update` hook: for each package it checks
the checkout against the commit pinned in `lake-manifest.json`,
skips a patch that is already applied, applies it otherwise, and verifies
the result. Any mismatch or conflict is fatal. The patches are upstream's
own files; nothing here edits proofs.

`--keep-pinned PKG` leaves PKG exactly at its pinned upstream commit and
fails if its checkout has any local change. The combined RH_Lean + OpenAI
kernel checks use it for PrimeNumberTheoremAnd: RH_Lean pins the same
commit unpatched, and Lean loads a package from a single build, so both
sides must be compiled against identical PrimeNumberTheoremAnd sources.
"""
import argparse
import json
import subprocess
from pathlib import Path

# The package list of the `post_update` hook in openai/math lean/lakefile.lean.
POST_UPDATE_PACKAGES = [
    "fixed-point-theorems", "PrimeNumberTheoremAnd", "Zeta3Irrational",
    "rellich-kondrachov", "carleson", "StrongPNT", "AbsorptionCutoff", "AINTLIB",
    "ClassFieldTheory", "schoenflies-lean", "SphereEversion", "gromov",
]


def git(directory, *args):
    return subprocess.run(["git", "-C", str(directory), *args],
                          capture_output=True, text=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default="oai-upstream/lean")
    parser.add_argument("--keep-pinned", action="append", default=[],
                        choices=POST_UPDATE_PACKAGES, metavar="PKG")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    manifest = json.loads((root / "lake-manifest.json").read_text())
    pins = {p["name"].strip("«»"): p for p in manifest["packages"]}
    for label in POST_UPDATE_PACKAGES:
        pin = pins[label]
        directory = root / ".lake" / "packages" / label
        patch = root / "patches" / f"{label}-lean4341.patch"
        if not patch.is_file():
            raise SystemExit(f"{label}: missing upstream patch {patch}")
        head = git(directory, "rev-parse", "HEAD").stdout.strip()
        if head != pin["rev"]:
            raise SystemExit(f"{label}: expected commit {pin['rev']}, found {head!r}")
        if label in args.keep_pinned:
            status = git(directory, "status", "--porcelain", "--untracked-files=all")
            changes = [line for line in status.stdout.splitlines()
                       if not line[3:].startswith(".lake/")]
            if status.returncode != 0 or changes:
                raise SystemExit(f"{label}: must stay at pinned {pin['rev']} but has local changes:\n"
                                 + "\n".join(changes))
            print(f"{label}: kept unpatched at pinned commit {head}")
            continue
        if git(directory, "apply", "--check", "--reverse", str(patch)).returncode == 0:
            print(f"{label}: upstream patch already applied")
            continue
        forward = git(directory, "apply", "--check", str(patch))
        if forward.returncode != 0:
            raise SystemExit(f"{label}: upstream patch conflicts:\n{forward.stderr}")
        applied = git(directory, "apply", str(patch))
        if applied.returncode != 0:
            raise SystemExit(f"{label}: failed to apply upstream patch:\n{applied.stderr}")
        if git(directory, "apply", "--check", "--reverse", str(patch)).returncode != 0:
            raise SystemExit(f"{label}: upstream patch did not verify after applying")
        print(f"{label}: applied upstream patch {patch.name}")


if __name__ == "__main__":
    main()
