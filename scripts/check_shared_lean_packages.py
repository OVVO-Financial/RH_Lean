#!/usr/bin/env python3
"""Check that two Lake workspaces share identical sources for given packages.

The combined RH_Lean + OpenAI kernel checks put both workspaces on one
LEAN_PATH. Lean loads every module of a package from the first search-path
entry that contains it, so a package present in both workspaces is only
sound to share when both were built from the same sources. For each named
package this requires the same commit in both checkouts and no local change
in either (Lake's own `.lake/` build directory aside).

Usage: check_shared_lean_packages.py WORKSPACE_A WORKSPACE_B PACKAGE...
"""
import subprocess
import sys
from pathlib import Path


def git(directory, *args):
    result = subprocess.run(["git", "-C", str(directory), *args],
                            capture_output=True, text=True)
    if result.returncode != 0:
        raise SystemExit(f"{directory}: git {' '.join(args)} failed:\n{result.stderr}")
    return result.stdout


def source_state(workspace, package):
    directory = Path(workspace).resolve() / ".lake" / "packages" / package
    head = git(directory, "rev-parse", "HEAD").strip()
    changes = [line for line in
               git(directory, "status", "--porcelain", "--untracked-files=all").splitlines()
               if not line[3:].startswith(".lake/")]
    if changes:
        raise SystemExit(f"{directory}: local changes to a shared package:\n" + "\n".join(changes))
    return head


def main():
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    first, second, *packages = sys.argv[1:]
    for package in packages:
        a, b = source_state(first, package), source_state(second, package)
        if a != b:
            raise SystemExit(f"{package}: {first} has {a}, {second} has {b}")
        print(f"{package}: identical unmodified sources at {a} in both workspaces")


if __name__ == "__main__":
    main()
