#!/usr/bin/env bash
set -euo pipefail

# Local mirror of the hosted jobs for the RH_Lean development project.
#
# Run this instead of a bare `lake build RHLean --wfail`. A bare build skips
# four things the hosted jobs do, and each one has produced a green local run
# against a red hosted run:
#
#   * the Mathlib build cache, so a fresh clone silently starts compiling
#     Mathlib from source instead of downloading it;
#   * the source audits, which reject unfinished proofs, project-local axioms
#     and paper/Analysis boundary violations that compile perfectly well;
#   * the export sync audit, which catches a module that exists in an export
#     but not in the development tree. A root build never compiles that
#     module, so the development project stays green while the published
#     repository fails on the source only it carries;
#   * the root import manifest check, which catches a new module that is on
#     disk but missing from RHLean.lean, and so is never compiled at all.
#
# The steps below are the same commands, in the same order, as
# .github/workflows/lean.yml plus the sync audit from
# .github/workflows/export.yml.
#
# This covers the development project only. To also compile the three exports
# as their own Lake projects, which is what the published repositories build,
# use scripts/verify_mobius_synthesis_local.sh or run
# `bash scripts/local_ci.sh` inside each export package directory.
#
# Usage, from anywhere inside the repository:
#
#     bash scripts/local_ci.sh

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lean_lib='RHLean'
root_manifest='RHLean.lean'

step() { printf '\n==> %s\n' "$1"; }
fail() { printf 'ERROR: %s\n' "$1" >&2; exit 1; }

# Fail on a missing toolchain with the real reason. Otherwise `lake` returning
# 127 is reported below as a cache-download failure, which sends you looking at
# the network instead of at PATH.
command -v lake >/dev/null 2>&1 || fail 'lake is not on PATH.
Install elan (https://github.com/leanprover/elan) and reopen the terminal.
On Windows, use the Git Bash that ships with Git for Windows.'

# Windows installs frequently expose `python` or the `py` launcher but no
# `python3`, so resolve whichever exists rather than hard-coding one.
python_bin=''
for candidate in python3 python py; do
  if command -v "$candidate" >/dev/null 2>&1; then python_bin="$candidate"; break; fi
done
[[ -n "$python_bin" ]] || fail 'no Python interpreter on PATH (tried python3, python, py).'

step 'Checking the paper / Analysis boundary'
bash scripts/check_paper_analysis_boundary.sh

step 'Auditing unfinished proofs and axioms'
bash scripts/audit_assumptions.sh

step 'Verifying every export closes and matches the development tree'
"$python_bin" scripts/check_export_sync.py

step 'Restoring the Mathlib build cache'
# CI gets this from lean-action's use-mathlib-cache. Locally nothing supplies
# it, and without it `lake build` compiles Mathlib from source: hours, not
# minutes. Stop rather than start that by accident.
if ! lake exe cache get; then
  fail 'could not restore the Mathlib build cache.
Continuing would compile Mathlib from source, which takes hours.
Restore connectivity to the Mathlib cache and rerun.'
fi

step "Regenerating the Lean root import manifest ($root_manifest)"
# mk_all rewrites the manifest in place. CI then fails if that rewrite changed
# anything, because a module missing from the manifest is a module nothing
# compiles. Locally the rewrite is the fix, so leave it on disk to be reviewed
# and committed rather than reverting it.
lake exe mk_all
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  if ! git diff --quiet -- "$root_manifest"; then
    git --no-pager diff -- "$root_manifest"
    fail "$root_manifest was stale and has been regenerated in place.
Review the diff above, commit it, then rerun this script."
  fi
else
  printf 'note: not a git checkout, so manifest staleness could not be checked.\n'
fi

step "Building $lean_lib with warnings fatal"
lake build "$lean_lib" --wfail

printf '\nLocal CI mirror passed for the development project.\n'
printf 'The three exports build as separate Lake projects and are not covered here.\n'
