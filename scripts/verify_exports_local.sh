#!/usr/bin/env bash
set -euo pipefail

# Strict pre-merge gate for every Lake project in this repository.
#
# scripts/local_ci.sh is the everyday command: it mirrors one project's hosted
# job. This script is the thing to run before merging, because it also closes
# the gaps that no single-project build can see:
#
#   * GitHub Desktop opens a terminal at the repository root, but each export
#     is a separate Lake project. A root build never compiles export-only
#     source, so the development tree can stay green while a published
#     repository fails on the source only it carries;
#   * agent commits pushed through GitHub can move the remote branch after
#     Desktop last fetched it, so a local build can validate an older head
#     than the one the pull request actually contains;
#   * stale .olean files can hide a proof that no longer elaborates from
#     source.
#
# It therefore pins the exact source surface before compiling anything:
#   1. require a clean tracked working tree;
#   2. fetch the current branch and require local HEAD = origin/<branch>;
#   3. verify development/export source synchronization;
#   4. delete every project's build products, preserving package caches;
#   5. run each project's own CI mirror, which restores that project's Mathlib
#      cache, audits its sources, rebuilds it from scratch and runs its axiom
#      gate;
#   6. recheck synchronization once everything has compiled.
#
# Expect this to take a while: step 4 means every project recompiles its whole
# library. That is the point.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# 'label=package directory relative to the repository root'
packages=(
  'development tree=.'
  'mobius-synthesis export=export_mobius_synthesis'
  'prime-wheel export=export_prime_wheel/formalization'
  'square-block export=export_square_block/lean'
)

step() { printf '\n==> %s\n' "$1"; }
fail() { printf 'ERROR: %s\n' "$1" >&2; exit 1; }

# Windows installs frequently expose `python` or the `py` launcher but no
# `python3`, so resolve whichever exists rather than hard-coding one.
python_bin=''
for candidate in python3 python py; do
  if command -v "$candidate" >/dev/null 2>&1; then python_bin="$candidate"; break; fi
done
[[ -n "$python_bin" ]] || fail 'no Python interpreter on PATH (tried python3, python, py).'

if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
  fail 'tracked working-tree changes are present.
Commit or discard them before using this command as merge validation.'
fi

current_branch="$(git symbolic-ref --quiet --short HEAD || true)"
if [[ -z "$current_branch" ]]; then
  fail 'detached HEAD. Check out the PR branch in GitHub Desktop first.'
fi

step "Fetching origin/$current_branch"
git fetch origin "$current_branch"
local_sha="$(git rev-parse HEAD)"
remote_sha="$(git rev-parse "origin/$current_branch")"
if [[ "$local_sha" != "$remote_sha" ]]; then
  fail "local checkout is not at the remote branch head.
local : $local_sha
remote: $remote_sha
Pull the latest branch in GitHub Desktop, then rerun this verifier."
fi

step 'Verifying export synchronization'
"$python_bin" scripts/check_export_sync.py

step 'Removing build products to prevent stale .olean reuse'
# Only .lake/build is removed. Downloaded packages under .lake/packages, which
# include the Mathlib each project has already fetched, are preserved.
for entry in "${packages[@]}"; do
  dir="${entry#*=}"
  rm -rf "${repo_root:?}/$dir/.lake/build"
done

for entry in "${packages[@]}"; do
  label="${entry%%=*}"
  dir="${entry#*=}"
  step "Running the CI mirror for the $label ($dir)"
  (
    cd "$repo_root/$dir"
    bash scripts/local_ci.sh
  )
done

step 'Rechecking export synchronization after every build'
cd "$repo_root"
"$python_bin" scripts/check_export_sync.py

printf '\nAll four Lake projects passed their own CI mirror.\n'
