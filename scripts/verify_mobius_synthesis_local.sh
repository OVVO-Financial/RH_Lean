#!/usr/bin/env bash
set -euo pipefail

# Authoritative local verification for changes that touch the mobius-synthesis
# development tree or export. GitHub Desktop opens terminals at the repository
# root, while export_mobius_synthesis is a separate Lake project. Agent commits
# may also move the remote branch after Desktop last fetched it.
#
# This script therefore verifies the exact source surface before compiling:
#   1. require a clean tracked working tree;
#   2. fetch the current branch and require local HEAD = origin/<branch>;
#   3. verify development/export source synchronization;
#   4. remove only project build products, preserving downloaded package caches;
#   5. build the development library from scratch;
#   6. build the standalone mobius-synthesis export from scratch.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export_root="$repo_root/export_mobius_synthesis"

cd "$repo_root"

if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
  echo 'ERROR: tracked working-tree changes are present.' >&2
  echo 'Commit or discard them before using this command as merge validation.' >&2
  exit 1
fi

current_branch="$(git symbolic-ref --quiet --short HEAD || true)"
if [[ -z "$current_branch" ]]; then
  echo 'ERROR: detached HEAD. Check out the PR branch in GitHub Desktop first.' >&2
  exit 1
fi

echo "==> Fetching origin/$current_branch"
git fetch origin "$current_branch"
local_sha="$(git rev-parse HEAD)"
remote_sha="$(git rev-parse "origin/$current_branch")"
if [[ "$local_sha" != "$remote_sha" ]]; then
  echo 'ERROR: local GitHub Desktop checkout is not at the remote branch head.' >&2
  echo "local : $local_sha" >&2
  echo "remote: $remote_sha" >&2
  echo 'Pull the latest branch in GitHub Desktop, then rerun this verifier.' >&2
  exit 1
fi

echo '==> Verifying mobius-synthesis export synchronization'
python3 scripts/check_export_sync.py

echo '==> Removing local RHLean build products to prevent stale .olean reuse'
rm -rf "$repo_root/.lake/build" "$export_root/.lake/build"

echo '==> Auditing development sources'
bash scripts/audit_assumptions.sh

echo '==> Fresh-building development RHLean'
lake build RHLean --wfail

echo '==> Auditing standalone mobius-synthesis export sources'
(
  cd "$export_root"
  bash scripts/audit_assumptions.sh
)

echo '==> Fresh-building standalone mobius-synthesis RHLean'
(
  cd "$export_root"
  lake build RHLean --wfail
)

echo '==> Rechecking export synchronization after both builds'
cd "$repo_root"
python3 scripts/check_export_sync.py

echo 'mobius-synthesis local verification passed.'
