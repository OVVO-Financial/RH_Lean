#!/usr/bin/env bash
set -euo pipefail

# Authoritative local verification for changes that touch the mobius-synthesis
# development tree or export.  GitHub Desktop opens terminals at the repository
# root, while export_mobius_synthesis is a separate Lake project.  A bare
# `lake build RHLean --wfail` from the root therefore does not verify the export
# unless the export module also exists in the development tree.
#
# This script makes the distinction impossible to miss:
#   1. verify development/export source synchronization;
#   2. remove only project build products, preserving downloaded package caches;
#   3. build the development library from scratch;
#   4. build the standalone mobius-synthesis export from scratch.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export_root="$repo_root/export_mobius_synthesis"

cd "$repo_root"

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
