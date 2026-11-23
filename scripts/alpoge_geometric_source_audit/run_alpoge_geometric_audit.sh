#!/usr/bin/env bash
# Fresh original-source verification in GitHub Actions only.  Native-port builds
# use RH_Lean's own toolchain/workflow and must be reported separately.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != "true" ]]; then
  echo "This runner executes Lean and is permitted only in GitHub Actions." >&2
  exit 2
fi
if [[ $# != 2 ]]; then
  echo "Usage: run_alpoge_geometric_audit.sh PINNED_SOURCE_CHECKOUT EMPTY_BUILD_DIRECTORY" >&2
  exit 2
fi

audit_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
upstream_source="$(cd -- "$1" && pwd)"
build_dir="$2"
manifest="$audit_dir/alpoge_geometric_closure_manifest.json"

python3 "$audit_dir/audit_alpoge_geometric_closure.py" \
  --source "$upstream_source" --manifest "$manifest" \
  --profile closed-short-constructor --report "$build_dir.static-source-report.json" \
  --export-source "$build_dir"

cd -- "$build_dir"
# This is Mathlib's dependency cache utility.  No project .olean cache is
# downloaded, copied, or reused; that is checked again before building.
lake exe cache get 2>&1 | tee dependency-cache.log
python3 - "$manifest" <<'PY'
from pathlib import Path
import hashlib
import json
import subprocess
import sys

own = list(Path('.lake/build').rglob('*.olean')) if Path('.lake/build').exists() else []
if own:
    raise SystemExit('Unexpected prebuilt project .olean files: ' + repr(own[:10]))
pin = json.loads(Path(sys.argv[1]).read_text())
data = Path('lake-manifest.json').read_bytes()
blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
if blob != pin['upstream']['config_git_blobs']['lake-manifest.json']:
    raise SystemExit('Pinned dependency manifest was modified')
manifest = json.loads(data)
for package in manifest['packages']:
    if package.get('type') != 'git':
        continue
    path = Path('.lake/packages') / package['name']
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit('Dependency revision mismatch: ' + package['name'])
print('Dependency revisions match; zero prebuilt project oleans.')
PY

# Explicit library: never defaultTargets, never Main, never the RH assembly.
lake build AlpogeGeometryAudit 2>&1 | tee fresh-source-build.log
lake env lean src/AlpogeGeometryAxiomGuard.lean 2>&1 | tee geometric-axiom-audit.log
python3 "$audit_dir/verify_alpoge_axiom_log.py" \
  --manifest "$manifest" --log geometric-axiom-audit.log --report geometric-axiom-report.json

printf '%s\n' 'Selected original source closure compiled and all seven axiom receipts passed.'
