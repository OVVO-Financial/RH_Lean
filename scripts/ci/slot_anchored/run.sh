#!/usr/bin/env bash
# Run only in the configured pinned proof CI environment, after baseline checks.
set -euo pipefail
bundle_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="${1:?usage: run.sh /path/to/RH_Lean}"
cd "$repo"
source_pin=9cbfce5295343bcb411e6d2cb159b59995cd985b
if ! git cat-file -e "$source_pin^{commit}" 2>/dev/null; then
  git fetch --no-tags --depth=1 origin "$source_pin"
fi
python3 "$bundle_dir/prepare_anchored.py" "$PWD"
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
mkdir -p .lake/build/lib/lean
log=slot-anchored-lean.log
: > "$log"
targets=(
 VF919PhysicalTiltFullBudget
 VF919SlotCalibratedData
 VF919AnchoredSmallTail
 VF919AnchoredPrincipalRemainder
 VF919AnchoredHighPrincipal
 VF919AnchoredHighTails
 VF919AnchoredHighTransport
 VF919AnchoredHighAssembly
 VF919SlotAnchoredEndpoint
 VF919SlotAnchoredConsequences
)
failed=0
for name in "${targets[@]}"; do
  echo "Checking $name" | tee -a "$log"
  if ! env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/research.oai_434.${name}.olean" \
    "research/oai_434/${name}.lean" 2>&1 | tee -a "$log"; then
    failed=1
  fi
done
if (( failed )); then
  echo 'At least one slot-anchored proof target failed. No endpoint is accepted.' >&2
  exit 1
fi
if grep -E 'sorryAx|admitAx' "$log"; then
  echo 'Rejected: admitted proof dependency' >&2
  exit 1
fi
for target in hecke mertens; do
  env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
    --run "$bundle_dir/SlotAnchoredAudit.lean" "$target" \
    2>&1 | tee "slot-anchored-audit-$target.log"
done
echo 'Compilation and endpoint audits passed; independent mathematical review remains separate.'
