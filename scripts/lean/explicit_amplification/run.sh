#!/usr/bin/env bash
# Lean execution is restricted to the authorized GitHub Actions workflow.
set -euo pipefail
bundle_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="${1:?usage: run.sh /path/to/RH_Lean}"
cd "$repo"

# Make the actual integer-source prerequisites explicit even on a cold cache.
lake build RHLean.Proof.SquareRootAmplificationLogGrowth RHLean.Proof.SquareRootAncestryRoot

# Reuse the complete endpoint proof and its original, unchanged dependency audit.
bash scripts/lean/total_mass/run.sh "$PWD"
python3 "$bundle_dir/check_inventory.py" "$PWD" | tee explicit-amplification-inventory.log
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
log=explicit-amplification-lean.log
: > "$log"

mkdir -p .lake/build/lib/lean/RHLean/Proof
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  -o .lake/build/lib/lean/RHLean/Proof/SquareRootAmplificationPowerBounds.olean \
  RHLean/Proof/SquareRootAmplificationPowerBounds.lean 2>&1 | tee -a "$log"

for name in VF919ExplicitFixedSourceSlotCount VF919ExplicitSlotTotalMass VF919ExplicitAmplificationBound VF919ExplicitSquareBlockPacking; do
  echo "Checking $name" | tee -a "$log"
  env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/research.oai_434.${name}.olean" \
    "research/oai_434/${name}.lean" 2>&1 | tee -a "$log"
done

env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  "$bundle_dir/SquarePackingTypes.lean" 2>&1 | tee -a "$log"

env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  "$bundle_dir/ExactTypes.lean" 2>&1 | tee -a "$log"
if grep -E 'sorryAx|admitAx' "$log"; then
  echo 'Rejected: admitted proof dependency' >&2
  exit 1
fi
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  --run "$bundle_dir/AmplificationAudit.lean" 2>&1 | tee explicit-amplification-audit.log
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  --run "$bundle_dir/SquarePackingAudit.lean" 2>&1 | tee square-packing-audit.log
echo 'Explicit finite-slot amplification and square-block packing: warning-fatal proof, exact types, and axiom audits passed.'
