#!/usr/bin/env bash
# The repository permits Lean execution only in authorized GitHub Actions.
set -euo pipefail
bundle_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo="${1:?usage: run.sh /path/to/RH_Lean}"
cd "$repo"
pin=9cbfce5295343bcb411e6d2cb159b59995cd985b
git cat-file -e "$pin^{commit}" 2>/dev/null || git fetch --no-tags --depth=1 origin "$pin"
python3 scripts/lean/slot_anchored/prepare_anchored.py "$PWD"
python3 "$bundle_dir/check_inventory.py" "$PWD" | tee total-mass-inventory.log
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
mkdir -p .lake/build/lib/lean
log=total-mass-lean.log
: > "$log"
baseline=(
 VF919OriginalMarkedSharpenedSignedNNS VF919NativeEnergyInduction
 VF919NativeSourceMoments VF919NativeSevenEighthsReplay
 VF919FiniteSlotReflectedGain VF919TiltedLowReflection VF919TiltedLowPhysical
 VF919TiltedProbe VF919TiltedHighTails VF919TiltedHighCentral
 VF919TiltedHighPrincipal VF919TiltedHighTransport VF919TiltedHighAssembly
 VF919NativeStrictSevenEighths VF919NativeStrictMertens
 VF919LowFirstPhysicalTiltFullBudget VF919LowFirstSlotCalibratedData
 VF919AnchoredSmallTail VF919AnchoredPrincipalRemainder VF919AnchoredHighPrincipal
 VF919AnchoredHighTails VF919AnchoredHighTransport VF919AnchoredHighAssembly
 VF919LowFirstSlotAnchoredEndpoint VF919ActualSlotMinRetighten
 VF919OriginalLowTupleSignedGram
)
targets=(VF919TotalMassLowEnergy VF919TotalMassLowPhysical VF919TotalMassEndpoint)
for name in "${baseline[@]}" "${targets[@]}"; do
  echo "Checking $name" | tee -a "$log"
  source="research/oai_434/${name}.lean"
  if grep -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' "$source"; then exit 1; fi
  env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/research.oai_434.${name}.olean" "$source" \
    2>&1 | tee -a "$log"
done
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  "$bundle_dir/ExactTypes.lean" 2>&1 | tee -a "$log"
if grep -E 'sorryAx|admitAx' "$log"; then
  echo 'Rejected: admitted proof dependency' >&2
  exit 1
fi
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  --run "$bundle_dir/TotalMassAudit.lean" 2>&1 | tee total-mass-audit.log
echo 'Total-mass complete endpoint: warning-fatal proof, exact public types, and live-axiom audit passed.'
