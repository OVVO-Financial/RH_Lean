#!/usr/bin/env bash
set -euo pipefail
repo="${1:?usage: run.sh /path/to/RH_Lean}"
cd "$repo"
# Reuse the unchanged source-pinned generator and its complete native audit.
bash scripts/lean/total_mass/run.sh "$PWD"
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
for name in VF919PrincipalSignedRemainder VF919PrincipalFiniteResponse VF919PrincipalResponseMass VF919PrincipalAllDelayReturn VF919PhysicalPrincipalResponse; do
  source="research/oai_434/$name.lean"
  if grep -nE '\b(sorry|admit|axiom)\b' "$source"; then exit 1; fi
  env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/research.oai_434.$name.olean" "$source" \
    2>&1 | tee "physical-principal-response-$name.log"
  test -s ".lake/build/lib/lean/research.oai_434.$name.olean"
done
python3 scripts/lean/physical_principal_response/check_inventory.py
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  scripts/lean/physical_principal_response/ExactTypes.lean \
  2>&1 | tee physical-principal-response-types.log
env LEAN_PATH="$RH_PATH:$OAI_PATH" lean -DwarningAsError=true \
  --run scripts/lean/physical_principal_response/Audit.lean \
  2>&1 | tee physical-principal-response-audit.log
if grep -E 'sorryAx|admitAx' physical-principal-response-*.log; then exit 1; fi
