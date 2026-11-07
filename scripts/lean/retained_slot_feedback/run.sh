#!/usr/bin/env bash
# Pinned GitHub Actions execution only. No local Lean execution.
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
python3 scripts/lean/retained_slot_feedback/prepare.py
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
export LEAN_PATH="$PWD/.lake/build/lib/lean:$RH_PATH:$OAI_PATH"
mkdir -p .lake/build/lib/lean/research/oai_434/Feedback
: > retained-slot-analytic.log
lean -DwarningAsError=true -DmaxHeartbeats=4000000 -o .lake/build/lib/lean/research/oai_434/RetainedSlotFeedback.olean research/oai_434/RetainedSlotFeedback.lean 2>&1 | tee retained-slot-scalar.log
mapfile -t modules < <(python3 -c 'import json; print("\n".join(json.load(open("retained-slot-generation.json"))["compile_order"]))')
for name in "${modules[@]}"; do
  echo "Checking feedback/$name" | tee -a retained-slot-analytic.log
  source="research/oai_434/Feedback/$name.lean"
  if grep -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' "$source"; then exit 1; fi
  lean -DwarningAsError=true -DmaxHeartbeats=4000000 \
    -o ".lake/build/lib/lean/research/oai_434/Feedback/$name.olean" "$source" \
    2>&1 | tee -a retained-slot-analytic.log
done
python3 - <<'PY'
from pathlib import Path
import re
text=Path('retained-slot-analytic.log').read_text()
name='OAI.SevenEighths.RetainedSlotFeedback.terminal_certificate_half'
checks=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
found=[a for n,a in checks if n==name]
if len(found)!=1:raise SystemExit('Missing exact terminal axiom report')
allowed={'propext','Classical.choice','Quot.sound'}
for axioms in found:
    actual={a.strip() for a in axioms.split(',') if a.strip()}
    if not actual<=allowed:raise SystemExit('Disallowed terminal axioms: '+str(actual-allowed))
if 'sorryAx' in text or 'admitAx' in text:raise SystemExit('Admitted dependency')
print('PASS: complete generalized terminal band; only permitted terminal axioms.')
print('No new global Mertens exponent is asserted by this audit.')
PY
