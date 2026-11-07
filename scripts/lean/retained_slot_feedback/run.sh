#!/usr/bin/env bash
# Pinned GitHub Actions execution only. No local Lean execution.
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
export LEAN_PATH="$PWD/.lake/build/lib/lean:$RH_PATH:$OAI_PATH"
mkdir -p .lake/build/lib/lean/research/oai_434
lean -DwarningAsError=true -o .lake/build/lib/lean/research/oai_434/RetainedSlotFeedback.olean research/oai_434/RetainedSlotFeedback.lean 2>&1 | tee retained-slot-scalar.log
if grep -E 'sorryAx|admitAx|native_decide|ofReduceBool' retained-slot-scalar.log; then
  echo 'Disallowed proof dependency' >&2
  exit 1
fi
printf '%s\n' 'SCALAR_CHECK_ONLY: analytic propagation not yet compiled by this revision.' | tee retained-slot-status.log
