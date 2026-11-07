#!/usr/bin/env bash
# Pinned GitHub Actions execution only. No local Lean execution.
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
python3 scripts/lean/retained_slot_feedback/prepare.py 2>&1 | tee retained-slot-generation.log
python3 scripts/lean/retained_slot_feedback/prepare_detector.py 2>&1 | tee -a retained-slot-generation.log
OAI_PATH="$(cd oai-upstream/lean && lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
RH_PATH="$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')"
export LEAN_PATH="$PWD/.lake/build/lib/lean:$RH_PATH:$OAI_PATH"
python3 scripts/lean/retained_slot_feedback/compile.py
