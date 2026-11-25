#!/usr/bin/env bash
# External replay only. Keep the native Lean 4.34.1 environment untouched.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
upstream="$(realpath "$1")"
pin=774b9e8022f50d20be861ecc9d609cfc26436a81
test "$(git -C "$upstream" rev-parse HEAD)" = "$pin"
test "$(git -C "$upstream" rev-parse HEAD:src)" = 24df20b62d9976ccd20da819bc20b16f808f0fdd
test "$(cat "$upstream/lean-toolchain")" = leanprover/lean4:v4.33.1
test "$(git -C "$upstream" hash-object lake-manifest.json)" = b4d1ec31575a26b2159ec3a262b482bc051f3f6f

# Do not create a new file inside the frozen src tree before restoring
# its pinned public community cache.
cd "$upstream"
bash "$root/scripts/ci/install_pinned_lean_retry.sh"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_ABORT_ON_PANIC=1
lake exe cache get
lake build --no-build Main

# Splice the actual main-branch-compatible source definitions, rather
# than maintaining a possibly divergent redefinition.
python3 - "$root" "$upstream" <<'PY'
from pathlib import Path
import re, sys
root, upstream = map(Path, sys.argv[1:])
native = (root / "RHLean/Analysis/AlpogeNativeBoundHandoff.lean").read_text()
defs = []
for name in ("statementOCSz", "statementOCGz", "SmallEpsilonWindowBound"):
    m = re.search(r"^def " + name + r"\b.*?(?=\n\n)", native, re.M | re.S)
    if m is None:
        raise SystemExit("Missing literal native definition: " + name)
    defs.append(m.group(0))
block = ("namespace RHLean.Analysis.AlpogeNativeBoundHandoff\n\n"
         + "\n\n".join(defs)
         + "\n\nend RHLean.Analysis.AlpogeNativeBoundHandoff")
template = (root / "scripts/alpoge_stage1/ClosedRH.lean.in").read_text()
marker = "-- NATIVE_SOURCE_DEFINITIONS"
if template.count(marker) != 1:
    raise SystemExit("Native source insertion marker missing or duplicated")
(upstream / "RHLeanStage1.lean").write_text(template.replace(marker, block))
PY
# Compile the newly extracted proof, not just check the upstream Main cache.
# No wrapper imports an olean from the RH_Lean 4.34.1 environment.
lake env lean --tstack=400000 -o RHLeanStage1.olean RHLeanStage1.lean 2>&1 | tee "$root/alpoge-stage1.log"
grep -q 'STAGE1_CLOSED_RH_CHECKED' "$root/alpoge-stage1.log"
test -s RHLeanStage1.olean
