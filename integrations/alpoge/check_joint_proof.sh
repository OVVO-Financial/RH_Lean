#!/usr/bin/env bash
# Build the ORIGINAL Alpoge proof under its pinned compiler and compile the
# EXACT same RHLean.AlpogeInterface source as in RH_Lean's native build.
# This is the full cross-project proof assembly, not an axiom or a .olean transplant.
set -euo pipefail

UPSTREAM_SHA="7cbf7a0c32fca1badf05931879a37c3f8a2b03b4"
UPSTREAM_MATHLIB_SHA="0df444a360eaa60ab8c11dca51a86af692955474"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
WORK_DIR="${1:-${RUNNER_TEMP:-/tmp}/alpoge_rhlean_merged_tree}"
LOG_FILE="$WORK_DIR/AlpogeAxiomAudit.log"

command -v lake >/dev/null || { echo 'ERROR: Lake/elan must be installed' >&2; exit 2; }
command -v git >/dev/null || { echo 'ERROR: git must be installed' >&2; exit 2; }

if [[ -e "$WORK_DIR" && ! -d "$WORK_DIR/.git" ]]; then
  echo "ERROR: non-repository directory already exists: $WORK_DIR" >&2
  exit 2
fi

if [[ ! -d "$WORK_DIR/.git" ]]; then
  mkdir -p "$WORK_DIR"
  git -C "$WORK_DIR" init
  git -C "$WORK_DIR" remote add origin https://github.com/CocoSgt/riemann-hypothesis-lean.git
fi

git -C "$WORK_DIR" fetch --depth 1 origin "$UPSTREAM_SHA"
git -C "$WORK_DIR" checkout -f --detach "$UPSTREAM_SHA"

test "$(git -C "$WORK_DIR" rev-parse HEAD)" = "$UPSTREAM_SHA"
test "$(cat "$WORK_DIR/lean-toolchain")" = "leanprover/lean4:v4.33.1"
grep -Fq "$UPSTREAM_MATHLIB_SHA" "$WORK_DIR/lakefile.toml"

# Overlaid files only. Neither upstream Main.lean nor ANY theorem source is changed.
mkdir -p "$WORK_DIR/src/RHLean" "$WORK_DIR/.lake/build/lib/lean/RHLean"
cp "$ROOT_DIR/RHLean/AlpogeInterface.lean" "$WORK_DIR/src/RHLean/AlpogeInterface.lean"
cp "$ROOT_DIR/integrations/alpoge/AlpogeProofAdapter.lean" "$WORK_DIR/src/RHLean/AlpogeProofAdapter.lean"
cp "$ROOT_DIR/integrations/alpoge/AlpogeAxiomAudit.lean" "$WORK_DIR/src/RHLean/AlpogeAxiomAudit.lean"
cmp -s "$ROOT_DIR/RHLean/AlpogeInterface.lean" "$WORK_DIR/src/RHLean/AlpogeInterface.lean"
git -C "$WORK_DIR" diff --exit-code HEAD -- src lakefile.toml lean-toolchain

(
  cd "$WORK_DIR"
  echo '== Upstream original Mathlib cache =='
  lake exe cache get
  echo '== Compiling the COMMON RHLean source with ORIGINAL Lean/Mathlib =='
  lake env lean -o .lake/build/lib/lean/RHLean/AlpogeInterface.olean \
    src/RHLean/AlpogeInterface.lean
  echo '== Building ORIGINAL full Alpoge Main theorem dependency closure =='
  lake build Main
  echo '== Compiling THE ORIGINAL proof + RHLean identity in one Lean environment =='
  lake env lean -o .lake/build/lib/lean/RHLean/AlpogeProofAdapter.olean \
    src/RHLean/AlpogeProofAdapter.lean
  echo '== Kernel axiom audit on EXACT new RHLean RH and Dirichlet declarations =='
  lake env lean src/RHLean/AlpogeAxiomAudit.lean | tee "$LOG_FILE"
)

python3 "$ROOT_DIR/integrations/alpoge/check_axioms.py" "$LOG_FILE"

echo "SUCCESS: upstream RH+GRH theorem and RHLean native Gz interface share one checked Lean 4.33.1 environment."
echo "ALPOGE_SHA=$UPSTREAM_SHA"
echo "MATHLIB_SHA=$UPSTREAM_MATHLIB_SHA"
