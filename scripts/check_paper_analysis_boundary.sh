#!/usr/bin/env bash
set -euo pipefail

if grep -RInE --include='*.lean' '^[[:space:]]*import[[:space:]]+RHLean\.Proof\.' RHLean/Analysis; then
  echo 'Analysis modules must not import Proof modules.' >&2
  exit 1
fi

if grep -RInE --include='*.tex' 'RHLean/(Proof|Arithmetic|Geometry|Kernel|CellMask|Verification)/|RHLean\.(Proof|Arithmetic|Geometry|Kernel|CellMask|Verification)\.' paper; then
  echo 'Paper Lean references must point only to RHLean/Analysis.' >&2
  exit 1
fi

echo 'Paper / Analysis boundary check passed.'
