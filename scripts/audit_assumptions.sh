#!/usr/bin/env bash
set -euo pipefail

if grep -RInE --include='*.lean' '\b(sorry|admit)\b' RHLean RHLean.lean; then
  echo 'Unfinished Lean proof found.' >&2
  exit 1
fi

mapfile -t axiom_lines < <(grep -RInE --include='*.lean' '^[[:space:]]*axiom[[:space:]]' RHLean RHLean.lean || true)
for line in "${axiom_lines[@]}"; do
  case "$line" in
    RHLean/Open/ActualStartFrame.lean:*) ;;
    *)
      echo "Unexpected axiom: $line" >&2
      exit 1
      ;;
  esac
done

echo 'Lean source audit passed.'
