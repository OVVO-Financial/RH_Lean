#!/usr/bin/env bash
# Install the exact lean-toolchain pin, retrying transient release-server/TLS
# failures. The preceding lean-action@v1 path had no retry around elan's
# first distribution download, so one TLS error stopped proof verification.
#
# This script never changes lean-toolchain, Lake package pins, or proof sources.
set -euo pipefail

: "${HOME:?HOME must be set}"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
toolchain="$(tr -d '\r\n' < lean-toolchain)"

if [[ ! "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
  echo "::error::Unexpected pinned Lean toolchain: $toolchain" >&2
  exit 1
fi

echo "::notice::Installing the exact pinned toolchain: $toolchain"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  echo "Bootstrapping elan from leanprover/elan..."
  curl --fail --location --silent --show-error \
    --retry 6 --retry-all-errors --retry-delay 4 \
    --connect-timeout 20 --max-time 180 \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    --output "$tmpdir/elan-init.sh"

  success=false
  for attempt in 1 2 3 4 5; do
    echo "::group::elan bootstrap attempt $attempt/5"
    if sh "$tmpdir/elan-init.sh" -y --default-toolchain none; then
      success=true
      echo "::endgroup::"
      break
    fi
    echo "::endgroup::"
    echo "::warning::elan bootstrap attempt $attempt failed; retrying transient download error."
    if [[ "$attempt" -lt 5 ]]; then sleep $((attempt * 6)); fi
  done
  if [[ "$success" != true ]] || [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    echo "::error::Unable to bootstrap elan after five attempts." >&2
    exit 1
  fi
fi

export PATH="$ELAN_HOME/bin:$PATH"
if [[ -n "${GITHUB_PATH:-}" ]]; then
  echo "$ELAN_HOME/bin" >> "$GITHUB_PATH"
fi

# elan uses lean-toolchain to select the precise release, and installs into
# ELAN_HOME. A failed or partial download is not treated as proof failure.
success=false
for attempt in 1 2 3 4 5 6; do
  echo "::group::Pinned Lean distribution attempt $attempt/6 ($toolchain)"
  if "$ELAN_HOME/bin/elan" toolchain install "$toolchain" \
      && "$ELAN_HOME/bin/lean" --version \
      && "$ELAN_HOME/bin/lake" --version; then
    success=true
    echo "::endgroup::"
    break
  fi
  echo "::endgroup::"
  echo "::warning::Lean toolchain install or verification failed on attempt $attempt/6 (possible release-server TLS outage)."
  if [[ "$attempt" -lt 6 ]]; then sleep $((attempt * 8)); fi
done

if [[ "$success" != true ]]; then
  echo "::error::Could not install or verify pinned Lean toolchain $toolchain after six attempts. This is a toolchain/setup failure, not a proof failure." >&2
  exit 1
fi

echo "::notice::Exact pinned Lean and Lake executables are verified."
