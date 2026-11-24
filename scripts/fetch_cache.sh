#!/bin/sh
# Download the prebuilt Mathlib and Physlib files for the pinned Physlib revision.
# Run once after cloning, before the first `lake build`.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/lean"
lake update --keep-toolchain 2>/dev/null || true
lake exe cache get
cd .lake/packages/physlib
LAKE_CONFIG="$PWD/lake-cache.toml" lake cache get --scope="physlib-master/leanprover-lean4-v4.36.0/physlib"
