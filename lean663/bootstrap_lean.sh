#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ARCHIVE=lean-4.35.0-linux.tar.zst
SHA=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
mkdir -p "$ROOT/.toolchain"
cd "$ROOT/.toolchain"
if [ ! -f "$ARCHIVE" ]; then
  curl --fail --location --retry 2 \
    https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
    --output "$ARCHIVE"
fi
printf '%s  %s\n' "$SHA" "$ARCHIVE" | sha256sum --check
if [ ! -x lean-4.35.0-linux/bin/lean ]; then
  tar --zstd -xf "$ARCHIVE"
fi
./lean-4.35.0-linux/bin/lean --version
printf 'Toolchain bin: %s\n' "$ROOT/.toolchain/lean-4.35.0-linux/bin"
