#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ARCHIVE=lean-4.19.0-linux.tar.zst
SHA=6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe
mkdir -p "$ROOT/.toolchain"
cd "$ROOT/.toolchain"
if [ ! -f "$ARCHIVE" ]; then
  curl --fail --location --retry 2 \
    https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst \
    --output "$ARCHIVE"
fi
printf '%s  %s\n' "$SHA" "$ARCHIVE" | sha256sum --check
if [ ! -x lean-4.19.0-linux/bin/lean ]; then
  tar --zstd -xf "$ARCHIVE"
fi
./lean-4.19.0-linux/bin/lean --version
printf 'Toolchain bin: %s\n' "$ROOT/.toolchain/lean-4.19.0-linux/bin"
