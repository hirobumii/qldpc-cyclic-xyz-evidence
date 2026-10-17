#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=4.19.0
ARCHIVE="lean-${VERSION}-linux.tar.zst"
SHA256=6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe
mkdir -p "$ROOT/.toolchain"
cd "$ROOT/.toolchain"
if [ ! -f "$ARCHIVE" ]; then
  curl --fail --location --retry 2 "https://github.com/leanprover/lean4/releases/download/v${VERSION}/${ARCHIVE}" --output "$ARCHIVE"
fi
printf '%s  %s\n' "$SHA256" "$ARCHIVE" | sha256sum --check
if [ ! -x "lean-${VERSION}-linux/bin/lean" ]; then
  tar --zstd -xf "$ARCHIVE"
fi
"lean-${VERSION}-linux/bin/lean" --version
"lean-${VERSION}-linux/bin/lean" --githash
