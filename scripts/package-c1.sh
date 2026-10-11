#!/usr/bin/env bash
# Bundle the built C1 executable with its license, usage and exact provenance.
set -euo pipefail
cd "$(dirname "$0")/.."

BIN=${C1_BIN:-.lake/build/bin/pskernel-c1}
PACKAGE=_tmp/c1/package
test -x "$BIN" || { echo "missing executable: $BIN" >&2; exit 1; }
mkdir -p "$PACKAGE"
install -m 755 "$BIN" "$PACKAGE/pskernel-c1"
install -m 644 LICENSE PSKERNEL_C1.md lean-toolchain "$PACKAGE/"
git -C "$PWD" rev-parse HEAD > "$PACKAGE/REVISION"
(cd "$PACKAGE" && sha256sum pskernel-c1 > SHA256SUMS)
tar -czf _tmp/c1/pskernel-c1-linux-x86_64.tar.gz -C "$PACKAGE" \
  pskernel-c1 LICENSE PSKERNEL_C1.md lean-toolchain REVISION SHA256SUMS
