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
mkdir -p "$PACKAGE/docs/pskernel-c1"
install -m 644 docs/pskernel-c1/*.md "$PACKAGE/docs/pskernel-c1/"
git -C "$PWD" rev-parse HEAD > "$PACKAGE/REVISION"
# Keep guide-to-guide links local. Pin source links to the packaged revision.
python3 - "$PACKAGE" <<'PY'
import pathlib
import re
import sys

root = pathlib.Path.cwd()
package = pathlib.Path(sys.argv[1]).resolve()
revision = (package / "REVISION").read_text().strip()
for document in [package / "PSKERNEL_C1.md", *package.glob("docs/pskernel-c1/*.md")]:
    source = root / document.relative_to(package)

    def pin_source_link(match):
        href = match[1]
        if href.startswith("#") or re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", href):
            return match[0]
        path, marker, fragment = href.partition("#")
        if (document.parent / path).exists():
            return match[0]
        target = (source.parent / path).resolve()
        if not target.exists():
            raise ValueError(f"missing guide target: {source}: {href}")
        kind = "tree" if target.is_dir() else "blob"
        url = f"https://github.com/dwijayuda/con-leche/{kind}/{revision}/{target.relative_to(root).as_posix()}"
        return f"]({url}{marker}{fragment})"

    document.write_text(re.sub(r"\]\(([^)]+)\)", pin_source_link, document.read_text()))
PY
(cd "$PACKAGE" && sha256sum pskernel-c1 > SHA256SUMS)
tar -czf _tmp/c1/pskernel-c1-linux-x86_64.tar.gz -C "$PACKAGE" \
  pskernel-c1 LICENSE PSKERNEL_C1.md docs lean-toolchain REVISION SHA256SUMS
