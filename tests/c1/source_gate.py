#!/usr/bin/env python3
"""Fence the C1 runtime's local import closure; report source size honestly.

This is a source dependency audit, not a linked-binary or proof-erasure claim.
The companion tests/trust-surface.sh scans C1 with its existing tested lexer.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[2]
FORBIDDEN = tuple(
    "ConLeche." + name
    for name in ("Model", "SetTheory", "SetModel", "Semantics", "Term", "Complete", "MainTheorem", "Challenge")
) + ("PskernelC1.Soundness", "PskernelC1Tests")
ENTRY_POINTS = ("PskernelC1.Kernel", "PskernelC1.Main")


def code_only(source: str) -> str:
    """Blank nested comments and strings, retaining newlines for import headers."""
    out = list(source)
    i = 0

    def blank(start: int, end: int) -> None:
        for k in range(start, end):
            if out[k] != "\n":
                out[k] = " "

    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        blank(start, min(i, len(source)))
    return "".join(out)


def module_path(name: str) -> Path:
    return ROOT / (name.replace(".", "/") + ".lean")


def imports(path: Path) -> list[str]:
    found = []
    for line in code_only(path.read_text()).splitlines():
        match = re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)$", line)
        if match:
            found.extend(word for word in match[1].split() if word != "all")
    return found


def closure(entry: str) -> dict[str, list[str]]:
    paths: dict[str, list[str]] = {}
    pending = [(entry, [entry])]
    while pending:
        name, route = pending.pop()
        if name in paths:
            continue
        path = module_path(name)
        if not path.exists():
            if any(name == top or name.startswith(top + ".") for top in ("Lean", "Init", "Std", "Lake")):
                continue  # These modules belong to the pinned toolchain.
            raise ValueError("unresolved non-toolchain import: " + " -> ".join(route))
        paths[name] = route
        pending.extend((dependency, route + [dependency]) for dependency in imports(path))
    return paths


def main() -> int:
    problems = []
    report = {"kind": "source-import-closure", "runtime_entries": {}}
    for entry in ENTRY_POINTS:
        dependencies = closure(entry)
        for name, route in dependencies.items():
            if any(name == banned or name.startswith(banned + ".") for banned in FORBIDDEN):
                problems.append("model/proof tier in runtime closure: " + " -> ".join(route))
        report["runtime_entries"][entry] = {
            "local_modules": len(dependencies),
            "local_source_lines": sum(len(module_path(name).read_text().splitlines()) for name in dependencies),
            "modules": sorted(dependencies),
        }
    owned = sorted((ROOT / "PskernelC1").glob("*.lean"))
    for path in owned:
        if not re.match(r"^\s*module\b", code_only(path.read_text())):
            problems.append(f"missing module header: {path.relative_to(ROOT)}")
    report["owned_source_lines"] = {
        str(path.relative_to(ROOT)): len(path.read_text().splitlines()) for path in owned
    }
    report["notes"] = [
        "Owned source size does not count the inherited checker and proves no binary-size claim.",
        "Import counts include model-free verification modules; erased proofs need no model at runtime.",
        "Runtime/compiler escapes are audited separately by tests/trust-surface.sh.",
    ]
    output = ROOT / "_tmp/c1/source-closure.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    if problems:
        print("C1 SOURCE GATE FAIL\n" + "\n".join(problems), file=sys.stderr)
        return 1
    for entry, entry_report in report["runtime_entries"].items():
        print(f"{entry}: {entry_report['local_modules']} local modules, model-free import closure")
    print("C1 source/import report: _tmp/c1/source-closure.json")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f"C1 SOURCE GATE FAIL: {error}", file=sys.stderr)
        sys.exit(1)
