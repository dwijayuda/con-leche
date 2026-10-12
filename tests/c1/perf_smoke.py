#!/usr/bin/env python3
"""Matched resource smoke: upstream CLI, C1, and C1 with statistics.

Only verdicts and execution failures gate CI. Timings from shared runners are
advisory; instructions:u are recorded only when the host supplies a working PMU.
This is a small regression probe, not a Mathlib-scale performance claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess
import sys
import tarfile


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "_tmp/c1/perf"
CONFIGS = (
    ("con-leche", ".lake/build/bin/con-leche", [], "con-leche: accepted "),
    ("c1", ".lake/build/bin/pskernel-c1", [], "pskernel-c1: accepted "),
    ("c1-stats", ".lake/build/bin/pskernel-c1", ["--stats"], "pskernel-c1: accepted "),
)


def positive(value: str) -> int:
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_output(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=30)
    return (result.stdout or result.stderr).strip()


def fixtures() -> list[tuple[str, Path]]:
    directory = OUT / "inputs"
    directory.mkdir(parents=True, exist_ok=True)
    selected = [
        ("init-prelude", "good/init-prelude.ndjson"),
        ("let-ladder", "good/perf/let-ladder.ndjson"),
    ]
    result = []
    with tarfile.open(ROOT / "tests/arena/lean-arena-tests.tar.gz", "r:gz") as archive:
        for label, member_name in selected:
            # Copy only named regular-file payloads into paths chosen here.
            # Do not extract archive paths or follow archive symlinks.
            member = archive.getmember(member_name)
            if not member.isfile():
                raise ValueError(f"not a regular fixture: {member_name}")
            source = archive.extractfile(member)
            if source is None:
                raise ValueError(f"unreadable fixture: {member_name}")
            path = directory / (label + ".ndjson")
            with source, path.open("wb") as destination:
                shutil.copyfileobj(source, destination)
            result.append((label, path))
    result.append(("parallel-install", ROOT / "tests/e2e/pinstall_ok.ndjson"))
    return result


def instructions(path: Path) -> int | None:
    if not path.exists():
        return None
    for line in path.read_text().splitlines():
        fields = line.split(";")
        if len(fields) >= 3 and fields[2].strip() == "instructions:u":
            value = fields[0].strip()
            if value.isdecimal():
                return int(value)
    return None


def probe_perf() -> tuple[str | None, str]:
    binary = shutil.which("perf")
    if binary is None:
        return None, "perf is not installed"
    output = OUT / "perf-probe.txt"
    result = subprocess.run(
        [binary, "stat", "--no-big-num", "-x", ";", "-e", "instructions:u", "-o", str(output), "--", "true"],
        capture_output=True, text=True, timeout=15,
    )
    if result.returncode == 0 and instructions(output) is not None:
        return binary, "instructions:u available; counters include the identical time/timeout wrappers"
    reason = (result.stderr or (output.read_text() if output.exists() else "no counter result")).strip()
    return None, "instructions:u unavailable: " + reason[-700:]


def run_sample(label: str, path: Path, config: tuple, repetition: int,
               jobs: int, limit: int, perf: str | None, warmup: bool) -> dict:
    name, executable, extra_flags, acceptance = config
    stage = "warmup" if warmup else "sample"
    stem = OUT / "logs" / f"{label}-{name}-{stage}-{repetition}"
    stdout_path = stem.with_suffix(".stdout")
    stderr_path = stem.with_suffix(".stderr")
    time_path = stem.with_suffix(".time")
    perf_path = stem.with_suffix(".perf")
    checker_command = [str(ROOT / executable), "--verified", f"--jobs={jobs}", *extra_flags, str(path)]
    command = [
        "/usr/bin/time", "-f", "%U\t%S\t%e\t%M\t%x", "-o", str(time_path),
        "timeout", "--signal=TERM", "--kill-after=5s", str(limit), *checker_command,
    ]
    if perf:
        command = [perf, "stat", "--no-big-num", "-x", ";", "-e", "instructions:u", "-o", str(perf_path), "--", *command]
    with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
        result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr, timeout=limit + 20)
    sample = {
        "fixture": label, "config": name, "repetition": repetition, "warmup": warmup,
        "argv": [executable, "--verified", f"--jobs={jobs}", *extra_flags, str(path.relative_to(ROOT))],
        "exit": result.returncode,
        "accepted": result.returncode == 0 and any(
            line.startswith(acceptance) for line in stdout_path.read_text().splitlines()
        ),
        "stderr_bytes": stderr_path.stat().st_size,
        "instructions_u": instructions(perf_path) if perf else None,
        "user_s": None, "system_s": None, "wall_s": None, "max_rss_kib": None,
    }
    if time_path.exists():
        fields = time_path.read_text().splitlines()[-1].split("\t")
        if len(fields) == 5:
            sample.update(user_s=float(fields[0]), system_s=float(fields[1]),
                          wall_s=float(fields[2]), max_rss_kib=int(fields[3]))
    print(f"{stage}: {label} / {name}: exit={sample['exit']}, wall={sample['wall_s']}s, RSS={sample['max_rss_kib']} KiB", flush=True)
    return sample


def aggregate(samples: list[dict]) -> list[dict]:
    groups = sorted({(sample["fixture"], sample["config"]) for sample in samples if not sample["warmup"]})
    result = []
    for fixture, config in groups:
        cells = [sample for sample in samples if not sample["warmup"] and sample["fixture"] == fixture and sample["config"] == config]
        row = {"fixture": fixture, "config": config, "accepted": all(sample["accepted"] for sample in cells)}
        for metric in ("user_s", "system_s", "wall_s", "max_rss_kib", "instructions_u", "stderr_bytes"):
            values = [sample[metric] for sample in cells if sample[metric] is not None]
            row[metric] = {
                "median": statistics.median(values), "min": min(values), "max": max(values)
            } if values else None
        result.append(row)
    return result


def markdown(report: dict) -> str:
    lines = [
        "# C1 matched resource smoke", "",
        "Successful verdicts are required. Resource numbers are observations on this runner; shared-runner elapsed time is advisory and has no pass/fail threshold.", "",
        f"Source revision: `{report['commit']}`. Toolchain: `{report['toolchain']}`.", "",
        "The baseline is the con-leche executable built from this same source revision. C1 fixes verified mode; C1-stats enables the telemetry removed from its default path. Every configuration checks the same bytes at the same worker count.", "",
        f"Hardware counter status: {report['hardware_counters']}", "",
        "| Fixture | Configuration | Accepted | Median wall s | Median user s | Median peak RSS KiB | Median instructions:u |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for row in report["summary"]:
        def value(metric: str) -> str:
            data = row[metric]
            return "unavailable" if data is None else f"{data['median']:,.2f}"
        lines.append(f"| {row['fixture']} | {row['config']} | {row['accepted']} | {value('wall_s')} | {value('user_s')} | {value('max_rss_kib')} | {value('instructions_u')} |")
    lines += ["", "## Binary artifacts", "", "| Binary | Bytes | SHA-256 |", "|---|---:|---|"]
    for name, binary in report["binaries"].items():
        lines.append(f"| {name} | {binary['bytes']:,} | `{binary['sha256']}` |")
    lines += [
        "", "The JSON report includes every measured run, warmup, command, input hash, and min/median/max. Binary bytes include the inherited checker; the small owned C1 source interface does not imply a small foundational codebase.", "",
        "These small inputs do not establish full Arena completeness, Mathlib throughput, compiler correctness, or binary-level verification.", "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=positive, default=3)
    parser.add_argument("--jobs", type=positive, default=1)
    parser.add_argument("--timeout", type=positive, default=180)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "logs").mkdir(exist_ok=True)
    for _, executable, _, _ in CONFIGS:
        if not os.access(ROOT / executable, os.X_OK):
            raise ValueError(f"missing executable: {executable}; build it first")
    if not Path("/usr/bin/time").exists() or shutil.which("timeout") is None:
        raise ValueError("Linux /usr/bin/time and timeout are required")
    inputs = fixtures()
    perf, perf_status = probe_perf()
    print(perf_status, flush=True)
    samples = []
    for label, path in inputs:
        for config in CONFIGS:
            samples.append(run_sample(label, path, config, 0, args.jobs, args.timeout, perf, True))
        for repetition in range(args.repetitions):
            # Rotate the three configurations to reduce fixed-order bias.
            order = CONFIGS[repetition % 3:] + CONFIGS[:repetition % 3]
            for config in order:
                samples.append(run_sample(label, path, config, repetition + 1, args.jobs, args.timeout, perf, False))
    report = {
        "schema_version": 1,
        "commit": command_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"]),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lean_version": command_output(["lean", "--version"]),
        "platform": platform.platform(), "machine": platform.machine(), "cpu_count": os.cpu_count(),
        "hardware_counters": perf_status, "jobs": args.jobs, "repetitions": args.repetitions,
        "comparison": "same-source binaries; upstream CLI vs verified-only C1 vs C1 with statistics",
        "binaries": {
            name: {"bytes": (ROOT / executable).stat().st_size, "sha256": sha256(ROOT / executable)}
            for name, executable, _, _ in CONFIGS
        },
        "inputs": {label: {"bytes": path.stat().st_size, "sha256": sha256(path)} for label, path in inputs},
        "samples": samples, "summary": aggregate(samples),
    }
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    rendered = markdown(report)
    (OUT / "summary.md").write_text(rendered)
    print(rendered)
    failures = [sample for sample in samples if not sample["accepted"]]
    if failures:
        print(f"C1 resource smoke FAIL: {len(failures)} unsuccessful checker runs", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"C1 resource smoke ERROR: {error}", file=sys.stderr)
        sys.exit(1)
