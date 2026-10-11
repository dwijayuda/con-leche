#!/usr/bin/env python3
"""Measure the actual C1 binary on an integrity-checked Arena archive subset.

This is a capability inventory, never a full-Arena qualification command.
All metadata tests remain in the report, including absent and unrun inputs.
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import subprocess
import tarfile
import time
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def download(url: str, path: Path, limit: int) -> None:
    if not url.startswith('https://arena.lean-lang.org/'):
        raise ValueError('snapshot URLs must name the documented HTTPS Arena host')
    part = path.with_suffix(path.suffix + '.part')
    request = Request(url, headers={'User-Agent': 'PSKernel-C1-capability-inventory'})
    with urlopen(request, timeout=60) as response, part.open('wb') as target:
        total = 0
        while chunk := response.read(1024 * 1024):
            total += len(chunk)
            if total > limit:
                raise ValueError(f'download exceeds documented capture resource limit: {url}')
            target.write(chunk)
    part.replace(path)


def safe_parts(name: str) -> tuple[str, ...]:
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or '\\' in name or not path.parts:
        raise ValueError(f'non-relative archive/test path: {name}')
    return path.parts


def archive_identity(name: str) -> tuple[str, str] | None:
    parts = safe_parts(name)
    if not name.endswith('.ndjson'):
        return None
    for i, part in enumerate(parts):
        if part in ('good', 'bad', 'either'):
            remainder = '/'.join(parts[i + 1:])
            if not remainder or remainder == '.ndjson':
                raise ValueError(f'empty archive test name: {name}')
            return remainder[:-len('.ndjson')], {'good': 'accept', 'bad': 'reject', 'either': 'either'}[part]
    raise ValueError(f'input without outcome directory: {name}')


def metadata_index(metadata: dict) -> dict[str, dict]:
    tests = metadata.get('tests')
    if not isinstance(tests, list) or not tests:
        raise ValueError('expected a nonempty Arena tests array')
    index = {}
    for test in tests:
        name = test['name']
        safe_parts(name)
        if name in index:
            raise ValueError(f'duplicate metadata test: {name}')
        if test.get('outcome') not in ('accept', 'reject', 'either'):
            raise ValueError(f'unsupported metadata outcome: {name}')
        digest = test.get('sha256', '')
        if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
            raise ValueError(f'missing or invalid input digest: {name}')
        index[name] = test
    return index


def unpack(archive: Path, destination: Path, index: dict[str, dict]) -> dict[str, Path]:
    """Read regular inputs only; verify their exact bytes and expected outcome."""
    found: dict[str, Path] = {}
    total = 0
    with tarfile.open(archive, 'r:gz') as bundle:
        for member in bundle:
            safe_parts(member.name)
            if member.isdir():
                continue
            if not member.isfile():
                raise ValueError(f'non-regular archive member: {member.name}')
            identity = archive_identity(member.name)
            if identity is None:
                continue
            name, expected = identity
            total += member.size
            if member.size > 64 * 1024**2 or total > 512 * 1024**2:
                raise ValueError('archive exceeds documented capture resource limit')
            stream = bundle.extractfile(member)
            if stream is None:
                raise ValueError(f'unreadable archive input: {member.name}')
            data = stream.read()
            digest = hashlib.sha256(data).hexdigest()
            if name not in index:
                # Some archives flatten names. A UNIQUE content-and-outcome
                # identity is exact correspondence, not a name-based guess.
                candidates = [n for n, t in index.items()
                              if t['sha256'] == digest and t['outcome'] == expected]
                if len(candidates) != 1:
                    raise ValueError(f'unresolved archive identity: {member.name}')
                name = candidates[0]
            if name in found:
                raise ValueError(f'duplicate archive input: {name}')
            if index[name]['sha256'] != digest or index[name]['outcome'] != expected:
                raise ValueError(f'archive/metadata integrity mismatch: {name}')
            target = destination.joinpath(*safe_parts(name + '.ndjson'))
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            found[name] = target
    if not found:
        raise ValueError('no test inputs in archive')
    return found


def classify(returncode: int, expected: str) -> str:
    if expected not in ('accept', 'reject', 'either'):
        raise ValueError('invalid expected outcome')
    if returncode in (0, 1):
        if expected == 'either':
            return 'matched_either'
        wanted = 0 if expected == 'accept' else 1
        if returncode == wanted:
            return 'matched'
        return 'wrong_accept' if returncode == 0 else 'wrong_reject'
    if returncode == 2:
        return 'declined'
    if returncode == 3:
        return 'error'
    return 'signal' if returncode < 0 else 'unexpected_exit'


def summarize(rows: list[dict]) -> dict:
    counts = dict(sorted(Counter(row['status'] for row in rows).items()))
    missing = [row['name'] for row in rows if row['status'] == 'not_in_archive']
    gaps = [row['name'] for row in rows
            if row['status'] not in ('matched', 'matched_either', 'not_in_archive')]
    return {'counts': counts, 'metadata_tests': len(rows),
            'archive_tests': len(rows) - len(missing), 'not_in_archive': missing,
            'present_input_gaps': gaps,
            'full_arena_qualified': False,
            'scope': 'captured public archive subset; not a public Arena submission'}


def run_case(binary: Path, input_path: Path, log: Path, jobs: int, timeout: float) -> dict:
    started = time.monotonic()
    command = [str(binary), '--verified', f'--jobs={jobs}', str(input_path)]
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('wb') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
            result = {'returncode': code}
        except subprocess.TimeoutExpired:
            # Own process group only. Never kill by an executable-name pattern.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            result = {'returncode': None, 'status': 'timeout'}
    result.update({'command': command, 'wall_seconds': time.monotonic() - started,
                   'timeout_seconds': timeout, 'log': str(log)})
    return result


def write_report(out: Path, report: dict) -> None:
    report['summary'] = summarize(report['tests'])
    temporary = out / 'report.json.part'
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(out / 'report.json')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--expected-source-revision', required=True)
    parser.add_argument('--source', type=Path, default=ROOT / 'tests/c1/arena-source.json')
    parser.add_argument('--output', type=Path, default=ROOT / '_tmp/c1-next/arena')
    parser.add_argument('--snapshot-mode', choices=('capture', 'pinned'), default='pinned')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--case-timeout', type=float, default=60)
    parser.add_argument('--budget-seconds', type=float, default=900)
    args = parser.parse_args()
    if args.jobs < 1 or not all(math.isfinite(x) and x > 0
                               for x in (args.case_timeout, args.budget_seconds)):
        parser.error('worker count and time budgets must be positive and finite')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = json.loads(args.source.read_text())
    source_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    if source_revision != args.expected_source_revision:
        raise ValueError('checkout does not match requested source revision')
    binary = args.binary.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise ValueError('C1 executable is missing or not executable')
    version = subprocess.check_output([str(binary), '--version'], timeout=10, text=True).strip()
    if not version.startswith('pskernel-c1 '):
        raise ValueError('requested executable does not identify itself as pskernel-c1')
    if args.snapshot_mode == 'pinned' and not all(source.get(k) for k in ('archive_sha256', 'metadata_sha256')):
        raise ValueError('pinned mode requires both captured file digests')
    archive, metadata_file = out / 'suite.tar.gz', out / 'metadata.json'
    download(source['metadata_url'], metadata_file, 32 * 1024**2)
    download(source['archive_url'], archive, 64 * 1024**2)
    captured = {**source, 'archive_sha256': sha256(archive),
                'metadata_sha256': sha256(metadata_file)}
    for key in ('archive_sha256', 'metadata_sha256'):
        if source.get(key) and source[key] != captured[key]:
            raise ValueError(f'{key} changed; review a new snapshot explicitly')
    metadata = json.loads(metadata_file.read_text())
    if metadata.get('meta', {}).get('git_revision') != source['arena_revision']:
        raise ValueError('Arena metadata revision changed; do not silently update the pin')
    (out / 'captured-source.json').write_text(json.dumps(captured, indent=2) + '\n')
    index = metadata_index(metadata)
    inputs = unpack(archive, out / 'inputs', index)
    shutil.copy2(binary, out / 'pskernel-c1')
    rows = [{'name': name, 'expected': test['outcome'], 'input_sha256': test['sha256'],
             'input_bytes': test.get('size'), 'exporter': test.get('lean4export_version'),
             'input_lean_version': test.get('lean_version'),
             'status': 'not_run' if name in inputs else 'not_in_archive'}
            for name, test in sorted(index.items())]
    report = {'schema': 1, 'captured_at': datetime.now(timezone.utc).isoformat(),
              'checker_revision': source_revision, 'checker_version': version,
              'checker_sha256': sha256(binary), 'checker_bytes': binary.stat().st_size,
              'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'suite_source': captured, 'snapshot_mode': args.snapshot_mode,
              'published_metadata': metadata['meta'], 'jobs': args.jobs,
              'resource_profile': {'case_timeout_seconds': args.case_timeout,
                                   'whole_run_budget_seconds': args.budget_seconds,
                                   'note': 'capture limits, not an official Arena timing campaign'},
              'tests': rows}
    write_report(out, report)
    deadline = time.monotonic() + args.budget_seconds
    for row in rows:
        if row['name'] not in inputs:
            continue
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            row['not_run_reason'] = 'whole-run resource budget exhausted'
            write_report(out, report)
            continue
        name = row['name']
        log = out.joinpath('logs', *safe_parts(name + '.log'))
        result = run_case(binary, inputs[name], log, args.jobs, min(args.case_timeout, remaining))
        row.update(result)
        if result['returncode'] is not None:
            row['status'] = classify(result['returncode'], row['expected'])
        if row['status'] not in ('matched', 'matched_either'):
            row['diagnostic_tail'] = log.read_bytes()[-1600:].decode(errors='replace')
            print(f"{row['status']}: {name}: {row['diagnostic_tail'].strip()}", flush=True)
        write_report(out, report)
    summary = report['summary']
    lines = ['# Actual C1 Arena archive baseline', '',
             f"Source: `{source_revision}`; executable SHA-256: `{report['checker_sha256']}`.",
             f"Arena metadata revision: `{source['arena_revision']}`.",
             f"Archive SHA-256: `{captured['archive_sha256']}`.",
             f"Metadata SHA-256: `{captured['metadata_sha256']}`.", '',
             '**Scope: archive subset, not full-Arena qualification or a public score.**', '',
             '| Outcome | Count |', '|---|---:|']
    lines.extend(f'| {status} | {count} |' for status, count in summary['counts'].items())
    lines += ['', '## Inputs absent from the archive', '']
    lines.extend('- `' + name + '`' for name in summary['not_in_archive'])
    lines += ['', '## Present inputs with capability/resource gaps', '']
    lines.extend('- `' + name + '`' for name in summary['present_input_gaps'])
    lines += ['', 'All input bytes, metadata, logs, the executable and per-input JSON evidence are retained.',
              'Declines remain capability gaps. Timing observations are not performance claims.', '']
    (out / 'summary.md').write_text('\n'.join(lines))
    print(json.dumps({'summary': summary, 'captured_source': captured,
                      'checker_sha256': report['checker_sha256']}, indent=2), flush=True)
    print('\n'.join(lines), flush=True)
    fatal = {'wrong_accept', 'wrong_reject', 'error', 'signal', 'unexpected_exit', 'timeout', 'not_run'}
    return int(any(row['status'] in fatal for row in rows))


if __name__ == '__main__':
    raise SystemExit(main())
