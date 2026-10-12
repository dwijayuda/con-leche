# C1 measurements: 2026-10-11

This page records one completed resource smoke from
[CI run 38162805999](https://github.com/dwijayuda/con-leche/actions/runs/38162805999).
All 27 measured checker invocations and nine warmups accepted their inputs.
The results below are observations on that runner; they support no speedup claim.

## Provenance and configuration

| Item | Recorded value |
|---|---|
| Source revision | `b67440c1e099471269ef30b211ff7f85b46f3098` |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` |
| Job | [`build-and-gates`, 114539078419](https://github.com/dwijayuda/con-leche/actions/runs/38162805999/job/114539078419) |
| Runner | GitHub-hosted Ubuntu 24.04.5; image `ubuntu-24.04`, version `20261004.327.1` |
| Benchmark interval | 2026-10-11, approximately 18:14:56–18:15:04 UTC |
| Checking mode and workers | `--verified --jobs=1` in every configuration |
| Repetitions | Three measured runs plus one excluded warmup per fixture/configuration |

The command recorded in the job was:

```bash
python3 tests/c1/perf_smoke.py --repetitions 3 --jobs 1
```

The script's default timeout was 180 seconds per checker invocation. It rotated
configuration order between repetitions. The `con-leche` baseline was built
from the **same revision** as C1, including the shared-driver changes.
`c1` and `c1-stats` used the same executable; only `--stats` differed.
See the [benchmark source at this revision](https://github.com/dwijayuda/con-leche/blob/b67440c1e099471269ef30b211ff7f85b46f3098/tests/c1/perf_smoke.py).

The fixture labels identify `good/init-prelude.ndjson` and
`good/perf/let-ladder.ndjson` from the committed Arena archive, and
`tests/e2e/pinstall_ok.ndjson`. The last is labelled `parallel-install`, but
this measurement used **one worker**; its label describes the fixture.

## Observed executable sizes

These are executable file sizes before packaging, as printed by the
[resource smoke in the job log](https://github.com/dwijayuda/con-leche/actions/runs/38162805999/job/114539078419).

| Executable | Bytes | SHA-256 |
|---|---:|---|
| `con-leche` | 18,905,264 | `6ec16f02748913727e90f80a577ceff3752f130f830745d0d8c4558b36542086` |
| `pskernel-c1` | 18,827,936 | `ebf410be6194e7184813658f76ae85d67513fe6ea093a2e058e08e15620844e9` |

The `c1-stats` configuration has the same size and hash as `pskernel-c1`.
These binaries contain the inherited checker; the small owned C1 interface
does not imply a correspondingly small implementation or proof development.

## Observed timing and memory

All entries are medians of the three measured runs, excluding warmups. Times
retain the log's two-decimal precision. `Peak RSS` is `/usr/bin/time`'s `%M`
for an individual invocation; the table reports the **median of those peaks**.
For example, C1's `init-prelude` peaks were 29,964, 29,968 and 30,240 KiB:
the table value is 29,968 KiB, while the largest measured peak was 30,240 KiB.

| Fixture | Configuration | Median elapsed s | Median user CPU s | Median peak RSS KiB |
|---|---|---:|---:|---:|
| `init-prelude` | `con-leche` | 0.31 | 0.31 | 32,156 |
| `init-prelude` | `c1` | 0.31 | 0.30 | 29,968 |
| `init-prelude` | `c1-stats` | 0.31 | 0.30 | 30,168 |
| `let-ladder` | `con-leche` | 0.23 | 0.22 | 227,276 |
| `let-ladder` | `c1` | 0.23 | 0.22 | 227,368 |
| `let-ladder` | `c1-stats` | 0.23 | 0.21 | 227,460 |
| `parallel-install` | `con-leche` | 0.01 | 0.01 | 25,708 |
| `parallel-install` | `c1` | 0.01 | 0.01 | 23,420 |
| `parallel-install` | `c1-stats` | 0.02 | 0.01 | 23,492 |

The [job log](https://github.com/dwijayuda/con-leche/actions/runs/38162805999/job/114539078419)
prints these aggregates and every elapsed-time/peak-RSS sample. Hardware
`instructions:u` counts were **unavailable**: the runner's perf diagnostic
reported `perf_event_paranoid=4` and restricted access without the required
`CAP_PERFMON`, `CAP_SYS_PTRACE` or `CAP_SYS_ADMIN` capability. No instruction
count or instruction-based performance conclusion is reported.

## Checks completed in the same run

The job log records successful warning-gated proof/axiom builds, `lake build`
and `lake test`; 47 C1 CLI cases with zero failures; and eight paired statistics
cases plus the upstream-default check with zero failures. The upstream fixture
battery reported 470/470 e2e and 15/15 annotation cases as expected, together
with matching serial and parallel sweeps. Its Arena good-input acceptance
count was 90/92.

The **overall job failed** at the public-import census: it did not yet include
`PskernelC1.Kernel`, `PskernelC1.Main` and `PskernelC1.Soundness`. That integration
failure is part of this revision's status; the individual results above are
not a claim that the complete CI job passed.

## Evidence and interpretation

The [measurement artifact](https://github.com/dwijayuda/con-leche/actions/runs/38162805999/artifacts/11710888159)
contains `_tmp/c1/perf/report.json`, `summary.md`, raw logs and the C1 package.
The JSON includes input hashes, commands, individual samples and min/median/max.
The separate [CI logs artifact](https://github.com/dwijayuda/con-leche/actions/runs/38162805999/artifacts/11711067584)
preserves the build, test and benchmark transcripts.

Elapsed medians agree across all configurations on `init-prelude` and
`let-ladder`. The remaining fixture is at the 0.01–0.02-second scale. Three
short runs on this host do not establish a repeatable telemetry speedup,
parallel scaling or Mathlib throughput. Keep the clear shared implementation;
require representative measurements before adding more runtime or proof
complexity. The [performance guide](PERFORMANCE_GUIDE.md) explains the method
and the costs that remain.
