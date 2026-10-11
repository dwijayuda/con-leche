# C1 performance guide

C1 keeps a small owned interface over con-leche's existing checker and proofs.
Its first performance change makes optional statistics a deliberate choice.
Read this guide alongside the executable contract in
[Kernel.lean](../../PskernelC1/Kernel.lean).

## What runs

| Part | Responsibility | Source |
|---|---|---|
| C1 contract | Fix verified mode and arithmetic pins; define acceptance receipts. | [Kernel](../../PskernelC1/Kernel.lean) |
| C1 command line | Read once, check once, compose the receipts, print the result. | [Main](../../PskernelC1/Main.lean) |
| Shared driver | Parse, install declarations, check recorded bodies, drain workers. | [Run](../../ConLeche/Driver/Run.lean) |
| Cached checker | Reuse the existing checking algorithms, memo state and environment. | [Installed](../../ConLeche/Cached/Installed.lean) |
| Model proofs | Establish guarantees for accepted results under `SetTheory`. | [Soundness](../../PskernelC1/Soundness.lean) |

The model module is absent from the executable's imports. Acceptance evidence
is a proposition erased during compilation; composing it needs no second
checker run. The runtime still contains the inherited checker implementation.

At `--jobs=1`, parsing and installation run on the main thread; the check phase
uses one dedicated worker. At higher counts, the existing parallel parser,
installer and check pool run. The CLI defaults to hardware concurrency, so
performance comparisons must set `--jobs` explicitly.

## What disabling statistics changes

The shared driver accepts `collectStats : Bool := true`. The con-leche CLI
keeps that default. C1 passes false unless the user requests `--stats`.
The switch controls instrumentation beside the checker; every successful
result still carries the same `checkDecls` acceptance equation.

| Work | C1 default | C1 with `--stats` |
|---|---|---|
| Per-record statistics clock samples and counter updates | Skipped | Collected |
| Slowest-record bookkeeping and final report collection | Skipped | Collected |
| Statistics formatting, stderr output and peak-RSS file read | Skipped | Performed |
| Parsing, installation, checking and worker draining | Performed | Performed |

The report retains the inherited `con-leche: stats:` line prefix. C1 requests
no progress output. Other callers of the shared driver can request progress,
which retains its own in-flight timestamps even with statistics disabled.

The remaining costs include parsing bytes, preparing the prelude, conversion
and type checking, memo and environment storage, reference counting, thread
scheduling and worker teardown. The existing persistent-marking policy also
remains. Statistics policy branches, a few empty bookkeeping objects and
fixed-cost setup timestamps remain; this change targets repeated telemetry
work, without restructuring the checker or its ownership discipline.

## Reproduce the matched comparison

After both binaries are built in GitHub's Linux CI, run from the repository
root. These commands use committed inputs and execute every checker with a
timeout; the scripts do not build the binaries.

```bash
bash tests/pskernel-c1-stats.sh
python3 tests/c1/perf_smoke.py --repetitions 3 --jobs 1 --timeout 180
```

The [statistics gate](../../tests/pskernel-c1-stats.sh) requires identical
verdicts and diagnostic output, after removing statistics lines, for accepted,
invalid and unsupported inputs at one and two workers. It also checks that
the upstream CLI still reports statistics by default. Its logs are under
`_tmp/c1/stats/`.

The [resource smoke](../../tests/c1/perf_smoke.py) compares three configurations:
con-leche, C1, and C1 with statistics. All use verified mode, the same revision,
input bytes and worker count. It warms up each configuration, rotates their
execution order, and reports repeated user/system time, elapsed time, peak
RSS and, when available, `instructions:u` hardware counts.

Compare **C1 against C1 with statistics** to measure the effect of enabling
telemetry in the same executable. The upstream-CLI comparison also includes
command-line differences. Counters include the identical timing/timeout
wrappers; very small inputs can be dominated by startup costs.

Results are written to `_tmp/c1/perf/report.json` and `summary.md`, with raw
logs alongside them. The JSON records input and binary hashes, revision,
toolchain, individual samples and min/median/max. A later run replaces these
paths, so retain each CI artifact before comparing another worker count.

## How to judge a change

[Measurements](MEASUREMENTS.md) records one CI run's executable sizes, timings,
memory figures and exact gate status. Performance claims need that archived
evidence and its configuration. Shared-runner elapsed time is advisory and
has no pass/fail speed threshold. These smoke inputs do not establish
Mathlib-scale throughput.

Prefer a change whose mechanism and acceptance contract are easy to explain,
whose runtime and proof ownership remain clear, and whose benefit repeats on
representative inputs. When two versions perform similarly, keep the clearer
one. Added caches, extra checker paths or intricate state handling need a
measured benefit sufficient to justify their proof and maintenance cost.
