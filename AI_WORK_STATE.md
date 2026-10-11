# pskernel-c1 work state

Updated: 2026-10-11 UTC (2026-10-12 in Asia/Jakarta).

## Goal and repository

Build a small, fast, model-backed Lean declaration checker in
`dwijayuda/con-leche`, branch `pskernel-c1`. Establish the concrete
acceptance and consistency contract before the executable and optimize
without breaking its proof connection.

The user's latest priority is explainability, readability and
understandability. Keep the source and proof path easy to follow; justify
added complexity with a clear invariant and measured benefit.

Base: `3b37939f0d9d37bfd86299dc92d9a97fbacba29e`.
Toolchain: `leanprover/lean4:v4.35.0-rc3`.
The existing independent `dwijayuda/pskernel` project is separate.

## Implemented source

- `PskernelC1/Kernel.lean`: fixed verified mode and committed pins;
  declaration/chunks entry points, certified results and compositional
  declaration/chunks/stream receipts.
- `PskernelC1/Soundness.lean`: model-existence and consistency corollaries
  for the actual entry points and receipt types, under `SetTheory V`.
- `tests/PskernelC1Tests/Axioms.lean`: thirteen capstone axiom guards.
- `PskernelC1/Main.lean`: small verified-only streaming command line,
  successful-run receipt composition, correct error/decline distinction,
  worker draining and fail-stop runtime configuration.
- Shared driver: optional statistics collection with the existing
  `collectStats := true` default; C1 disables it unless `--stats` is given.
- Linux CI: proof-first build, inherited gates, C1 source/closure and
  verdict checks, telemetry equivalence and matched performance smoke.
- `PSKERNEL_C1.md`: contract, foundations, architecture, usage, performance
  rationale, compatibility limits and pinned primary research sources.
- `docs/pskernel-c1/PROOF_GUIDE.md` and `PERFORMANCE_GUIDE.md`: short source
  reading guides. The CLI names its policy arguments explicitly.

The first implementation reuses the full ConLeche checker. It is an owned
small interface and optimized driver configuration, not a newly minimal
independent implementation of every Lean feature. It adds no semantic
axiom, proof placeholder or second checking pass.

## Proof-first history

`9149092af80b13f34acf25c2f0b2614336a357bf` establishes the executable
acceptance contract, its inherited model corollaries and the axiom audit.
The following implementation commit adds the command line, optional
telemetry and cloud validation. A release qualifies only after CI checks
the proof sources and executable; the existence of a source commit alone
is not validation.

## Validation status

[CI run 38162805999](https://github.com/dwijayuda/con-leche/actions/runs/38162805999)
at `b67440c1e099471269ef30b211ff7f85b46f3098` passed the warning-free C1
proof and thirteen-axiom-audit build, default build, upstream test library,
all 47 C1 CLI cases, eight paired statistics cases, matched measurements
and executable packaging. The standard battery also passed its 470 e2e
and 15 annotation fixtures and worker-count/trusted sweeps. The overall
run failed because the import census omitted the three new C1 modules.
The current source adds that coverage and the readability/package changes.
Each push validates the exact branch head; consult the checks linked from
[draft PR #1](https://github.com/dwijayuda/con-leche/pull/1) for the current
qualification result. A passing earlier revision never qualifies changed
source automatically.

The earlier run found a dependent-match elaboration error in
`certifyResult`; `b67440c1` corrected the refined branch with `rfl`, and
the subsequent proof build passed. Both runs preserved successful module
work in the CI cache.

No local Lean build or checker test has been run; the project workflow uses
GitHub/cloud Linux CI. Static source inspection and lint are separate from
that compiler/runtime validation.

The first C1 measurements are in `docs/pskernel-c1/MEASUREMENTS.md`:
three measured repetitions per fixture/configuration, one worker, no
measurable wall-time speedup and a 77,328-byte smaller executable than
the same-commit original. Instruction counters were unavailable on the
runner. No new public Lean Kernel Arena score is claimed. Measurements
must be read at their exact commit and toolchain; the historical upstream
PERF.md and public Arena snapshot concern their own revisions.

## Required CI evidence

1. Warning-free `lake build PskernelC1Proof PskernelC1Tests`.
2. Warning-free default `lake build` and upstream `lake test`.
3. Existing `tests/arena.sh` gates and suites.
4. C1 runtime import closure and trust-surface gate.
5. C1 acceptance, rejection, decline and error fixtures with one and two
   workers; first failing declaration preserved.
6. Statistics enabled/disabled verdict equivalence and output checks.
7. Paired baseline/C1 measurements and executable artifact with provenance.

The build cache preserves successful dependency work after a failed CI
attempt. Source changes still invalidate Lake's dependency traces.

## Remaining research after the first release

Qualify the actual C1 binary on Lean Kernel Arena at a recorded commit.
Measure Init and Mathlib with controlled resources and retired-instruction
counters before making large-corpus speed claims. Select any deeper
representation or kernel simplification from those measurements, state
its refinement obligation first, then implement it and repair its proofs.

The existing SetTheory premise, semantic model meaning, supported axiom
policy and IO/compiler/runtime trust boundary must remain explicit.
Arbitrary-axiom deduction checking would need a separate conditional
contract and is not enabled by the C1 command line.
