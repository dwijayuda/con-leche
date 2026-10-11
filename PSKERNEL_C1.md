# pskernel-c1

`pskernel-c1` is a verified-only Lean declaration checker built on the
model-proved ConLeche implementation. Its first version establishes an
owned acceptance contract and consistency corollaries, then connects a
small streaming command line to that contract. It checks raw `lean4export`
NDJSON streams.

The starting revision is ConLeche
[`3b37939f0d9d37bfd86299dc92d9a97fbacba29e`](https://github.com/leanprover/con-leche/commit/3b37939f0d9d37bfd86299dc92d9a97fbacba29e).
The compiler, embedded prelude and operation pins remain on the coherent
`leanprover/lean4:v4.35.0-rc3` baseline. The executable accepts only the
model-proved `.verified` mode. `--verified` is an optional explicit spelling
for integration with checker harnesses.

## Build the proof first

The Linux CI workflow builds the C1 proof and axiom audit before the C1
executable. These are also the commands for reproducing that sequence in
a Linux build environment:

```sh
lake build PskernelC1Proof PskernelC1Tests
lake build pskernel-c1
timeout 120 .lake/build/bin/pskernel-c1 --jobs=1 INPUT.ndjson
```

`lake build pskernel-c1` builds the executable's dependency closure. It does
not import the set-model proof or the parked completeness development into
the runtime. An ordinary `lake build` continues to validate the upstream
default targets and the C1 proof and executable. `lake test` retains the
upstream suite; CI separately builds `PskernelC1Tests` to check the C1
capstones' axiom footprint.

The CI download contains a Linux tarball with the executable, original
license, this guide, toolchain pin, source revision and executable checksum.
After extraction, verify `sha256sum -c SHA256SUMS` and run `./pskernel-c1`.
Draft branches are checked on pushes; opening a draft pull request reuses
that push validation instead of starting a duplicate cold build.

The executable has four operational options:

| Option | Behavior |
|---|---|
| `--jobs=N` | Use a positive worker count; the default is hardware concurrency. |
| `--stats` | Collect and print the inherited phase and per-record statistics. |
| `--verified` | Explicitly select the sole checking mode. |
| `--help`, `--version` | Print usage or the C1 version. |

Exactly one input path is required for a checking run. `--` permits an input
path beginning with a hyphen. Diagnostics retain the shared driver's
`con-leche: stats:` prefix when statistics are enabled; the C1 verdict and
error messages use `pskernel-c1:`.

| Exit | Meaning |
|---|---|
| 0 | The checking run accepted, or a requested help/version command completed. |
| 1 | The checker positively rejected an invalid declaration or inconsistent record. |
| 2 | The checker positively detected an unsupported feature. |
| 3 | Usage, malformed input, IO or internal error. |

Runtime panics abort the process and do not produce a checker verdict.
Use a time limit for checker runs. A timeout is a resource failure, never
evidence of acceptance or a mathematical rejection.

## What the proof says

The concrete declaration entry point is
[`PskernelC1.checkDeclarations`](PskernelC1/Kernel.lean):

```lean
def checkDeclarations (ds : Array Declaration) : CheckResult :=
  Cached.checkDecls .verified natOpPinSets ds
```

Its owned model theorem in
[`PskernelC1.Soundness`](PskernelC1/Soundness.lean) has this statement:

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (ds : Array Declaration) (env : Env)
    (accepted : checkDeclarations ds = .ok env) :
    Nonempty (ConLeche.Model V env)
```

This is a corollary of the existing model theorem for the actual checker
function. There is no new axiom asserting that a future implementation is
sound. The global proof dependencies are audited separately from the
explicit `SetTheory V` premise.

The API also composes the complete pure input path:

```lean
def checkChunks (chunks : List ByteArray) : CheckResult := do
  let pre ← Frontend.builtinPreludeE
  let parsed ← Frontend.parseChunks chunks
  checkDeclarations (Frontend.preparePrelude pre parsed.decls)
```

Successful environments are wrapped in one of three evidence-bearing
types:

| Type | Evidence supplied by a value |
|---|---|
| `Accepted ds` | This declaration checker returned this environment on `ds`. |
| `AcceptedChunks chunks` | This parser/prelude/checker pipeline returned this environment on these chunks. |
| `AcceptedStream` | There exists a chunk sequence for which the pipeline returned this environment. |

`checkCertified` and `checkChunksCertified` attach evidence to the result
actually computed. Their erasure theorems cover both successful and error
results. The evidence is in `Prop` and is erased by Lean's compiler.

The streaming CLI uses the third type. The parser already returns an
existential witness for its chunks, and the shared driver already returns
evidence that its result equals the verified declaration fold. The C1 CLI
combines these with the successful prelude equation. The only checking
success path calls `printAccepted` with the resulting `AcceptedStream`.
The chunks need not be retained, and the checker need not run twice.

The proof layer derives model existence and the absence of a stored
constant with the pinned `False` type from each receipt. It also proves
the `Empty` constant corollary, excludes a theorem record of type `False`
from successful declarations, and excludes any successful parser output
containing such a theorem record from the complete chunks pipeline.
The separately named JSON-template corollary preserves the upstream
template predicate; it is not a characterization of every textual spelling
of `False`.

### The foundation and trust boundary

All model and consistency statements are conditional on `SetTheory V`.
That interface supplies the set-theoretic foundation and universe
structure; this project does not discharge it by defining a field named
`sound`. The thirteen C1 capstones are pinned by
[`tests/PskernelC1Tests/Axioms.lean`](tests/PskernelC1Tests/Axioms.lean) to
the inherited proof dependencies `propext`, `Classical.choice` and
`Quot.sound`. The explicit set-theory premise is still present even when
that axiom audit succeeds.

The accepted model is the upstream `ConLeche.Model` with its existing
meaning. The checker-to-model argument uses the inherited stronger
environment invariants and rule-soundness proofs. A future representation
change must preserve the required denotation and computation properties,
including the relevant environment and recursor obligations. Replacing
these by a weaker predicate with the same name is not a verification step.

Lean checks the proof terms. The produced native executable still depends
on Lean's compiler, its runtime and allowed runtime primitives, the platform
and file IO. `AcceptedStream` connects the parser result to a chunk witness;
the physical filename-to-bytes relationship remains an IO boundary. This
is a conditional consistency guarantee for C1's accepted declarations,
not a verification of Lean's separate C++ kernel binary.

## Architecture and size

| Layer | Location | Responsibility |
|---|---|---|
| Owned executable contract | `PskernelC1/Kernel.lean` | Fixed verified mode and pins; concrete check functions and receipts. |
| Owned proof layer | `PskernelC1/Soundness.lean` | Model and consistency corollaries for those functions and receipts. |
| Owned command line | `PskernelC1/Main.lean` | Flags, streaming IO, receipt composition and verdicts. |
| Shared implementation | `ConLeche/Kernel`, `Cached`, `Frontend`, `Driver` | Existing verified checking, parsing, indexing, caches and parallel scheduling. |
| Shared metatheory | `ConLeche/Rules`, `Verify`, `Semantics`, `Model`, `SetTheory` | Existing implementation bridges and semantic proof. |

The owned API is small. The full inherited checker is retained to preserve
its declaration coverage and proof chain. This first version therefore
does not claim a newly minimal independent kernel. The import-closure gate
reports the actual runtime source extent, and the performance artifact
reports executable size; both distinguish C1's thin interface from its
dependencies.

The runtime contract imports implementation modules only. The command line
may use the shared driver's model-free verification modules, while the
model and set-theory tiers remain outside its import closure. The C1 source
gate checks that transitive boundary. The existing trust-surface gate also
scans C1 files without adding an escape allowance for them.

## Performance change in C1

The shared driver gains a `collectStats` option whose default is `true`,
preserving the original command's behavior. C1 passes `false` unless
`--stats` is requested. The disabled path skips per-record telemetry
clocks, worker-statistics accumulation and the final statistics report.
The checker functions, declaration order, cache rules, model premises and
proof-carrying result type are unchanged by this option.

This targets concrete avoidable work while retaining the existing
reference-counting optimizations, dedicated check-worker heap and parallel
install/check architecture. The serial and parallel paths use the same
driver bodies with configuration; there is no duplicate checker retained
solely to avoid repairing a proof.

CI compares the original command, C1 with telemetry disabled and C1 with
telemetry enabled on the same inputs and toolchain. Verdict equivalence is
a gate. Timing is advisory on shared GitHub runners. The benchmark records
wall and CPU time, peak RSS and binary size, and records retired
instructions if the runner permits the performance counter. Missing
counters remain explicitly unavailable. A measured improvement on a small
fixture is not a claim of a universal speedup on Mathlib.

## Compatibility and Arena

C1 inherits the supported declaration language of this pinned verified
checker. The upstream model policy admits its supported standard axioms
and declines arbitrary added axioms. C1 currently has no interface for
supplying models of additional axioms.
An arbitrary declaration `axiom bad : False` cannot be admitted under an
unconditional model-existence guarantee. Supporting deductions relative to
arbitrary assumptions would require a separately stated conditional
contract.

The research snapshot of Lean Kernel Arena tested a different pinned
ConLeche revision, `67f04630`, with `--verified --jobs=4`. Its declined
cases included custom axioms and unsafe/partial declaration records. Those
declines are distinct from wrong acceptance or rejection, and an Arena
score for that revision is not a score for C1. The C1 CI fixture suite
validates specified local behavior; publication of a new Arena score
requires an actual Arena run on the C1 commit.

## Why this route was chosen

We chose the existing model-proved implementation to minimize new semantic
proof work for a useful first checker. The original C++ Lean
kernel is a valuable behavior and performance reference, but proving that
implementation directly would add a language and implementation bridge.
Starting a fresh minimal calculus would reduce the initial code while
leaving broad Lean declaration compatibility to be proved later.

Con-ron demonstrates another viable route: a Rust-oriented Lean twin,
an Aeneas-translated implementation and a refinement into ConLeche. That
architecture is valuable if a different runtime representation justifies
the extra bridge. C1 starts with the existing Lean implementation so it can
acquire an actual checked acceptance contract before paying that cost.

Future optimizations should follow the same order:

1. State the precise acceptance or representation contract against the
   inherited semantics.
2. Prove the new implementation refines that contract, including errors
   and ordering where relevant.
3. Run the proof and trust gates before qualifying a release binary.
4. Keep a performance change only when matched measurements justify its
   complexity and resource behavior.

## Primary research sources

- [ConLeche model and stream capstones, pinned baseline](https://github.com/leanprover/con-leche/blob/3b37939f0d9d37bfd86299dc92d9a97fbacba29e/ConLeche/MainTheorem.lean).
- [ConLeche set-theory interface](https://github.com/leanprover/con-leche/blob/3b37939f0d9d37bfd86299dc92d9a97fbacba29e/ConLeche/SetTheory/Core.lean).
- [ConLeche rule relation](https://github.com/leanprover/con-leche/blob/3b37939f0d9d37bfd86299dc92d9a97fbacba29e/ConLeche/Rules/Rel.lean) and [rule soundness](https://github.com/leanprover/con-leche/blob/3b37939f0d9d37bfd86299dc92d9a97fbacba29e/ConLeche/Model/Rules/Sound.lean).
- [ConLeche stronger environment invariant](https://github.com/leanprover/con-leche/blob/3b37939f0d9d37bfd86299dc92d9a97fbacba29e/ConLeche/Model/Annot/EnvModelM.lean).
- [Con-ron capstone, researched revision](https://github.com/leanprover/con-ron/blob/64a2172a01276aa049220200bac11c075316230f/proof/ConRon/Capstone.lean) and [implementation/proof architecture](https://github.com/leanprover/con-ron/blob/64a2172a01276aa049220200bac11c075316230f/OVERVIEW.md).
- [Official Lean kernel type checker, researched revision](https://github.com/leanprover/lean4/blob/c29b6dda4f7c20e3eeaa717c4e565663c5cfa364/src/kernel/type_checker.cpp).
- [lean4lean implementation axiom audit](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Axioms.lean) and [separate lean4lean-model development](https://github.com/digama0/lean4lean-model).
- [Lean Kernel Arena protocol and checker configurations](https://github.com/leanprover/lean-kernel-arena).

See [AI_WORK_STATE.md](AI_WORK_STATE.md) for the current commit, CI evidence,
measured results and remaining work. Source statements and tests are the
authority for the implemented guarantee.
