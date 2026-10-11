# PSKernel-C1 work state

Updated: 2026-10-12, Asia/Jakarta.
Repository: `dwijayuda/con-leche`; branch: `pskernel-c1`.
Separate from `dwijayuda/pskernel` and PSKernel-Fast. PR #1 remains draft and unmerged.

## Authoritative priorities

Build an independently implemented, Lean-compatible checker with correctness, full capability, performance, explainability/readability and a proof-first connection to model existence and relative consistency.

**Substantial size reduction is optional and must not constrain the other priorities.** No mandatory percentage reduction, binary-size ceiling, or line-count budget. The earlier proposed 50% threshold is explicitly NOT adopted. Never weaken a theorem, drop a capability, obscure code or sacrifice useful performance to reduce size.

Execution plan: [PSKERNEL_C1_NEXT_ARCHITECTURE.md](PSKERNEL_C1_NEXT_ARCHITECTURE.md).
Implementation checkpoint: [IMPLEMENTATION_CHECKPOINT_20261012.md](docs/pskernel-c1/IMPLEMENTATION_CHECKPOINT_20261012.md).
Shipped interface: [PSKERNEL_C1.md](PSKERNEL_C1.md).
Historical state: [WORK_STATE_BASELINE.md](docs/pskernel-c1/WORK_STATE_BASELINE.md).
Actual C1 capability evidence: [ARENA_BASELINE_20261012.md](docs/pskernel-c1/ARENA_BASELINE_20261012.md).

## Validated implementation checkpoint

The original polynomial-component baseline passed at **`a2476126606850347c8a209f9ebd8adb56fecd1c`**. New checks are recorded separately:

| Validation | Result and exact run |
|---|---|
| Independent library, proofs, tests and 16 capstone audits | Passed, [38173757176](https://github.com/dwijayuda/con-leche/actions/runs/38173757176) |
| Seven-theorem initial universe bridge | Passed, [38173757189](https://github.com/dwijayuda/con-leche/actions/runs/38173757189) |
| Finite name codec and 22 independent axiom guards | Passed, [38178368518](https://github.com/dwijayuda/con-leche/actions/runs/38178368518) at `0c75c9e6` |
| Actual finite source bridge: 15 theorems | Passed, [38178500807](https://github.com/dwijayuda/con-leche/actions/runs/38178500807) at `f1d5574a` |
| Complete root CI, including import audits and inherited standard battery | Passed, [38173757192](https://github.com/dwijayuda/con-leche/actions/runs/38173757192) |

The audit/documentation checkpoint following that source pins the observed theorem dependencies without modifying any Lean function, theorem statement or regression expectation. Its own workflow results must still be read at its exact revision. A historical passing run does not automatically qualify changed sources.

**This is a qualified component/development checkpoint, not full-Arena qualification or a complete independently implemented kernel.**

## Preserved production checker

The original qualified source is `2be0589fa57b6909b3551afa01e88a9326a75545`, [run 38165678404](https://github.com/dwijayuda/con-leche/actions/runs/38165678404). Upstream starting point: `3b37939f0d9d37bfd86299dc92d9a97fbacba29e`. The build toolchain remains `leanprover/lean4:v4.35.0-rc3`.

The production CLI still calls `ConLeche.Cached.checkDecls .verified`. Its declaration/chunks/stream receipts, thirteen owned capstone guards, and model/False/Empty corollaries remain conditional on `SetTheory V`. **The production acceptance path is not yet independently implemented.** Experimental components do not silently replace or bypass it.

The current production binary remains 18,827,936 bytes, SHA-256 `ebf410be6194e7184813658f76ae85d67513fe6ea093a2e058e08e15620844e9`. No repeatable speedup or substantial size reduction has been demonstrated. The inherited standard runtime battery tests the upstream executable; the C1-specific and new actual-Arena cases test C1 itself.

## Implemented independent components

### Basic universes

The separate `independent/` Lake package owns all five universe constructors, evaluation, simultaneous substitution, renaming, conservative normalization and a positive equality fast path. It imports no ConLeche or Lean checker implementation and has no external package dependencies.

`UniverseProofs.lean` proves eleven contracts over every parameter assignment, including an explicit semantically equivalent input pair for which the fast path returns unknown. Unknown is not inequality.

### Complete max/successor fragment

`UniversePolynomial.lean` represents a finite maximum of a constant and parameter-offset atoms. Duplicate atoms are allowed; comparison checks dominance explicitly rather than relying on hashes or an assumed unique normal form.

`UniversePolynomialProofs.lean` establishes evaluation preservation, dominance soundness/completeness using a separating parameter assignment, sound positive and negative comparator results, fragment completeness, and conclusive results for arbitrary zero/parameter/successor/max expressions.

**All current proofs passed**, together with **36 regression guards and four theorem examples**. The [independent evidence artifact 11714304653](https://github.com/dwijayuda/con-leche/actions/runs/38173757176/artifacts/11714304653) records the logs and source hashes. The implementation is a readable correctness baseline; it has not been shown faster than existing checkers.

General imax comparison remains open. The polynomial comparator returns unknown outside its fragment; the basic normalization fast path establishes some additional imax equalities. Neither function alone is a complete arbitrary-universe comparator.

### Proof-only semantic and input-fidelity bridge

`bridge/pskernel-c1/UniverseBridge.lean` proves seven contracts connecting the basic independent representation, normalization and positive fast path to inherited universe semantics. Source equality requires a faithful name codec or concrete per-input roundtrip equations.

The adapter is proof-only, imports no inherited comparison algorithm, and leaves ConLeche outside the independent runtime package. The generic finite codec and source-polynomial bridge are checked; integrating an actual independent checking algorithm remains open. These component bridges are not the full declaration/environment/model theorem.

### Proof assumptions

All **22 independent capstone footprints are pinned exactly** to their observed subsets of `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholder or added semantic axiom is accepted.

Among the five new capstones, `toPolynomial_sound`, `comparePolynomial_sound`, and `comparePolynomial_decides` use `propext` and `Quot.sound`. `comparePolynomial_different` and `comparePolynomial_complete` additionally use `Classical.choice`. The existing eleven exact pins are preserved.

## Actual C1 Arena baseline: capability/resource gaps

[Run 38171872724](https://github.com/dwijayuda/con-leche/actions/runs/38171872724), source `87ffd9d725bbd1b28e43e97d5872306489885c58`, attempted the actual C1 binary on all 196 captured public-archive inputs. Every input's digest and expected outcome matched the pinned metadata.

Results: **187 matched verdicts, eight declines, one 60-second timeout, and 27 metadata cases absent from the archive**. No incorrect accept/reject verdict was recorded on completed cases. The workflow correctly failed for `perf/magma-list-deep-n36` timing out; this remains a failed resource qualification, not a full-suite pass.

Six declines stopped at non-standard axioms; two stopped at unsafe/partial definition records. The absent entries include large corpora and unscored corner cases, all enumerated in the report. No missing input, decline or timeout was counted as a successful check.

Metadata and archive hashes are committed in `tests/c1/arena-source.json`. [Artifact 11714189593](https://github.com/dwijayuda/con-leche/actions/runs/38171872724/artifacts/11714189593) retains the exact archive, metadata, input bytes, executable, per-input JSON results and logs. Ten evidence-harness tests passed. No new public Arena score was submitted.

Do not weaken the modeled receipt to accept arbitrary axioms. Assumption-relative deduction checking needs its own derivation contract and a model-extension theorem conditional on a model of those assumptions. A larger future diagnostic budget must preserve, not overwrite, the first timeout record.

## Validation infrastructure corrections

The C1 telemetry test previously presumed rejected parallel installs always report a completed timing sample. The documented driver snapshots only finished workers. The test now permits zero samples only when omitted unfinished workers are disclosed and the top list is empty; four deterministic positive/negative report-contract cases exercise this rule. Runtime code and expected checker verdicts were unchanged. All 47 CLI cases and eight statistics pairs passed.

The root import census now handles `independent/` as its own Lake package rather than inventing `independent.PskernelC1Independent.*` module names. Commit `c5d1a2a40e1aff5508885306956a92a818549e77` preserves all root dependency/public/fallback checks, requires the separate manifest and runs the complete independent source fence. Its dedicated proof job remains required. The one-shot exact-source maintenance workflow removed itself.

The optional Mathlib bridge workflow now follows its actual package path, while C1's semantic bridge has a dedicated lightweight job. The unchanged Mathlib bridge passed [run 38172175540](https://github.com/dwijayuda/con-leche/actions/runs/38172175540). No mathematical bridge gate was disabled.

Initial proof elaboration issues were repaired with correct module-stage imports, named natural-number laws, explicit contradiction and an explicit maximum equality chain. No theorem statement, algorithm verdict, or regression expectation was weakened to obtain green checks.

## Milestones

| Milestone | Status |
|---|---|
| C1-N0: priorities/architecture/baseline | Implemented and committed |
| C1-N1: actual capability inventory | Archive captured; full corpus and nine observed gaps remain |
| C1-N2: independent foundation | Universe laws, polynomial fragment, finite input codec and source bridge checked; imax and kernel-level conversion remain |
| C1-N3: independent inference/conversion | Not implemented |
| C1-N4: declaration/inductive model extension | Not implemented |
| C1-N5: assumption-relative checking | Contract specified; generalized proof/runtime not implemented |
| C1-N6: independent CLI/model integration | Not implemented; production CLI remains inherited |
| C1-N7: full qualification/optimization | Not completed; no hard size target |

## Next implementation actions

Complete general imax comparison using explicit zero/positive cases and distinct soundness/completeness proofs. Integrate the already checked finite source codec into a future checker acceptance path. Proceed to expression/context operations, inference/conversion rules, and declaration/inductive environment preservation.

Implement assumption-relative checking only with its distinct derivation theorem and conditional model extension. Integrate the independent CLI only when its actual acceptance path connects to the model theorem. Keep full-corpus acquisition and the recorded performance case as explicit qualification work rather than running expensive corpora on every small source edit.

## Workflow and trust boundary

Use GitHub/cloud Linux CI for Lean builds and checker execution. No Desktop Commander, unrelated project edits, branch deletion, or automatic PR merge. Use expected-head leases.

Component proofs are not a full independent-kernel consistency theorem. Semantic universe equality does not replace all operational conversion obligations. Source proofs do not themselves verify the compiler, runtime primitives, physical IO, platform or scheduling. Keep model meanings, explicit hypotheses and this trust boundary visible.

## Current finite-source milestone (2026-10-12)

The independent `NameCodec` returns the first occurrence of each source name in a finite list and no name for an invalid index. Six proved contracts include decoding fidelity, existence, missing-name rejection, injectivity, and stable IDs on append. It does not depend on ConLeche checking code. The proof-only `UniverseBridge` now builds a finite table from actual exported level expressions; eight additional theorems prove encoding roundtrip and semantics for all five constructors, encode coverage and sound source-level equal/different results. All fifteen bridge capstones passed at [38178500807](https://github.com/dwijayuda/con-leche/actions/runs/38178500807). The root CI at this exact revision was running when recorded; later revisions need their own checks.

Next, formalize an exact sign-case decomposition for arbitrary imax; cover each universe parameter's zero/successor branch and compile the resulting problem to the proved max/successor polynomial comparator. Prove semantic equivalence and completeness without assuming the procedure is efficient. An exponential complete reference belongs in proof/development, not automatically the production hot path. Strict official Lean conversion and semantic equality must remain separate contracts.

This project is a checker, not a self-host compiler. It is built by a pinned Lean toolchain; native compiler/runtime and input IO remain trusted boundaries. Size reduction remains optional and never blocks correctness, capability or readability.
