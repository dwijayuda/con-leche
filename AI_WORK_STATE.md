# PSKernel-C1 work state

Updated: 2026-10-12, Asia/Jakarta.
Repository: `dwijayuda/con-leche`; branch: `pskernel-c1`.
Separate from `dwijayuda/pskernel` and PSKernel-Fast. PR #1 remains draft and unmerged.

## Authoritative priorities

Build an independently implemented, Lean-compatible checker with correctness, full capability, performance, explainability/readability and a proof-first connection to model existence and relative consistency.

**Substantial size reduction is optional and must not constrain the other priorities.** There is no mandatory percentage reduction, binary-size ceiling, or line-count budget. The earlier proposed 50% threshold is explicitly NOT adopted. Do not weaken a theorem, drop a capability, obscure code or sacrifice useful performance to reduce size.

Execution plan: [PSKERNEL_C1_NEXT_ARCHITECTURE.md](PSKERNEL_C1_NEXT_ARCHITECTURE.md).
Shipped inherited interface: [PSKERNEL_C1.md](PSKERNEL_C1.md).
Historical state preserved verbatim: [WORK_STATE_BASELINE.md](docs/pskernel-c1/WORK_STATE_BASELINE.md).
Actual C1 capability evidence: [ARENA_BASELINE_20261012.md](docs/pskernel-c1/ARENA_BASELINE_20261012.md).

## Qualified inherited baseline

Source `2be0589fa57b6909b3551afa01e88a9326a75545`; upstream starting point `3b37939f0d9d37bfd86299dc92d9a97fbacba29e`; build toolchain `leanprover/lean4:v4.35.0-rc3`.
[Run 38165678404](https://github.com/dwijayuda/con-leche/actions/runs/38165678404) qualified that revision.

The production CLI still reuses `ConLeche.Cached.checkDecls .verified`. Its declaration/chunks/stream receipts, thirteen owned capstone audits, and model/False/Empty corollaries remain conditional on `SetTheory V`. **It is not yet independently implemented.** The new package does not change the shipped acceptance path.

Baseline binary: 18,827,936 bytes; SHA-256 `ebf410be6194e7184813658f76ae85d67513fe6ea093a2e058e08e15620844e9`. No repeatable speedup has been established. The inherited full runtime battery tests the upstream executable; the C1-specific cases test C1.

## Work delivered in this development session

### Architecture and priority decision

Committed `PSKERNEL_C1_NEXT_ARCHITECTURE.md`, preserving the original baseline and separating modeled acceptance from assumption-relative deduction checking. The plan defines independent-runtime, rule-refinement, environment/model, completeness, versioning, Arena and execution-trust obligations. No hard size goal is adopted.

### Independent universe foundation

The separate `independent/` Lake package owns its functions and imports no ConLeche/Lean checker implementation. `Universe.lean` provides all five universe constructors, evaluation, simultaneous substitution, renaming, conservative normalization and a sound positive equality fast path. Eleven contracts and twenty regression guards were verified in [run 38171096293](https://github.com/dwijayuda/con-leche/actions/runs/38171096293), source `563eb55698a0501af78a8caf184b2900a3e386a6`.

The source/import/trust fence scans all independent Lean files, prohibits proof placeholders and unchecked implementation replacements, and checks named theorem footprints. Basic theorem footprints are pinned exactly to observed subsets of the standard `propext`, `Classical.choice`, `Quot.sound` foundations.

### Proof-only semantic and input-fidelity bridge

`bridge/pskernel-c1/UniverseBridge.lean` translates independent universes to/from the inherited representation and proves seven evaluation/normalization/positive-equality/roundtrip contracts. Source equality explicitly requires a faithful codec or per-input roundtrip equations. The actual finite source-name interner is not implemented yet.

This bridge was verified in [run 38172175657](https://github.com/dwijayuda/con-leche/actions/runs/38172175657) at `e955caa00efcb79a3a5aa68cf23d24ab3c8cd64f`. It is proof-only and does not call the inherited comparison algorithm. The optional, unrelated Mathlib bridge also passed [run 38172175540](https://github.com/dwijayuda/con-leche/actions/runs/38172175540) at that revision.

### Complete max/successor fragment comparator — validation in progress

`UniversePolynomial.lean` implements a transparent finite maximum of a constant and parameter-offset atoms. Duplicate atoms are permitted; dominance is checked explicitly. No hash or presumed canonical-form invariant establishes equality.

`UniversePolynomialProofs.lean` contains operation preservation, dominance soundness/completeness via a separating assignment, sound positive/negative verdicts, and completeness/conclusive-result contracts for the imax-free zero/parameter/successor/max fragment. Sixteen new regression guards cover commutativity, associativity, idempotence, successor distribution, dominated offsets and constant-floor distinctions.

Initial cloud checking exposed proof-language issues, not changed test verdicts: arithmetic automation did not unfold the explicit `Nat.max` implementation, `by_contra` was not available in this minimal import environment, and rewriting a generic maximum lemma needed an explicit equality chain. These were corrected using named natural-number laws and explicit contradiction. **The latest correction is awaiting fresh CI; do not call the new polynomial package qualified until its proof, tests and axiom audit pass.**

General `imax` remains unknown in the polynomial comparator. The basic fast path can still prove reflexive/normalized equalities involving imax. Neither function alone is a complete arbitrary-universe comparator. The new five polynomial capstone footprints are constrained to the allowed foundations and must be pinned to their exact observed subsets after the first successful run.

### Actual-binary Arena baseline

[Run 38171872724](https://github.com/dwijayuda/con-leche/actions/runs/38171872724), source `87ffd9d725bbd1b28e43e97d5872306489885c58`, ran the actual C1 executable against 196 captured archive inputs. All input hashes/outcomes matched pinned public metadata.

Results: **187 matched verdicts, eight declines, one 60-second timeout, and 27 metadata cases absent from the archive**. No incorrect accept/reject verdict was recorded on completed cases. The workflow correctly failed on `perf/magma-list-deep-n36` timing out; it is not a passing qualification.

Both metadata and archive hashes are committed in `tests/c1/arena-source.json`; all captured bytes, binary and per-case evidence are in [artifact 11714189593](https://github.com/dwijayuda/con-leche/actions/runs/38171872724/artifacts/11714189593). Ten Python evidence-harness tests passed. See the dedicated report for exact hashes, missing inputs and each stopping point.

The six non-standard-axiom declines and two safety-record declines confirm contract/capability work remains. Do not weaken the existing model receipt merely to accept these cases. The first resource profile and timeout remain immutable evidence even if a later diagnostic uses a larger budget.

### Validation infrastructure corrections

The C1 statistics test previously assumed a rejected parallel install always reports a completed timing sample. The actual documented driver snapshots only finished workers; zero samples are valid when unfinished workers are disclosed. The test now checks both legitimate shapes and four deterministic positive/negative report-contract cases. Runtime checker behavior and expected verdicts were unchanged. The eight paired tests and all 47 C1 verdict cases subsequently passed.

The root import census initially interpreted the nested package as `independent.PskernelC1Independent.*`, which are not its module names. Commit `c5d1a2a40e1aff5508885306956a92a818549e77` preserves all root census/public/fallback rules, requires the separate package manifest, and runs its complete source fence before separating that package's namespace. Its dedicated proof workflow remains required. A one-shot exact-source maintenance workflow made the narrow edit and removed itself.

The optional Mathlib bridge workflow now follows its actual package path rather than every file under `bridge/`. The C1 semantic bridge has its own lightweight verification workflow; no mathematical bridge gate was disabled.

## Milestone status

| Milestone | Status |
|---|---|
| C1-N0: priorities/architecture/baseline | Implemented and committed |
| C1-N1: actual C1 capability inventory | Archive subset captured and reported; full corpus and observed gaps remain |
| C1-N2: independent foundation | Basic universe laws and semantic bridge checked; polynomial extension undergoing final validation |
| C1-N3: independent inference/conversion | Not implemented |
| C1-N4: declaration/inductive model extension | Not implemented |
| C1-N5: assumption-relative checking | Contract specified; generalized proof and runtime not implemented |
| C1-N6: independent CLI/model integration | Not implemented; current CLI remains inherited |
| C1-N7: full qualification/optimization | Not completed; no hard size target |

## Next actions

1. Inspect the current independent proof, semantic-bridge and root CI results. Fix proof elaboration at the actual statement, never by weakening its claim or test expectations. Pin the five new capstone footprints after a successful check.
2. Record the exact newly qualified component revision and remaining Arena failure separately. Do not describe the whole branch as full-Arena-qualified.
3. Complete general universe comparison with explicit zero/positive case reasoning for imax; preserve soundness and completeness independently. An unknown result is never inequality.
4. Implement and prove finite source-name interning/input roundtrip, then expression/context representation and the rule-level bridge.
5. Proceed to declaration/inductive environment preservation and assumption-relative contracts; integrate only after the actual new acceptance path connects to the model theorem.

## Workflow and non-goals

GitHub/cloud Linux CI for Lean builds and checker execution; no Desktop Commander, unrelated project edits, branch deletion or automatic PR merge. Use expected-head leases. Preserve all existing model meanings and explicit hypotheses.

Component proofs do not establish a full independent kernel. Semantic universe equality is not a substitute for all operational conversion obligations. Source proofs do not verify the compiler, runtime primitives, IO, platform or scheduling by themselves. No size/performance or public Arena score claim is inferred from source counts or historical checks.
