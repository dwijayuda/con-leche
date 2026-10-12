# Independent C1 implementation checkpoint — 2026-10-12

## Decision implemented

The independent, proof-first development has started in `dwijayuda/con-leche`, branch `pskernel-c1`. The [architecture document](../../PSKERNEL_C1_NEXT_ARCHITECTURE.md) is committed, and [AI_WORK_STATE.md](../../AI_WORK_STATE.md) tracks the current obligations.

**Size reduction is optional, not a constraint on correctness, capability, proofs, performance, or readability.** No 50% reduction threshold, binary ceiling, or line-count budget was adopted.

The existing qualified checker is preserved. The new code lives in a separate package and is not an unproved replacement for the production acceptance path.

## Independent implementation and formal evidence

Source `a2476126606850347c8a209f9ebd8adb56fecd1c` contains the checked implementation described below.

| Delivered result | Evidence and exact scope |
|---|---|
| Independent universe functions | All five constructors, substitution, renaming, normalization and a positive equality fast path |
| Polynomial universe comparison | Complete for arbitrary zero/parameter/successor/max expressions, with both positive and negative verdict proofs |
| Soundness and completeness separated | Positive acceptance soundness, negative-result soundness, fragment completeness and absence of unknown results in that fragment |
| Regression coverage | 36 guards and four theorem examples, all compiled successfully |
| Proof assumptions | 16 named capstones audited; exact observed subsets of the three allowed standard foundations pinned |
| Input-fidelity bridge | Seven proof-only theorems connect the basic representation/fast path to inherited universe semantics; source-name correspondence is an explicit premise |

The [independent proof run 38173757176](https://github.com/dwijayuda/con-leche/actions/runs/38173757176) and [semantic-bridge run 38173757189](https://github.com/dwijayuda/con-leche/actions/runs/38173757189) completed successfully at that source. The independent proof artifact is [11714304653](https://github.com/dwijayuda/con-leche/actions/runs/38173757176/artifacts/11714304653), ZIP digest `b5c3b0110d4c65fd9e01ad9cb8930c3b7f5077e6b931d50b7f5416b684922def`.

The new source imports no inherited checking implementation and has no added semantic axiom, proof placeholder or unchecked replacement. Its proof-only bridge intentionally reuses mathematical semantics. This establishes component correctness, not a complete independently implemented declaration checker.

## Actual C1 capability baseline

The [separate Arena report](ARENA_BASELINE_20261012.md) records the actual production C1 binary, unchanged from the qualified inherited release. It attempted all 196 inputs in a hash-verified public archive against a 223-test metadata inventory.

| Outcome | Count |
|---|---:|
| Prescribed verdict matched | 187 |
| Declined | 8 |
| Timed out at the recorded 60-second limit | 1 |
| Absent from the public archive | 27 |

Six declines stopped at non-standard axioms, two at unsafe/partial declaration records. The timeout was `perf/magma-list-deep-n36`. No incorrect accept/reject result was recorded among completed inputs. The timeout remains a failed resource qualification, and absent inputs are not counted as checked. This is not a new public Arena score or a full-suite pass.

## Validation infrastructure

The root import census now recognizes that `independent/` has its own Lake namespace. It keeps all existing root dependency/fallback checks, requires the independent package manifest, and runs that package's source fence. The independent proof workflow remains separate required evidence.

A nondeterministic statistics test was corrected to match the driver's documented nonblocking snapshot: zero completed samples are valid only when omitted unfinished workers are disclosed. Four deterministic report-contract tests cover both valid shapes and invalid omissions. Checker code and expected verdicts were not changed.

## Remaining implementation work

General imax comparison and a proved source-name interner are the next foundational obligations. Expression/context representation, inference, conversion, declaration/inductive environment preservation, arbitrary-assumption deduction checking, and the new checker-to-model integration remain open.

Model-backed acceptance must remain distinct from assumption-relative deduction checking. Full Lean capability cannot be obtained by disabling the current axiom checks while retaining the old unconditional acceptance claim.

The production CLI still uses the inherited verified checker. Its model-existence and consistency corollaries remain conditional on `SetTheory V`, with compiler/runtime/IO/platform trust boundaries explicit. No speedup or substantial size reduction has been demonstrated by this checkpoint.
