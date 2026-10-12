# Actual C1 Arena archive baseline — 2026-10-12 Jakarta

This report records the actual `pskernel-c1` executable, not the upstream `con-leche` executable and not another checker's public score.

**Result: capability/resource gaps remain. This is not a full-Arena pass.**

## Provenance

- Source: `87ffd9d725bbd1b28e43e97d5872306489885c58`.
- Toolchain: `leanprover/lean4:v4.35.0-rc3`.
- Executable: 18,827,936 bytes; SHA-256 `ebf410be6194e7184813658f76ae85d67513fe6ea093a2e058e08e15620844e9` (same bytes as the qualified inherited baseline).
- [Run 38171872724](https://github.com/dwijayuda/con-leche/actions/runs/38171872724), [job 114565977974](https://github.com/dwijayuda/con-leche/actions/runs/38171872724/job/114565977974).
- [Complete captured evidence, artifact 11714189593](https://github.com/dwijayuda/con-leche/actions/runs/38171872724/artifacts/11714189593): archive, metadata, all available input bytes, executable, per-input JSON report and logs.
- Artifact ZIP digest reported by GitHub: `536b10e0b08d15c0ff7dc1cb8e66a8b9dea3d446721b7c5175b8b9b1b3aba874`.
- Arena revision: `0454b9707259b59e18f97a065adbf14f1f61a355`, published 2026-10-11 19:39:59 UTC.
- Metadata SHA-256: `7f5d9c60430bad574692c9ff05d5c07fb7a43125329d0ac81792d0f638510306`.
- Archive SHA-256: `8c70846d4dfd77b0697036fa2d69daf3dbe13e3a9280629cce1dfe9d480ee9a7`.

Every available input was checked against its individual metadata hash and expected outcome. Ten evidence-harness regression tests passed, as did the model/proof audit and executable build before this run. The corpus hash and metadata hash are now committed in `tests/c1/arena-source.json`.

## Outcomes and resource profile

The command used one worker, `--verified`, a 60-second per-case limit, and a 900-second overall checking budget. These are an explicit capture resource profile, not the public Arena's instruction-count campaign.

| Outcome | Count |
|---|---:|
| Prescribed verdict matched | 187 |
| Unsupported/declined | 8 |
| Timed out | 1 |
| Metadata tests absent from archive | 27 |
| Total metadata inventory | 223 |
| Total archive inputs attempted | 196 |

No incorrect accept/reject verdict, crash, or unexpected exit was recorded on the completed inputs. This does not establish correctness on absent inputs or a successful result for the timeout. The workflow intentionally exits unsuccessfully for a timeout; the result has not been reclassified as a pass.

## Capability gaps

| Test | Observed stopping point |
|---|---|
| `other/level-index-out-of-order` | Non-standard axiom `foo` |
| `other/sparse-name-index` | Non-standard axiom `foo` |
| `tutorial/034_letTypeDep` | Non-standard axiom `aDepProp` |
| `tutorial/035_letRed` | Non-standard axiom `aProp` |
| `tutorial/047_inductBadNonSort2` | Non-standard axiom `aType` before the expected rejection |
| `tutorial/107_proofIrrelevanceUnderBinder` | Non-standard axiom `aType` |
| `tutorial/140_falseFromUnsafe` | Definition record with safety `unsafe` |
| `tutorial/141_falseFromPartial` | Definition record with safety `partial` |
| `perf/magma-list-deep-n36` | No verdict before the 60-second limit |

These observations support prioritizing the assumption-relative and safety-declaration contracts. They do not justify accepting arbitrary axioms under the existing model-backed receipt. Parser-related filenames do not establish parser defects when the actual stopping point is an axiom.

The timeout is a measured performance/resource gap. A future diagnostic may use a larger explicitly recorded budget, but it must preserve this first result and must not change the original test's meaning or claim a speedup. Investigate the algorithm and phase behavior rather than adding a test-name exception.

## Unavailable inputs

The 27 metadata entries absent from this public archive are:

`cedar`, `con-leche`, `cslib`, `init`, `mathlib`, `navier-stokes-euler`, `std`,
`perf/magma-string-n4`, `perf/magma-string-pair-n9`,
`corner-cases/alg-conv-trans-acc`, `corner-cases/alg-conv-trans-acc-left`,
`corner-cases/alg-conv-trans-acc-right`, `corner-cases/alg-conv-trans-quot`,
`corner-cases/alg-conv-trans-quot-left`, `corner-cases/alg-conv-trans-quot-left-def`,
`corner-cases/alg-conv-trans-quot-right`, `corner-cases/eta-ctor`,
`corner-cases/eta-rule-k`, `corner-cases/imax-right-successor`,
`corner-cases/let-value-type-mismatch`, `corner-cases/nested-nonuniform-param`,
`corner-cases/positivity-whnf`, `corner-cases/proj-maybe-prop`,
`corner-cases/proj-maybe-prop-past`, `corner-cases/proof-param-swap`,
`corner-cases/subject-reduction-redex`, `corner-cases/subject-reduction-reduct`.

Some are unscored corner cases rather than large benchmarks. None were silently counted as checked. A full qualification requires the complete pinned corpus, including large library workloads and separately reported unscored cases.

## What remains

C1-N1 now has an actual-binary, per-input baseline for the public archive. Full-corpus acquisition/qualification and the nine observed capability/resource gaps remain open. Independent universe-component proofs are a separate milestone and do not change this inherited executable's results.
