# PSKernel-C1 — authoritative AI work state

Updated: 2026-10-12 (Asia/Jakarta)
Repository: `dwijayuda/con-leche`; active branch: `pskernel-c1`.
PR: [#1](https://github.com/dwijayuda/con-leche/pull/1), draft and unmerged.
This project is separate from `dwijayuda/pskernel` and PSKernel-Fast.

## Mission and non-negotiable boundaries

Deliver an independently implemented, Lean 4-compatible, high-performance kernel checker with explainable architecture, readable code and a verified connection to semantic model existence and relative consistency. The full input and declaration capabilities of a pinned official Lean version and the complete Lean Kernel Arena are intended acceptance targets. **Correctness and theorems cannot be sacrificed for performance or coverage.**

**Substantial size reduction is OPTIONAL; it is NOT an acceptance constraint, percentage target, binary ceiling, or reason to sacrifice capability, proof correctness, performance or readability.**

Do not mistake an independent universe/expression component for a completed independent checker. Do not mistake model-backed acceptance under a specific axiom policy for deduction checking with arbitrary axioms. The latter requires separate conditional model/derivation theorems. Do not silently run the original ConLeche checker as a fallback.

The primary design source is [PSKERNEL_C1_NEXT_ARCHITECTURE.md](PSKERNEL_C1_NEXT_ARCHITECTURE.md). The qualified original release is documented by [PSKERNEL_C1.md](PSKERNEL_C1.md), and the historic initial state is preserved in [WORK_STATE_BASELINE.md](docs/pskernel-c1/WORK_STATE_BASELINE.md). Source implementation guides: [independent README](independent/README.md) and [bridge README](bridge/pskernel-c1/README.md).

## Preserved qualified production checker

Baseline source `2be0589fa57b6909b3551afa01e88a9326a75545` passed [CI 38165678404](https://github.com/dwijayuda/con-leche/actions/runs/38165678404) on `leanprover/lean4:v4.35.0-rc3`. Its actual CLI still invokes `ConLeche.Cached.checkDecls .verified`. Its model existence and pinned `False`/`Empty` consistency corollaries are conditional on `SetTheory V` and the modeled axiom policy. Compiler, runtime, physical IO and platform are distinct execution trust boundaries.

Binary at the qualified source: 18,827,936 bytes. No repeatable speedup or substantial size reduction was demonstrated, and none is required just to continue development.

The actual C1 binary's captured public Arena archive run [38171872724](https://github.com/dwijayuda/con-leche/actions/runs/38171872724) attempted 196 cases from a 223-entry metadata snapshot: **187 correct prescribed verdicts, 8 unsupported declines, 1 timeout and 27 metadata inputs not in the downloadable archive**. The eight declines stopped at six non-standard axioms and two unsafe/partial declarations; `perf/magma-list-deep-n36` timed out under its 60s per-input resource profile. No wrong accept/reject verdict was reported in completed cases, but the run FAILED qualification. This is neither a full-suite pass nor a public Arena score. Full corpus and root-cause follow-up remain mandatory. See [ARENA_BASELINE_20261012.md](docs/pskernel-c1/ARENA_BASELINE_20261012.md).

## Independent implementation and verified capability

The experimental `independent/` Lake package imports no ConLeche checking implementation and no external package. Its runtime implementation is written in Lean, built by a pinned Lean toolchain; this is **implementation independence**, not independent runtime/compiler verification or self-hosting.

### Universes, source identity and semantic comparison

- Owned all-five-constructor universe syntax, evaluation, simultaneous substitution, renaming and normalizer with proofs over ALL parameter valuations.
- Sound and complete polynomial comparator for every zero/parameter/succ/max universe, with proofs for both positive and negative judgments.
- Finite first-occurrence parameter-name codec. Its six proofs establish roundtrip, membership, absence behavior, nonaliasing and index stability under extension.
- A fixed-sign `imax` compiler whose zero tests and polynomial denotations are proved exact. The independent **`compareExhaustive_correct`** theorem makes exhaustive finite sign enumeration equivalent to semantic equality for arbitrary nested `imax`. The negative outcome is justified too. This reference can be EXPONENTIAL and is NOT a production kernel-conversion strategy.
- The proof-only `UniverseBridge.lean` transports polynomial and exhaustive comparisons to actual exported `ConLeche.Level` input through the proved finite codec, including sound negative outcomes. `compareSourceExact_correct` proves total semantic equivalence for the source representation.
- Semantic universe equality does NOT automatically coincide with strict pinned official Lean kernel algorithmic conversion. A separately verified and measured operational comparator is still required.

### Expressions, scope, substitution and abstraction

- Own ten-constructor `Expr` syntax, hierarchical names, literals and untrusted binder annotation data. These are structurally represented; no unvalidated annotation becomes a proof.
- Structural `Expr.Scoped` and executable `checkScoped` proved equivalent. Scoped `fvar idx ty` requires `ty` closed against loose bvars and containing only fvar levels earlier than `idx`.
- Independent de Bruijn raising and general capture-safe binder instantiation have proofs of scope preservation for open replacements. Fvar type annotations are correctly ATOMIC, following the inherited checker. Additional proofs establish lifting closed replacement terms does nothing.
- Independent binder closure `abstractAt` and `abstract1` replace a fresh fvar by its binder index while preserving scope, including all binders, lets and projections.
- The **proof-only** [ExprBridge.lean](bridge/pskernel-c1/ExprBridge.lean) maps all ten independent expression forms to the actual reference representation and proves: (i) independent scope implies the reference bvar-scope test, (ii) independent instantiation agrees with `ConLeche.Expr.instantiate1` for a proved bvar-closed replacement, and (iii) independent abstraction agrees with `ConLeche.Expr.abstract1` at every cursor.
- These are checked operational **component refinement** theorems, NOT yet full expression inference/conversion or the independent kernel model/consistency theorem.

### Exact recent cloud evidence

| Scope | Commit | Workflow |
|---|---|---|
| Independent universes, sign/exhaustive proof, and early 31-capstone audit | `e9ea555` | [38179387294](https://github.com/dwijayuda/con-leche/actions/runs/38179387294), passed |
| Full source universe semantic bridge | `bee34a4` | [38179595828](https://github.com/dwijayuda/con-leche/actions/runs/38179595828), passed |
| Independent expression and closed-lift operations | `d7965be` | [38180568264](https://github.com/dwijayuda/con-leche/actions/runs/38180568264), passed |
| Independent abstraction plus its scope proofs | `181cc040` | [38195107171](https://github.com/dwijayuda/con-leche/actions/runs/38195107171), passed |
| Universe semantic bridge at `181cc040` | `181cc040` | [38195107173](https://github.com/dwijayuda/con-leche/actions/runs/38195107173), passed |
| All six expression refinement proof obligations | `181cc040` | [38195107226](https://github.com/dwijayuda/con-leche/actions/runs/38195107226), passed |

The complete root CI [38195107167](https://github.com/dwijayuda/con-leche/actions/runs/38195107167) was still running when inspected. Do not infer a green result until it completes. Later commits must be qualified at their exact SHA, not merely by referring to these older runs.

## Current milestone status

| ID | Status |
|---|---|
| C1-N0: architecture, contracts and priorities | Implemented; size reduction explicitly nonbinding |
| C1-N1: actual-binary Arena baseline | Captured archive and gaps; full corpus and nine observed archive gaps unresolved |
| C1-N2: independent foundational semantics | Independent universe and expression operations and several scoped/semantic refinement bridges verified; incomplete as a checker foundation |
| C1-N3: independent full inference and algorithmic conversion | NOT implemented |
| C1-N4: declaration installation, inductives and model preservation | NOT implemented |
| C1-N5: assumption-relative deduction checking | Contracts designed; independent proof and implementation NOT complete |
| C1-N6: independent runtime CLI with genuine model theorem | NOT implemented; production CLI still inherited |
| C1-N7: full Arena and large-corpus qualification, optimization | NOT complete |

## Next coherent subsystem work

1. Complete the hierarchical expression-name input-fidelity and binder-zero validation contracts. Never equate independently decoded expression metadata with a valid source declaration without a proof; duplicates and unordered lists can normalize.
2. Establish a bound-variable opening/closing correspondence under explicit freshness, scoping and equal-annotation hypotheses; introduce no universal roundtrip that is false for open/aliased input.
3. Create the first independently implemented inference/conversion judgments for closed, well-formed expressions, then prove an actual bridge to the existing rule-level semantics before enabling any acceptance path.
4. Develop a reference-compatible, appropriately bounded operational universe comparator. Maintain complete semantics as a separate test/proof oracle; avoid exponential brute force on the production hot path.
5. Generalize axiom assumptions only through a separate relative deduction contract and conditional model extension; never weaken the existing model-backed receipts.
6. Continue declaration installation, inductives, complete Arena acquisition, large-input benchmarks, and executable/model integration until the complete proof-first checker qualifies.

## Workflow

GitHub-first cloud Linux CI only; no Desktop Commander, unrelated repositories, branch deletion or premature PR merge. Commit checkpoints on `pskernel-c1` using an expected-head lease. Run focused proof tests, then root CI; preserve the canonical `AI_WORK_STATE.md` and architecture documentation. Never count a declined input, timeout, absent corpus, proof-only component or unqualified commit as a verified complete checker. No `sorry`, `admit`, arbitrary axioms or unchecked acceptance shortcuts in new proof paths.
