# PSKernel-C1: independent, proof-first kernel architecture and execution plan

Status: active development plan, not a claim of completed implementation.
Decision date: 2026-10-12, Asia/Jakarta.
Repository: `dwijayuda/con-leche`; working branch: `pskernel-c1`.
Qualified inherited baseline: `2be0589fa57b6909b3551afa01e88a9326a75545`.

## 1. Authoritative priorities

Build a correct, capable, independently implemented Lean-compatible declaration checker with a clear proof path to model existence and relative consistency. Performance, explainability, readability, and understandability guide implementation choices.

**Substantial size reduction is an optional optimization objective, not a constraint on any other priority.** There is no percentage-reduction requirement, binary-size ceiling, line-count budget, or release blocker based solely on size. In particular, the earlier suggested 50% reduction threshold is NOT adopted.

Do not remove a capability, weaken an invariant, obscure a proof, introduce an opaque encoding, or accept a performance regression merely to make a size number smaller. A larger implementation is acceptable when it is clearer, faster, more capable, or easier to verify. Report implementation size, dependency closure, proof size, binary size, and execution trust separately.

Correctness cannot be traded for benchmark success. No unsupported assumption becomes an acceptance shortcut. A proposed optimization needs a stated invariant and measured benefit, not a target number of deleted lines.

This is compiler/kernel correctness and formal-methods work on the user's own open-source repository. Differential conformance tests and negative-input tests evaluate untrusted proof terms; this is not offensive-security work.

## 2. Preserve the qualified baseline

The first C1 release fixes ConLeche's checker to verified mode and composes receipts for the actual declaration/chunk/stream pipeline. Its model and consistency results are conditional on `SetTheory V`. It is an inherited implementation, not a new independent checking engine.

At the qualified baseline, the C1 executable is 18,827,936 bytes. The initial small-fixture measurements establish no repeatable speedup. The complete inherited runtime battery runs the upstream executable, whereas the C1-specific cases run C1. Neither is a new public full-Arena qualification of C1.

Keep the baseline history and public contracts intact during development. Do not rewrite the old checker merely to attach the new project name. Do not run the old checker as an invisible production fallback. During the transition it is an explicitly named development oracle and a separately qualified release.

Sources: [baseline PR and evidence](https://github.com/dwijayuda/con-leche/pull/1), [baseline contract](https://github.com/dwijayuda/con-leche/blob/2be0589fa57b6909b3551afa01e88a9326a75545/PskernelC1/Kernel.lean), [baseline soundness](https://github.com/dwijayuda/con-leche/blob/2be0589fa57b6909b3551afa01e88a9326a75545/PskernelC1/Soundness.lean), [baseline CI](https://github.com/dwijayuda/con-leche/actions/runs/38165678404).

## 3. What independence means

The new production acceptance path will own expression/environment representations, inference, conversion, declaration installation, and relevant caching. It must not invoke ConLeche's checker or Lean's C++ checker to establish acceptance.

Reusing mathematical definitions, rule-soundness results, and model proofs is permitted and desirable. Mathematical reuse is not runtime delegation. Initially use Lean for the new implementation to minimize the verification-language bridge; this is implementation independence, not independent compilation or runtime.

A later Rust or other native implementation is permitted when measurements justify its additional bridge and trust obligations. A second backend is not a prerequisite to the first independently implemented release. If the Lean runtime makes a target difficult, investigate the measured bottleneck before changing languages.

The transitional independent package lives under `independent/`. It has its own library/test targets and an import fence. Components remain explicitly experimental until integrated with the declaration checker and its model theorem. A green component proof does not qualify the current CLI as independent.

## 4. Two assurance contracts, one verified core

### 4.1 Model-backed acceptance

For an explicit modeled axiom policy:

    Foundation(V) and AcceptModeled(input, env)
      imply existence of a model of env in V.

The consistency corollary excludes a proof-safe constant of the pinned False type in such an environment. The current foundation is the inherited `SetTheory V` interface. Its premise and the allowed global proof axioms remain separately visible.

No new field named `sound`, no opaque assumed implementation theorem, and no renamed weaker model predicate can replace the proof.

### 4.2 Assumption-relative deduction checking

For arbitrary well-formed input assumptions A:

    AcceptRelative(A, input, env)
      implies a checked derivation under A.

Its semantic consequence is conditional:

    Foundation(V) and a model MA of A and AcceptRelative(A, input, env)
      imply a model of env extending MA.

The derivation theorem must not assume A has a model; the semantic extension theorem does. Record the assumption dependencies actually used. Do not claim to decide consistency of arbitrary assumptions.

An input axiom of type False can be well-formed in the relative interface. That must never produce a model-backed receipt without the impossible corresponding model premise. The two receipt types must not be interchangeable through a flag or an unchecked cast.

This interface is planned, not currently enabled by the C1 command line. Implementing it requires generalizing declaration/environment proofs, not merely disabling the existing axiom check.

### 4.3 Program declarations and proof-safe declarations

Handle the target Lean version's unsafe and partial records explicitly. Distinguish program-only declarations from the proof-safe logical environment, enforce reference restrictions, and prevent proof-safe acceptance from depending on prohibited declarations.

Native-evaluation assumptions and externally supplied declarations must be reported honestly. Type-checking deductions from a native-evaluation axiom is not independent verification of the native computation.

Source: [Lean axioms reference](https://lean-lang.org/doc/reference/latest/Axioms/). Version-specific behavior is fixed by source pins rather than the moving documentation URL.

## 5. Versioned compatibility contract

Keep four independent pins in the evidence: implementation source revision, build toolchain, target Lean semantics/exporter revision, and test-corpus revision or content hash. The compiler pin alone does not identify the semantics of every exported input.

The qualified build toolchain remains `leanprover/lean4:v4.35.0-rc3` until a deliberate, separately validated bump. Investigate 4.35.0-rc4 compatibility without silently changing the baseline's pins.

Coverage must include:

| Family | Required work and proof obligations |
|---|---|
| Universes | Zero, successor, max, imax, parameters, substitution, scope, comparison, and resource outcomes |
| Expressions | All exported core forms, faithful names/indices, binders, substitution and context validity |
| Inference/conversion | Full and infer-only preconditions; beta/delta/iota/zeta, eta, proof irrelevance, projections |
| Definitions/theorems | Ordered installation, body/type checking, opacity, reducibility and environment extension |
| Inductives | Parameters, indices, mutual/nested blocks, positivity, universes, constructors, recursors and elimination restrictions |
| Special support | Quotients, literals, arithmetic pins and justified primitive reductions |
| Axiom/safety policies | Distinct modeled/relative receipts, assumption dependencies, unsafe/partial reference restrictions |
| Input/driver | Faithful decoding, complete declaration coverage, no skipped failures, deterministic commits and correct error categories |

A discovered false acceptance in a reference implementation is not behavior to reproduce. Document the deviation and preserve soundness.

Two concrete semantic issues require dedicated fixtures and proofs:

* The inspected ConLeche rule layer never delta-unfolds theorem bodies. The inspected official 4.35.0-rc4 `constant_info::has_value` still includes theorem values. PR #14896 was draft/unmerged during this research. Do not assume proposed upstream behavior has shipped.
* Semantic equality is not automatically the target kernel's algorithmic conversion relation. In particular, do not introduce an unrestricted transitive conversion closure merely because denotations agree.

Sources: [official declaration source](https://github.com/leanprover/lean4/blob/v4.35.0-rc4/src/kernel/declaration.h), [theorem-opacity proposal](https://github.com/leanprover/lean4/pull/14896), [inherited rules](https://github.com/dwijayuda/con-leche/blob/2be0589fa57b6909b3551afa01e88a9326a75545/ConLeche/Rules/Rel.lean).

## 6. Proof architecture and obligations

The preferred proof path is:

    independent operation
      -> representation/operational refinement
      -> explicit rule derivation
      -> semantic rule soundness
      -> declaration/environment extension
      -> model existence
      -> relative consistency.

The existing rule layer deliberately separates executable bodies from the rule relations. Reuse that boundary where appropriate. It is not a ready-made completeness proof, and its current types/guards still require an explicit representation bridge.

Every component has a contract before optimization. Prove the simple implementation against that contract, then replace it with a measured optimization and repair the refinement. The new optimized body is the subject of the proof; do not retain redundant reference bodies merely to avoid proof repair.

Term-level correctness is insufficient: declaration installation must preserve the stronger invariants about stored types, values, constructors, recursors, and inductive models. Generalizing arbitrary axioms also changes these invariants.

Separate the obligations:

| Obligation | Meaning |
|---|---|
| Input fidelity | Accepted terms/declarations correspond to actual decoded input, not a substituted easier problem |
| Operation soundness | Successful inference, reduction and conversion satisfy the specified judgments |
| Representation correctness | IDs, storage and substitutions decode to the specified terms |
| Environment preservation | Successful installation maintains all premises used by later operations |
| Model theorem | Accepted proof-safe environment has a model under the stated policy/foundation |
| Completeness | Covered successful reference checks can also succeed; accepting nothing is not progress |
| Resource behavior | Timeout, exhaustion, crash and unsupported feature are not mathematical rejection |
| Execution correspondence | Source proofs versus compiler, runtime, IO and scheduling assumptions remain explicit |

For components with a resource bound, distinguish soundness for every returned result from completeness with sufficient resources. Never label empirical coverage a universal completeness theorem.

Sources: [rule soundness](https://github.com/dwijayuda/con-leche/blob/2be0589fa57b6909b3551afa01e88a9326a75545/ConLeche/Model/Rules/Sound.lean), [environment invariant](https://github.com/dwijayuda/con-leche/blob/2be0589fa57b6909b3551afa01e88a9326a75545/ConLeche/Model/Annot/EnvModelM.lean).

## 7. Performance and representation policy

Begin with a clear independent implementation, not an obligatory arena, closure evaluator, or fixed line budget. Evaluate compact term IDs, immutable environments, per-declaration temporary storage, delayed substitution, and cache redesign against measurements and proof cost.

For compact IDs, prove valid decoding and acyclicity before using them. For temporary storage, prove that persistent objects cannot retain reclaimed references. Hash equality never establishes expression equality. Unequal pointers/IDs never establish definitional inequality. Cache keys and validity must account for all relevant environment, context, inference-grade and policy information.

Use one verified acceptance algorithm; diagnostics and statistics must not affect its verdict. Establish a sound, understandable serial path before adding more scheduling complexity. Parallel work must not omit a declaration, conceal a worker failure, or change the committed first failure.

Report wall/CPU time, memory and available instruction counts with commands, binary hashes, input hashes, worker counts, build/link configuration and repetitions. Shared-runner wall times are observations, not definitive speed claims. Size is reported but has no hard pass/fail threshold.

The existence of compact Rust checkers or fast closure-based checkers is evidence that alternatives deserve measurement, not proof that any specific design will improve C1. [Con-ron](https://github.com/leanprover/con-ron) is a useful implementation/refinement precedent; its translator and runtime assumptions must not be hidden in comparisons.

## 8. Arena evidence discipline

The actual C1 executable must be tested, not merely the inherited upstream executable. Give each run an exact checker revision, executable hash, toolchain, suite source/hash and per-input outcome.

The public downloadable archive omits large tests and does not represent the entire Arena suite. Capture its hash and test inventory, enumerate omitted tests from the public metadata where available, and label the run as an archive subset. A captured snapshot is reproducible evidence only while its bytes are retained; moving URLs are not immutable pins.

The runner must distinguish accept, reject, unsupported, error, timeout, signal termination, missing input and not-run. No test-name decline allowlist or blanket zero-wrong-results rule can justify full qualification. For an expected reject, a decline is still a capability gap.

A public score belongs to the exact checker revision tested there. Local differential testing does not publish a score. Tests with no prescribed outcome should still be run and reported, but not miscounted as scored positive/negative cases.

A full qualification requires every prescribed-outcome case in the pinned full corpus, including large workloads. Download failures, omitted inputs, resource limits and missing corpora stay visible. Do not build every external corpus on every small source edit; use a fast incremental gate and a separate full-corpus qualification lane.

Sources: [Arena protocol](https://github.com/leanprover/lean-kernel-arena), [live suite and download limitations](https://arena.lean-lang.org/). Counts on the live site are observations, not permanent constants in the implementation.

## 9. Execution milestones

| ID | Work | Completion evidence |
|---|---|---|
| C1-N0 | Freeze baseline and revise priorities | Qualified source preserved; this plan and work state committed; no hard size threshold |
| C1-N1 | Measure actual C1 capability | Per-input C1 report with hashes; full versus subset scope explicit; all gaps inventoried |
| C1-N2 | Establish independent foundational components | Owned executable functions, checked laws, regression tests, import/trust fence |
| C1-N3 | Implement independent inference/conversion | Explicit representation bridge, rule derivations, positive/negative coverage and resource semantics |
| C1-N4 | Implement declaration/inductive installation | Environment-extension proof, all supported declaration families and input fidelity |
| C1-N5 | Add assumption-relative capability | Verified deduction contract, assumption ledger, conditional model extension, safety isolation |
| C1-N6 | Integrate independent CLI | No inherited checking fallback; parser/driver acceptance connected to the model theorem |
| C1-N7 | Qualify full capability and optimize | Full pinned Arena, target-version matrix, controlled large-corpus results, explicit trust boundary |

N5's contract work begins before its runtime feature. Individual well-specified components may proceed alongside N1; do not wait for every large benchmark to start basic verified implementation. Progress is tracked by delivered capabilities and discharged obligations, not by theorem counts or a speculative global percentage.

The first independent component is universe syntax/evaluation/substitution and a sound normalization/equality fast path. An inconclusive fast path returns unknown, never unequal. Full universe comparison, source-name interning, expression checking, and the ConLeche model bridge remain later obligations.

## 10. Development and release rules

Use GitHub/cloud Linux CI. No Desktop Commander and no unrelated project branches. Preserve commits and do not merge the draft PR without a separate decision. Stage explicit paths and use a fast-forward/expected-head lease when updating refs.

No proof placeholders or new semantic axioms on the active implementation path. Audit actual theorem dependencies and explicit hypotheses. Keep the baseline's proof gate, runtime tests and trust checks. Add independent-package import, trust and axiom gates rather than silently excluding new code from review.

Every change includes its current scope, proof obligation, negative conformance behavior and validation status. Keep `AI_WORK_STATE.md` current. Failed or pending CI is reported as such. Green historical CI never qualifies later code automatically.

A release may be larger than the old one. It may not silently be less correct, less capable, harder to understand, or dependent on an unreported checking oracle just to achieve a size target.

## 11. Next exact imax proof strategy (2026-10-12)

The finite first-occurrence name codec and proof-only source comparison bridge are now implemented. Duplicate source occurrences share their first internal ID, and new trailing names do not renumber existing IDs. The source bridge builds a finite table from actual levels, proves roundtrip and semantic evaluation for all five level constructors, and transports sound equal/different polynomial outcomes. That is input fidelity, not yet a full kernel conversion proof.

For general `imax`, use a semantically exact sign partition, not ad-hoc rewrite exceptions. Every parameter is either zero or successor. Under a fixed sign assignment, the zero/nonzero value of every `imax` right operand is determined and the branch can be compiled into a max/successor polynomial. Prove the translation for *all* residual parameter assignments. Finite exhaustive sign enumeration can then be a complete reference, although it may be exponential. A production algorithm must preserve the contract and justify resource costs. See [Lean level normalization issue 12747](https://github.com/leanprover/lean4/issues/12747) and Arena's [imax-leq](https://arena.lean-lang.org/test/bugs/level-imax-leq/) and [imax-normalization](https://arena.lean-lang.org/test/bugs/level-imax-normalization/) negative conformance cases.

Semantic universe equality is not necessarily identical to the pinned official Lean kernel's algorithmic conversion relation. Measure and specify both before integrating this comparator into acceptance. C1 is a checker built by the pinned Lean toolchain, not a self-hosted compiler; proof checks do not verify that compiler, runtime or physical file IO.

## 12. Universe reference-completeness milestone

The independently implemented universe semantics now has a complete (potentially exponential) reference comparison for all constructors, including arbitrary nested `imax`, and its direct source bridge constructs a finite table from the actual exported names. Both proof paths are anchored to the concrete algorithms, with soundness and completeness shown separately and negative equality outcomes justified; no assumption was introduced that arbitrary source IDs can be mapped injectively by an unproved codec. These results solve the **semantic reference** problem, not the target Lean kernel's potentially stricter, versioned **operational conversion** problem. The latter must have its own stated contract and differential qualification, not be replaced by extra extensional equalities. The reference and its proof artifacts must remain outside the production checking loop until a bounded algorithm and an actual checking integration theorem exist.

The next dependency is independent expression syntax and explicit binder operations, with scope and substitution invariants before any reduction/inference code. Both self-hosting and binary shrinking are outside this correctness-critical path: C1 is an independent checker implemented in Lean and bootstrapped with the pinned Lean compiler/runtime.
