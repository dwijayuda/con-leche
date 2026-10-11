# PSKernel-C1 work state

Updated: 2026-10-12, Asia/Jakarta.
Repository: `dwijayuda/con-leche`; branch: `pskernel-c1`.
This project is separate from `dwijayuda/pskernel` and PSKernel-Fast.

## Current user direction

Proceed with an independently implemented Lean-compatible kernel, using proof-first architecture and a real connection to model existence and relative consistency. Preserve correctness, capability, performance, explainability, readability and understandability.

**Substantial size reduction is not a strict priority and must not constrain the other priorities.** No mandatory percentage reduction, binary-size ceiling or line-count budget. The previous suggested 50% threshold is not adopted. Measure size, but never weaken proofs, reduce coverage or obscure code to satisfy it.

Authoritative execution document: [PSKERNEL_C1_NEXT_ARCHITECTURE.md](PSKERNEL_C1_NEXT_ARCHITECTURE.md).
Current shipped interface: [PSKERNEL_C1.md](PSKERNEL_C1.md).
Historical work state is preserved verbatim in [WORK_STATE_BASELINE.md](docs/pskernel-c1/WORK_STATE_BASELINE.md).

## Qualified inherited baseline

Source: `2be0589fa57b6909b3551afa01e88a9326a75545`.
Toolchain: `leanprover/lean4:v4.35.0-rc3`.
Upstream starting point: `3b37939f0d9d37bfd86299dc92d9a97fbacba29e`.
[CI run 38165678404](https://github.com/dwijayuda/con-leche/actions/runs/38165678404) completed successfully at the qualified source.
[PR #1](https://github.com/dwijayuda/con-leche/pull/1) remains draft and unmerged.

The baseline has concrete declaration/chunks/stream receipts, thirteen owned capstone axiom guards, model existence and False/Empty corollaries conditional on `SetTheory V`, a streaming verified-only CLI, optional statistics, and provenance packaging. It reuses `ConLeche.Cached.checkDecls` and is NOT independently implemented.

Recorded baseline evidence: warning-free proof/default/test builds; all 47 C1 CLI cases; eight statistics pairs; inherited 470 e2e and 15 annotation cases; import/trust gates; matched small-fixture measurements; packaged executable of 18,827,936 bytes. No repeatable speedup or new public Arena score was established. The complete inherited runtime battery runs the upstream executable, not C1.

## Active execution

| Milestone | Current status |
|---|---|
| C1-N0: priorities, architecture, baseline | Plan and updated state prepared; baseline preserved |
| C1-N1: actual C1 capability inventory | In progress: add a hash-recording runner; archive subsets must never be called the full Arena |
| C1-N2: independent foundation | In progress: implement universe operations with semantic preservation proofs and isolated import/trust tests |
| C1-N3: independent inference/conversion | Not implemented |
| C1-N4: declaration/inductive model extension | Not implemented |
| C1-N5: assumption-relative checking | Contract specified in plan; runtime and generalized proof not implemented |
| C1-N6: independent CLI/model integration | Not implemented; current CLI still inherited |
| C1-N7: full-corpus qualification/optimization | Not completed; no hard size target |

The next independent components live in `independent/`, a separate library package using the enclosing pinned Lean toolchain. This is a meaningful separation from the qualified runtime, not a second checking pass. Experimental components do not change the shipped acceptance path until their integration proof is checked.

## Proof and capability boundaries

Keep model-backed acceptance separate from assumption-relative deduction checking. A model for arbitrary axioms is an additional premise of the semantic extension theorem, not something obtained by toggling an allow-all flag. Never give a modeled receipt to an arbitrary axiom environment without its model proof.

An independent operation proof is not full checker consistency. Universe evaluation/normalization correctness does not imply complete universe comparison, correct input name interning, expression inference or declaration installation. Those bridges remain explicit tasks.

A rule-refinement theorem proves sound acceptance, not universal completeness. Retain successful-reference coverage and resource-aware completeness as separate obligations. Unknown/exhaustion must not be converted to mathematical rejection.

## Immediate next actions

1. Commit the architecture and priority change; retain baseline work-state history.
2. Add an independent universe representation, evaluation and substitution laws, a sound equality fast path, and regression/axiom/import tests.
3. Run the actual C1 executable on a captured Arena archive with per-input hashes/outcomes and explicit missing/full-suite coverage status.
4. Inspect cloud CI results, fix root causes without weakening tests or contracts, and record exact qualified revisions.
5. Continue with source-name/universe bridging and a complete universe comparator, then expression representation and the rule-level bridge.

## Workflow

GitHub/cloud Linux CI only for Lean builds and checker execution. No Desktop Commander. Do not change unrelated repositories or delete branches. Use expected-head leases for commits. Do not merge PR #1 automatically.

All source changes require fresh qualification. The successful baseline run above does not qualify newly added code. Static inspection, checked proofs, executed test cases and full-suite qualification are distinct evidence levels.

## Known follow-up findings

The prior analysis identified current Arena policy declines for non-standard axioms and unsafe/partial records. These are hypotheses for capability work until the actual C1 executable is run on the captured inputs; do not transplant another revision's score.

Theorem opacity differs between the inherited rule layer and the inspected official 4.35.0-rc4 kernel. Do not assume proposed upstream PR #14896 has merged. Add targeted conformance cases and a versioned proof decision.

The full Arena contains large tests omitted from the downloadable archive. A successful subset gate must publish its scope and exclusions. Large-corpus timings, retired instructions and complete independent-kernel qualification remain outstanding.
