# PSKernel-C1 proof-only integration bridges

These bridges **are not runtime acceptance fallbacks** and cannot replace independent checking or the model/consistency proof.

## Universe semantics

[UniverseBridge.lean](UniverseBridge.lean) connects all five independent universe constructors to the inherited semantic evaluation of source `ConLeche.Level`. Finite first-occurrence name tables encode every parameter actually present. Their proofs establish exact roundtrip and semantic representation, sound positive and negative polynomial results, and a semantically complete exhaustive `imax` source comparison. It is potentially exponential and not the official kernel's operational equality algorithm.

Run [C1 universe semantic bridge CI](https://github.com/dwijayuda/con-leche/actions/workflows/c1-universe-bridge.yml). Its source/readout audit pins twenty named theorem dependency footprints.

## Expression scope and binder operations

[ExprBridge.lean](ExprBridge.lean) translates the independently defined hierarchical names, universe levels, all ten expression constructors, both literals, and binder-zero metadata into the inherited reference expression format.

Six proved contracts establish that independent scope implies the reference bound-variable scope test; that independent capture-safe substitution agrees with reference `ConLeche.Expr.instantiate1` when the replacement is provably closed against loose bound variables; and that independent binder closing agrees with reference `ConLeche.Expr.abstract1` at arbitrary binder cursors. This closes an operational representation gap without importing inherited checker execution into the independent runtime.

The source `BinderZero.allZero` annotation is not inherently canonical. Translating it with the reference `PropWhen.ifAllZero` normalizes parameter sets, and does NOT alone prove arbitrary original binder metadata valid. Input fidelity, annotation canonicality and checker-level semantics must be justified before accepting a declaration.

Run [C1 expression operational bridge CI](https://github.com/dwijayuda/con-leche/actions/workflows/c1-expression-bridge.yml). Its six named proof capstones passed at [38195107226](https://github.com/dwijayuda/con-leche/actions/runs/38195107226). The current bridge is NOT yet a proof of independent type inference, definitional equality, declaration installation, model existence or full Lean compatibility.

## Trust boundary

The bridge proofs run under the pinned Lean 4.35.0-rc3 kernel/toolchain. They are source-level proofs about actual Lean functions. Compiler code generation, Lean's runtime, native primitives, physical IO, concurrency and hardware execution remain separately reported trust assumptions.

See [PSKERNEL_C1_NEXT_ARCHITECTURE.md](../../PSKERNEL_C1_NEXT_ARCHITECTURE.md) for the full execution plan. Smaller code or binary size is optional and never a constraint on correctness or capability.
