# Independent C1 implementation lane

This package starts the independently implemented PSKernel-C1 engine. It is not yet a declaration checker and is not on the shipped C1 CLI acceptance path.

Read the [architecture and priorities](../PSKERNEL_C1_NEXT_ARCHITECTURE.md) first. Size reduction is optional; no size target constrains correctness, capability, proofs, performance or readability.

## Delivered first component

`PskernelC1Independent/Universe.lean` owns universe syntax with zero, successor, max, imax and natural-number parameter IDs; evaluation; simultaneous substitution; renaming; conservative normalization; and a positive equality fast path.

`UniverseProofs.lean` proves substitution/renaming laws, semantic preservation of normalization, and soundness of every positive fast-path result. The statements quantify over all assignments. Tests include an equality that deliberately yields `unknown`, so callers cannot treat an inconclusive fast path as inequality.

These are proofs of the component's actual functions, not a consistency proof for a full kernel. There is no inherited checking call, external dependency, foreign-function implementation or runtime model computation in this component.

## Build and audit

The package uses the enclosing repository's `lean-toolchain`.

```sh
cd independent
lake build
lake test
lake env lean PskernelC1IndependentTests.lean
```

Cloud Linux CI builds the proofs and regression examples warning-free, scans the independent source/import boundary, and audits all eleven named theorem dependencies. The normal repository CI still validates the qualified inherited checker independently.

## Still required

The parameter-ID/source-name bridge, complete universe comparator, expressions, contexts, inference, conversion, declaration/inductive installation, assumption-relative policy, parser/driver integration and checker-to-model theorem are not implemented here yet. No full-Arena, independent-kernel completion, speedup or binary-size claim follows from this component.
