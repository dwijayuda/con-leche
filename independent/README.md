# Independent C1 implementation lane

This package implements the first independently written PSKernel-C1 components. It is not yet a declaration checker and is not on the shipped C1 CLI acceptance path.

Read the [architecture and priorities](../PSKERNEL_C1_NEXT_ARCHITECTURE.md) first. Size reduction is optional: no size target constrains correctness, capability, proofs, performance, or readability.

## Implemented and proved

| Module | Executable component or checked contract |
|---|---|
| `Universe.lean` | Owned zero/successor/max/imax/parameter syntax; evaluation; simultaneous substitution; renaming; conservative normalization; positive equality fast path |
| `UniverseProofs.lean` | Eleven substitution, renaming, semantic-preservation, positive-verdict, and explicit-incompleteness contracts |
| `UniversePolynomial.lean` | Finite maxima of constants and parameter-offset atoms; dominance comparison; complete comparator for the imax-free fragment |
| `NameCodec.lean` and `NameCodecProofs.lean` | Independent finite first-occurrence name IDs, partial decoder and six proof contracts; no name alias or unstable existing IDs |
| `NameCodecTests.lean` | Source-identity regression tests |
| `UniversePolynomialProofs.lean` | Evaluation preservation, dominance soundness/completeness, sound positive and negative verdicts, and complete/conclusive comparison for the supported fragment |
| `PolynomialTests.lean` and `PskernelC1IndependentTests.lean` | Forty-three regression guards, six theorem examples, and twenty-two named capstone audits |

The polynomial comparator handles arbitrary nesting of zero, parameters, successor, and max. Tests cover reordered/grouped maxima, duplicate terms, successor distribution, dominated offsets, and distinct constant floors. Its completeness proof uses an explicit separating parameter assignment; it does not assume a unique canonical form or rely on finitely sampled assignments.

General imax is not yet handled by that comparator. It returns `unknown` for that missing fragment; the basic normalization fast path can still establish some equalities involving imax. Neither unknown result is inequality. `comparePolynomial_different` separately proves the soundness of the polynomial comparator's conclusive negative result.

These are proofs of the actual functions, not a consistency proof for an entire independent kernel. There is no inherited checking call, external package dependency, foreign-function implementation, or runtime model computation in these components.

## Checked evidence

At source `a2476126606850347c8a209f9ebd8adb56fecd1c`, [run 38173757176](https://github.com/dwijayuda/con-leche/actions/runs/38173757176) passed the warning-free independent build, all regression guards and theorem examples, the import/trust fence, and all sixteen capstone audits. [Artifact 11714304653](https://github.com/dwijayuda/con-leche/actions/runs/38173757176/artifacts/11714304653) retains the build logs and exact source hashes.

Every capstone's observed dependency subset is pinned in `scripts/c1-independent-audit.py`. The only allowed global proof foundations are `propext`, `Classical.choice`, and `Quot.sound`; not every theorem uses all three. No proof placeholder or new semantic axiom is accepted.

The separate [proof-only universe bridge](../bridge/pskernel-c1/README.md) connects the basic universe representation and positive fast path to the inherited semantics, with input-name fidelity explicit. Its seven theorems passed [run 38173757189](https://github.com/dwijayuda/con-leche/actions/runs/38173757189) at the same source. It imports ConLeche only in that proof adapter, not in this runtime package. The later semantic bridge run [38178500807](https://github.com/dwijayuda/con-leche/actions/runs/38178500807) also proved finite source encoding and transported positive/negative polynomial outcomes; an actual independent checker acceptance path is still missing.

## Build and audit

The package uses the enclosing repository's `lean-toolchain`.

```sh
cd independent
lake build
lake test
lake env lean PskernelC1IndependentTests.lean
```

Cloud Linux CI builds the proofs and regression examples warning-free, scans all independent source/imports, and audits each named theorem footprint from the direct root capstone census. New modules must import their proof interface explicitly in the root audit: an ordinary import from a test submodule is not re-exported. The normal repository CI still checks the inherited declaration checker independently. Historical passing evidence does not automatically qualify changed sources.

## Still required

General imax comparison, checker-level integration of the proved finite source-name codec, expression/context operations, inference, conversion, declaration/inductive installation, the assumption-relative policy, parser/driver integration, and the independent checker-to-model theorem are not implemented here yet.

The list-based polynomial dominance implementation is a readable correctness baseline; no hot-path performance superiority is claimed. No full-Arena, full-independent-kernel, speedup, or binary-size claim follows from these component proofs.
