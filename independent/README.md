# Independent C1 implementation lane

This package implements the first independently written PSKernel-C1 components. It is not yet a declaration checker and is not on the shipped C1 CLI acceptance path.

Read the [architecture and priorities](../PSKERNEL_C1_NEXT_ARCHITECTURE.md) first. Size reduction is optional: no size target constrains correctness, capability, proofs, performance, or readability.

## Implemented and proved

| Module | Executable component or checked contract |
|---|---|
| `Universe.lean` | Owned zero/successor/max/imax/parameter syntax; evaluation; simultaneous substitution; renaming; conservative normalization; positive equality fast path |
| `UniverseProofs.lean` | Eleven substitution, renaming, semantic-preservation, positive-verdict, and explicit-incompleteness contracts |
| `UniversePolynomial.lean` | Finite maxima of constants and parameter-offset atoms; dominance comparison; complete comparator for the imax-free fragment |
| `UniverseSignCases.lean` and `UniverseSignCasesProofs.lean` | Exact zero/successor sign analysis of nested imax; four verified fixed-sign branch contracts |
| `UniverseAllSigns.lean` and `UniverseAllSignsProofs.lean` | Complete semantic equality reference via finite sign enumeration; five proofs including a global iff and justified negative result (exponential, not on the runtime hot path) |
| `NameCodec.lean` and `NameCodecProofs.lean` | Independent finite first-occurrence name IDs, partial decoder and six proof contracts; no name alias or unstable existing IDs |
| `NameCodecTests.lean` | Source-identity regression tests |
| `UniversePolynomialProofs.lean` | Evaluation preservation, dominance soundness/completeness, sound positive and negative verdicts, and complete/conclusive comparison for the supported fragment |
| `PolynomialTests.lean` and `PskernelC1IndependentTests.lean` | At least fifty regression guards, seven theorem examples, and thirty-one named capstone audits |

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

Optimized kernel-compatible operational imax comparison, checker-level integration of the proved finite source-name codec, expression/context operations, inference, conversion, declaration/inductive installation, the assumption-relative policy, parser/driver integration, and the independent checker-to-model theorem are not implemented here yet.

The list-based polynomial dominance implementation is a readable correctness baseline; no hot-path performance superiority is claimed. No full-Arena, full-independent-kernel, speedup, or binary-size claim follows from these component proofs.

## Independent expression and scope foundation (in development)

The new independent `Expr` AST preserves ten kernel expression constructors (including locally nameless `fvar`s and typed annotations). Binder propositions are untrusted structured input until the later kernel checker validates their semantic meaning; duplicate or unordered annotation parameters are NOT silently assumed canonical. A separate structural `Scoped` judgment and a runnable scope checker specify variable-depth correctness. Capture-safe raising shifts only variables above the cutoff and increments the cutoff when entering binder bodies, not their types or let values. The scope-preservation theorem belongs to the independent checker foundations, not a proof of inference/conversion or declaration checking. Follow its exact cloud CI result before claiming qualification.

## Capture-safe binder instantiation (in development)

The actual `instantiateAt`/`instantiate1` implementation removes one bound-variable level, raises replacements under intervening binder bodies, lowers indices above the eliminated binder and traverses fvar-type annotations. Its proofs establish the scope-preserving precondition for beta/zeta reduction with arbitrary open replacement terms, including nested lets and dependent binder domains. This is not yet an evaluator or a type-checker acceptance theorem. The proof audit and cloud CI must qualify its exact commit.

### Correctness invariant: typed free variables are atomic under bound substitution

A whole-subsystem inspection of `ConLeche/Kernel/ExprOps.lean` found that both its binder instantiation and abstraction/metadata walks treat `.fvar index type` as an atomic expression; its annotated type is a previously closed term, not a subtree where loose binder indices may be substituted. The independent implementation now enforces a stronger explicitly scoped construction rule: an fvar at level `i` may refer only to fvar levels `< i` in its type, and its type contains no loose `bvar`. Consequently, both bound-variable raising and binder instantiation leave fvar type annotations unchanged. The scope and substitution proofs are about the corrected functions, not a stale implementation. Arbitrary open replacement expressions still receive capture-avoiding lifting; the inherited kernel uses already closed replacements. A later operational refinement must prove equivalence under that precondition. This guards against an entire family of binder-capture/annotation mismatches, instead of patching sample terms.
