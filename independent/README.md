# Independent PSKernel-C1 implementation

This separate Lean/Lake package implements a new checker foundation without importing ConLeche checking code. It is **not** the shipped `pskernel-c1` declaration checker, not a new self-hosting compiler, and not yet a full Lean4 kernel.

[Architecture and priorities](../PSKERNEL_C1_NEXT_ARCHITECTURE.md) | [Canonical work state](../AI_WORK_STATE.md)

## Verified modules

| Module family | Scope |
|---|---|
| `Universe`, `UniverseProofs` | Five universe constructors, evaluation, substitution, renaming and sound normalization |
| `UniversePolynomial`, `UniversePolynomialProofs` | Sound, complete zero/parameter/succ/max polynomial equality |
| `UniverseSignCases`, `UniverseSignCasesProofs` | Exact zero/positive branch semantics of nested `imax` |
| `UniverseAllSigns`, `UniverseAllSignsProofs` | Fully semantically complete arbitrary-`imax` equality oracle and negative proof; exhaustive, potentially exponential |
| `NameCodec`, `NameCodecProofs` | Finite first-occurrence IDs, optional decoding, no aliasing, stable IDs when tables extend |
| `Expr`, `ExprProofs` | Own ten expression constructors, a decidable scope judgment, and bound-variable raising preserving scope |
| `ExprSubst`, `ExprSubstProofs` | Capture-safe single-binder substitution, including open replacements, scope preservation, lift-closed identity |
| `ExprAbstract`, `ExprAbstractProofs` | Close a fresh fvar into a bvar; independent scope preservation |
| `*Tests.lean` | Regression guards, theorem interface examples and exact named-axiom audits |

**Important fvar invariant:** `fvar i ty` stores a type closed against loose bound variables and referencing only earlier fvar levels. Both raising and substitution treat this annotation as atomic. This is intentional alignment with the actual inherited kernel implementation—not a shortcut.

**Important binder annotation invariant:** `BinderZero` is untrusted representation. An `allZero` list is not assumed sorted/deduplicated or semantically validated. Inference/conversion must discharge those obligations separately.

**Important universe distinction:** `compareExhaustive` proves semantic equality for all five constructors, not the pinned official Lean kernel's algorithmic conversion relation. It is a proof/development reference, not an acceptable unbounded production hot-path implementation.

## Proof-only integration

The [universe bridge](../bridge/pskernel-c1/UniverseBridge.lean) proves source-name encoding fidelity and semantic comparison against actual exported reference levels.

The [expression bridge](../bridge/pskernel-c1/ExprBridge.lean) proves that the independent expression representation preserves reference bound-variable scope, and that the actual independent `instantiate1` (with a provably bvar-closed replacement) and `abstract1` commute with the corresponding `ConLeche.Expr` executable operations. These bridges import inherited code ONLY for their proofs; the independent runtime package remains clean.

At commit `181cc040641d3065f2baa808d5729c835e4eeb02`, independent tests passed [run 38195107171](https://github.com/dwijayuda/con-leche/actions/runs/38195107171), the expression bridge passed [run 38195107226](https://github.com/dwijayuda/con-leche/actions/runs/38195107226), and the universe bridge passed [run 38195107173](https://github.com/dwijayuda/con-leche/actions/runs/38195107173). Later changes need their own green validation.

## Build

Use the repository's pinned Lean toolchain:

```sh
cd independent
lake build
lake test
lake env lean PskernelC1IndependentTests.lean
```

`scripts/c1-independent-audit.py` checks imports, forbidden trust constructs and exact named capstone dependencies. The separate expression and universe bridge cloud workflows prove operational/semantic cross-implementation obligations and check no new proof assumptions.

## Remaining capability

Independent full inference, algorithmic conversion, typed contexts, declaration/inductive installation, arbitrary-assumption ledger, model-extension proof, direct CLI acceptance, full official Lean compatibility, full Arena, and large-corpus performance remain outstanding. Size reduction is explicitly optional: correctness, capability, measured performance, proof assurance and readability take precedence.
