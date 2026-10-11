# Independent universe semantic bridge

`UniverseBridge.lean` is proof-only integration work. The independent executable component remains free of ConLeche imports.

The adapter translates all five universe constructors and proves that evaluation, normalization, and every positive comparison result agree with the existing `ConLeche.Level.eval` semantics. It does not call the inherited comparison algorithm and does not claim that semantic equality already establishes every requirement of an integrated kernel.

The source-input theorem exposes input fidelity explicitly: either prove the name codec roundtrip or provide roundtrip equations for the two concrete source levels. A finite first-occurrence input codec is now implemented. The bridge constructs tables from the actual source parameters and proves input coverage, exact roundtrip and evaluation preservation. An internal equality theorem cannot justify accidentally identifying distinct source parameters.

Cloud CI builds the two libraries, checks this bridge, and audits its fifteen named theorem dependencies against exact axiom pins. Both positive and negative polynomial results are proved on the original source expressions; general imax and strict Lean kernel algorithmic conversion remain separate obligations. This is not yet the expression/rule/declaration/model bridge for the full kernel, and no shipped CLI path uses it yet.

To reproduce from the repository root after installing the pinned toolchain:

```sh
lake build ConLeche.Verify.Level
(cd independent && lake build)
LEAN_PATH="$PWD/independent/.lake/build/lib/lean:$PWD/.lake/build/lib/lean" \
  lean bridge/pskernel-c1/UniverseBridge.lean
```

## Complete semantic reference, not the production conversion algorithm

The standalone independent `compareExhaustive` now has a proof of soundness and completeness of semantic universe equality for all five constructors, including nested `imax`, by enumerating zero/positive parameter patterns. The proof-only bridge applies it to actual exported source names through the complete finite codec and proves the Boolean outcomes reflect source evaluation. The reference algorithm can be exponentially expensive (including duplicate parameter occurrences) and must not be placed on the production hot path without a measured refinement and resource policy. Equivalence in this set-theoretic semantics is not automatically identical to pinned Lean kernel operational conversion; preserve separate conformance tests and requirements.
