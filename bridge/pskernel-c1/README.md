# Independent universe semantic bridge

`UniverseBridge.lean` is proof-only integration work. The independent executable component remains free of ConLeche imports.

The adapter translates all five universe constructors and proves that evaluation, normalization, and every positive comparison result agree with the existing `ConLeche.Level.eval` semantics. It does not call the inherited comparison algorithm and does not claim that semantic equality already establishes every requirement of an integrated kernel.

The source-input theorem exposes input fidelity explicitly: either prove the name codec roundtrip or provide roundtrip equations for the two concrete source levels. The finite input interner itself is not implemented here. An internal equality theorem cannot justify accidentally identifying distinct source parameters.

Cloud CI builds the two libraries, checks this bridge, and audits its seven named theorem dependencies. This is not yet the expression/rule/declaration/model bridge for the full kernel, and no shipped CLI path uses it yet.

To reproduce from the repository root after installing the pinned toolchain:

```sh
lake build ConLeche.Verify.Level
(cd independent && lake build)
LEAN_PATH="$PWD/independent/.lake/build/lib/lean:$PWD/.lake/build/lib/lean" \
  lean bridge/pskernel-c1/UniverseBridge.lean
```
