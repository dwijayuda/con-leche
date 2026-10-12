# Reading the C1 proof

C1 connects a real checking result to a mathematical model. This guide
follows that connection in the source. Read [the project overview](../../PSKERNEL_C1.md)
for commands, supported inputs, measurements and the broader design.

## Reading order

| Step | Open | Look for |
|---|---|---|
| 1 | [Kernel.lean](../../PskernelC1/Kernel.lean) | `checkDeclarations`, then `checkChunks`: the functions being proved sound. |
| 2 | [Soundness.lean](../../PskernelC1/Soundness.lean) | `model_exists`, then `no_False_constant`: what successful checking guarantees. |
| 3 | [Kernel.lean](../../PskernelC1/Kernel.lean) | `Accepted`, `AcceptedChunks`, `AcceptedStream`: how a result carries evidence. |
| 4 | [Main.lean](../../PskernelC1/Main.lean) | `checkFile`: how streaming IO supplies that evidence. |
| 5 | [SetTheory/Core.lean](../../ConLeche/SetTheory/Core.lean) and [Denotes.lean](../../ConLeche/Denotes.lean) | The foundation assumed and the precise meaning of `Model`. |

## 1. Start with the checking function

`checkDeclarations ds` calls the existing cached declaration checker with
two fixed choices: `.verified` and the committed `natOpPinSets`. Its result
is either `.ok env`, containing the accepted environment, or `.error e`.
The C1 API does not offer the unverified checking mode.

`checkChunks` adds three steps: read the embedded prelude, parse the input
chunks, and check the records produced by prelude preparation. A failure
stops this sequence. These are the same pure functions used to describe
the successful path through the streaming command line.

An environment is the checker's collection of stored declarations.
Acceptance is the equation saying that this function returned this
environment on this input; it is more specific than a Boolean flag.

## 2. Read the theorem as a contract

This is the actual theorem and proof from `Soundness.lean`:

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (ds : Array Declaration) (env : Env)
    (accepted : checkDeclarations ds = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  exact ConLeche.model_exists V natOpPinSets ds env accepted
```

| Part | Meaning |
|---|---|
| `V`, `[SetTheory V]` | Choose a universe of sets satisfying the explicitly required laws. |
| `ds`, `env` | The input declaration array and returned environment. |
| `accepted` | Evidence of this concrete function's successful result. |
| `Nonempty (ConLeche.Model V env)` | A model of that environment exists in those sets. |

The short proof applies the existing ConLeche theorem. This works because
`checkDeclarations` unfolds to exactly its verified checker call. No field
asserting that an unknown implementation is sound is added.

`chunks_model_exists` peels apart a successful `checkChunks` run, obtains
its successful declaration check, and applies this same theorem.

## 3. Understand the model-to-`False` argument

`SetTheory` supplies set membership, its laws and the universe chain used
to interpret Lean's universes. Those are assumptions of the consistency
theorems. They are not consequences of a checker returning success.

The public `ConLeche.Model` assigns a set value to every stored constant
and places that value inside the interpretation of its declared type.
It also fixes the interpretation of the pinned `False` type as empty
and the pinned `Eq` as set equality. A stored constant of type `False`
would therefore require an element of the empty set.

`no_False_constant` excludes precisely that possibility. The stronger
inherited environment invariant supports its proof; the public model is
the readable statement of the resulting guarantee. C1 also proves that a
declaration stream containing a `False` theorem record cannot be accepted.
If the record occurs in a successful parser result, the complete chunks
pipeline cannot accept it either. The separately named JSON-template
corollary has the specific textual scope described beside its source
statement.

[Axioms.lean](../../tests/PskernelC1Tests/Axioms.lean) audits the thirteen
capstones' proof dependencies. Its three standard Lean axioms do not
remove the separate `[SetTheory V]` premise.

## 4. Follow the evidence into the executable

A receipt contains an environment and a proof about the result:

| Receipt | What its proof identifies |
|---|---|
| `Accepted ds` | The result of checking these declarations. |
| `AcceptedChunks chunks` | The result of the complete pipeline on these chunks. |
| `AcceptedStream` | Some chunk sequence on which the complete pipeline produced this environment. |

`checkCertified` and `checkChunksCertified` attach evidence to a result
they actually compute. Their erasure theorems show that removing the
receipt preserves the result, including errors.

The CLI uses streaming instead of keeping the whole input. Its parser
returns a chunk witness in a proposition. Its checking driver returns an
environment with the successful-check equation. `AcceptedStream.ofChecks`
combines these with the successful prelude equation. `checkFile` passes
the resulting receipt to `printAccepted` on its checking success path.
Proofs in `Prop` are erased; constructing the receipt does not recheck
the declarations or retain the input chunks.

The existential chunk witness does not certify a filename or a physical
read operation. File IO, the compiler, runtime and platform remain part
of the execution trust boundary. Acceptance soundness also does not
promise a decision on every input or full official-Lean compatibility.
Additional arbitrary axioms are declined; C1 supplies no interface for
assuming them or for attaching a model of them.

## 5. Know which layer an optimization changes

| Layer | Source | Its job |
|---|---|---|
| Implementation | [Cached/Installed.lean](../../ConLeche/Cached/Installed.lean), `Kernel`, `Frontend`, `Driver` | Compute results, parse input and schedule work. |
| Rules and verification | [Rules/Rel.lean](../../ConLeche/Rules/Rel.lean), [Verify/Rules](../../ConLeche/Verify/Rules) | State judgments and connect checker operations to them. |
| Semantics and model | [Model/Rules/Sound.lean](../../ConLeche/Model/Rules/Sound.lean), `Semantics`, `SetTheory` | Interpret the judgments and prove their semantic validity. |

The CLI and runtime contract import no model tier. Start a driver change
by preserving its accepted-result equation. A representation or checking
algorithm change can also require new rule, environment and computation
proofs; retaining the name `Model` alone preserves no guarantee.

Before accepting an optimization, identify its success equation, repair
the affected proof connection, and check error behavior and ordering
where relevant. Then measure its cost. Prefer a clearly named invariant
and a short local explanation over a faster-looking change whose proof
obligation a reader cannot locate. CI must check both the proof and the
executable that is being qualified.
