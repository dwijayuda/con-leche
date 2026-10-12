module

public import ConLeche.Cached.Installed
public import ConLeche.Frontend.Prelude

@[expose] public section

/-!
# The verified executable boundary

The first implementation reuses ConLeche's checked declaration fold. The
owned boundary fixes its checking mode and committed arithmetic pins, so
callers cannot accidentally select the unverified mode.

`checkDeclarations` is the declaration-level entry point. `checkChunks`
adds the existing parser and prelude preparation. The certified entry
points return the same verdicts together with evidence of the *actual*
functions' successful results. That evidence is a proposition, erased by
Lean's compiler; the model and its proofs live in `PskernelC1.Soundness`
and are not imported here.

An alternative driver can return `Accepted` by proving the same concrete
success equation. `AcceptedChunks.ofChecks` connects a streaming parser
and such a declaration receipt to the whole chunks pipeline, without
running either phase again.
-/

namespace PskernelC1

open ConLeche

/-- The original error and its input line or declaration-fold position. -/
abbrev CheckResult := Except (ConLeche.CheckError × Nat) ConLeche.Env

/-- Check declarations using only the model-proved mode and shipped pins. -/
def checkDeclarations (ds : Array Declaration) : CheckResult :=
  Cached.checkDecls .verified natOpPinSets ds

/-- Parse the chunks, prepare the prelude, and check every resulting record. -/
def checkChunks (chunks : List ByteArray) : CheckResult := do
  let pre ← Frontend.builtinPreludeE
  let parsed ← Frontend.parseChunks chunks
  checkDeclarations (Frontend.preparePrelude pre parsed.decls)

/-- An environment accepted by the concrete declaration checker. -/
abbrev Accepted (ds : Array Declaration) :=
  { env : Env // checkDeclarations ds = .ok env }

/-- An environment accepted by the concrete parser-and-checker pipeline. -/
abbrev AcceptedChunks (chunks : List ByteArray) :=
  { env : Env // checkChunks chunks = .ok env }

/-- A streaming receipt keeps its chunk witness in a proposition, so the
runtime need not retain the bytes after parsing them. The link between
physical file reads and those chunks belongs to the IO implementation. -/
abbrev AcceptedStream :=
  { env : Env // ∃ chunks, checkChunks chunks = .ok env }

/-- Attach the equation witnessed by a computed result, preserving errors. -/
def certifyResult {ε α : Type} (result : Except ε α) :
    Except ε { value : α // result = .ok value } :=
  match result with
  | .error e => .error e
  | .ok value => .ok ⟨value, rfl⟩

/-- Execute the declaration checker and return its successful-run evidence. -/
def checkCertified (ds : Array Declaration) :
    Except (ConLeche.CheckError × Nat) (Accepted ds) :=
  certifyResult (checkDeclarations ds)

/-- Execute the chunks pipeline and return its successful-run evidence. -/
def checkChunksCertified (chunks : List ByteArray) :
    Except (ConLeche.CheckError × Nat) (AcceptedChunks chunks) :=
  certifyResult (checkChunks chunks)

/-- Removing the receipt changes neither the value nor any error. -/
theorem certifyResult_erase {ε α : Type} (result : Except ε α) :
    (certifyResult result).map (fun accepted => accepted.val) = result := by
  cases result <;> rfl

/-- The certified declaration entry point has exactly the ordinary verdict. -/
theorem checkCertified_erase (ds : Array Declaration) :
    (checkCertified ds).map (fun accepted => accepted.val) = checkDeclarations ds := by
  exact certifyResult_erase (checkDeclarations ds)

/-- The certified chunks entry point has exactly the ordinary verdict. -/
theorem checkChunksCertified_erase (chunks : List ByteArray) :
    (checkChunksCertified chunks).map (fun accepted => accepted.val) = checkChunks chunks := by
  exact certifyResult_erase (checkChunks chunks)

/-- Compose phase receipts into acceptance of the actual chunks pipeline.
The parser's equality identifies the exact chunks; an IO reader supplies
that equality for the bytes it read. -/
def AcceptedChunks.ofChecks {chunks : List ByteArray}
    {pre : Frontend.PreludeIx} {parsed : Frontend.ParseResultD}
    (hpre : Frontend.builtinPreludeE = .ok pre)
    (hparse : Frontend.parseChunks chunks = .ok parsed)
    (accepted : Accepted (Frontend.preparePrelude pre parsed.decls)) :
    AcceptedChunks chunks :=
  ⟨accepted.val, by
    simpa only [checkChunks, hpre, hparse, Bind.bind, Except.bind] using accepted.property⟩

/-- Compose the existential parse receipt returned by the streaming reader
with a declaration receipt. Chunk storage remains proof-only. -/
def AcceptedStream.ofChecks
    {pre : Frontend.PreludeIx} {parsed : Frontend.ParseResultD}
    (hpre : Frontend.builtinPreludeE = .ok pre)
    (hparse : ∃ chunks, Frontend.parseChunks chunks = .ok parsed)
    (accepted : Accepted (Frontend.preparePrelude pre parsed.decls)) :
    AcceptedStream :=
  ⟨accepted.val, by
    obtain ⟨chunks, hchunks⟩ := hparse
    exact ⟨chunks, (AcceptedChunks.ofChecks hpre hchunks accepted).property⟩⟩

end PskernelC1
