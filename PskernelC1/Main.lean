module

public import PskernelC1.Kernel
public import ConLeche.Driver.Run
public import Std.Async.System

@[expose] public section

/-!
# The small, verified-only C1 command line

The existing streaming parser and proof-carrying parallel driver do the
work. A successful line requires an `AcceptedStream`: its proof connects
the parser witness, prelude preparation, and this particular checker run.
No model module is imported into the executable, and no second pass is
needed to obtain the receipt. Filesystem reads, compilation and runtime
execution remain the inherited trust boundary.
-/

namespace PskernelC1.Cli

open ConLeche

def version : String := "pskernel-c1 0.1.0"

def usage : String := String.intercalate "\n" [
  "usage: pskernel-c1 [--jobs=<n>] [--stats] [--verified] FILE.ndjson",
  "       pskernel-c1 --help | --version",
  "",
  "Check a raw lean4export stream in the model-proved verified mode.",
  "  --jobs=<n>  positive worker count; default: hardware concurrency",
  "  --stats     collect and print per-phase and per-record statistics",
  "  --verified  explicit spelling of the only supported checking mode",
  "",
  "Exit codes: 0 accepted, 1 invalid, 2 unsupported, 3 usage/IO/internal error.",
  "Model and consistency claims are relative to the SetTheory interface.",
  "See PSKERNEL_C1.md for the theorem, supported scope and trust boundary."]

structure Args where
  jobs : Option Nat := none
  stats : Bool := false
  file : Option String := none
  help : Bool := false
  version : Bool := false

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--help" :: rest, a => parseArgs rest { a with help := true }
  | "--version" :: rest, a => parseArgs rest { a with version := true }
  | "--verified" :: rest, a => parseArgs rest a
  | "--stats" :: rest, a => parseArgs rest { a with stats := true }
  | "--" :: rest, a =>
    match rest, a.file with
    | [file], none => .ok { a with file := some file }
    | _, _ => .error "exactly one input file is required after --"
  | arg :: rest, a =>
    if arg.startsWith "--jobs=" then
      match ((arg.drop "--jobs=".length).toString).toNat? with
      | some 0 => .error "--jobs requires a positive decimal worker count"
      | some n => parseArgs rest { a with jobs := some n }
      | none => .error "--jobs requires a positive decimal worker count"
    else if arg.startsWith "-" then
      .error s!"unknown option {arg}"
    else
      match a.file with
      | none => parseArgs rest { a with file := some arg }
      | some _ => .error "exactly one input file is required"

/-- Lean checks the receipt at this call boundary. The body only prints:
the evidence is erased, so accepting never computes a model at runtime. -/
def printAccepted (count : Nat) (_accepted : AcceptedStream) : IO UInt32 := do
  IO.println s!"pskernel-c1: accepted {count} declarations (--verified)"
  return 0

/-- Stream once, check once, and compose the evidence already returned. -/
def checkFile (file : String) (jobs : Nat) (stats : Bool)
    (drain : IO.Ref (IO Unit)) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  match hp : Frontend.builtinPreludeE with
  | .error (e, line) =>
    IO.eprintln s!"pskernel-c1: internal error: built-in prelude at line {line}: {e}"
    return 3
  | .ok pre =>
    let outcome ← Driver.parseInput file jobs false
    match hr : outcome.val with
    | .error (e, line) =>
      IO.eprintln s!"pskernel-c1: {file}:{line}: {e} (--verified)"
      return e.exitCode
    | .ok parsed =>
      let decls := Frontend.preparePrelude pre parsed.decls
      let tParse ← IO.monoMsNow
      let err ← IO.getStderr
      -- No progress output; keep the inherited persistent-mark optimization.
      -- Statistics are independent of the fixed checking policy.
      let result ← Driver.checkDeclsIO
        (mode := .verified) (err := err) (stride := 0) (total := decls.size)
        (t0 := t0) (tParse := tParse) (jobs := jobs) (noMark := false)
        (drain := drain) (ds := decls) (collectStats := stats)
      match result with
      | .ok checked =>
        let accepted : Accepted decls := ⟨checked.val, checked.property⟩
        let receipt : AcceptedStream := AcceptedStream.ofChecks hp
          (by simpa only [hr] using outcome.property) accepted
        printAccepted parsed.decls.size receipt
      | .error (e, i) =>
        let loc := if h : i < decls.size then
            s!" [at {Driver.declCName decls[i]}, fold position {i}]"
          else s!" [at fold position {i}]"
        IO.eprintln s!"pskernel-c1: {e}{loc} (--verified)"
        return e.exitCode

/-- IO exceptions are errors, never rejections of a mathematical declaration. -/
def run (args : List String) (drain : IO.Ref (IO Unit)) : IO UInt32 := do
  try
    -- Preserve the inherited linearity checks and fail-stop panic policy.
    -- These variables affect this process only and do not select its verdict.
    Std.Async.System.setEnvVar "LEAN_ABORT_ON_NONLINEAR" "1"
    Std.Async.System.setEnvVar "LEAN_ABORT_ON_PANIC" "1"
    let a ← match parseArgs args {} with
      | .ok a => pure a
      | .error msg =>
        IO.eprintln s!"pskernel-c1: {msg}\n{usage}"
        return 3
    if a.help then
      IO.println usage
      return 0
    if a.version then
      IO.println version
      return 0
    let file ← match a.file with
      | some file => pure file
      | none =>
        IO.eprintln usage
        return 3
    let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
    let jobs := a.jobs.getD (max 1 hw)
    checkFile file jobs a.stats drain
  catch e =>
    (try IO.eprintln s!"pskernel-c1: internal error: {e}" catch _ => pure ())
    return 3

end PskernelC1.Cli

/-- Flush and join the install workers before process exit, including errors. -/
def main (args : List String) : IO UInt32 := do
  let drain ← IO.mkRef (pure () : IO Unit)
  let mut code ← PskernelC1.Cli.run args drain
  try
    (← IO.getStdout).flush
    (← IO.getStderr).flush
  catch _ => code := 3
  try (← drain.get) catch _ => code := 3
  IO.Process.exit code.toUInt8
