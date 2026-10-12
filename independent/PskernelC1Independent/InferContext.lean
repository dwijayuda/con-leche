module

public import PskernelC1Independent.InferHead

@[expose] public section

/-!
# The independent local type context, not merely a numeric fvar depth

The original leaf-inference rule reads a type stored directly in a fvar
node. On untrusted terms, the same numeric fvar level could carry
conflicting annotations unless those nodes are pinned to one checked
context. This module makes the missing binding invariant explicit.

The context is a list ordered by increasing fvar level, with `lookup`
returning the type at that level. This is a simple correctness baseline.
Changing it to a faster persistent array later requires an equivalent
lookup/invariant proof, never a hash-only equality shortcut.

A matching annotation is NOT sufficient to prove that the context
contains semantically well-typed declarations; that is a separate
kernel typing/environment proof obligation.
-/

namespace PskernelC1Independent

/-- One authority for every opened free-variable type. -/
def LocalContext := List Expr

namespace LocalContext

def lookup : LocalContext → Nat → Option Expr
  | [], _ => none
  | type :: _, 0 => some type
  | _ :: more, index + 1 => lookup more index

/-- A context only stores syntactically closed types referring to
strictly earlier local levels. This is not yet a theorem of typing. -/
def WellScoped (context : LocalContext) : Prop :=
  ∀ index type, lookup context index = some type → Expr.Scoped 0 index type

end LocalContext

/-- An annotated fvar that disagrees with its registered local binding
cannot silently get a type merely by writing a different annotation. -/
inductive ContextOutcome where
  | inferred (type : Expr)
  | invalidScope
  | contextMismatch
  | unsupported
  deriving Repr, DecidableEq

namespace Expr

/-- First perform actual term scope checking, then check that the
inference leaf's annotated fvar type agrees with the local context.
Errors are distinct from unsupported syntax and successful inference. -/
def inferHeadIn (context : LocalContext) (term : Expr) : ContextOutcome :=
  match inferHead context.length term with
  | .inferred type =>
      match term with
      | .fvar index annotation =>
          if LocalContext.lookup context index = some annotation then .inferred type
          else .contextMismatch
      | _ => .inferred type
  | .invalidScope => .invalidScope
  | .unsupported => .unsupported

/-- A typing judgment whose fvar rule reads its type from the actual
local context rather than trusting whichever annotation input supplies. -/
inductive ContextHeadDerives (context : LocalContext) : Expr → Expr → Prop where
  | sort (level : Level) :
      ContextHeadDerives context (.sort level) (.sort (.succ level))
  | fvar {index : Nat} {type : Expr} :
      LocalContext.lookup context index = some type →
      Scoped 0 index type →
      ContextHeadDerives context (.fvar index type) type

end Expr
end PskernelC1Independent
