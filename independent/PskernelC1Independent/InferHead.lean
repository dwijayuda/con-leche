module

public import PskernelC1Independent.Expr

@[expose] public section

/-!
# Independent kernel type-inference front door: the foundational leaves

This is NOT the full expression type checker. Its first two decidable
cases are the universe sort rule and locally-nameless free-variable
lookup. A preliminary *actual* scope check distinguishes invalid
inputs from syntactically supported-but-not-yet-implemented terms.

The result is evidence of a local inference-rule derivation, not a
model, not an unconstrained declaration acceptance, and not a
self-justifying trust certificate. Every future inference constructor
must be added to the rule relation and proved independently.
-/

namespace PskernelC1Independent

/-- The checker never reports an unsupported feature as a false theorem,
or an invalid variable reference as merely an unsupported feature. -/
inductive HeadOutcome where
  | inferred (type : Expr)
  | invalidScope
  | unsupported
  deriving Repr, DecidableEq

namespace Expr

/-- The executable leaf fragment. Check actual variable/annotation scope
before returning any type. It is deliberately conservative elsewhere. -/
def inferHead (fdepth : Nat) (term : Expr) : HeadOutcome :=
  if checkScoped 0 fdepth term then
    match term with
    | .sort level => .inferred (.sort (.succ level))
    | .fvar _ type => .inferred type
    | _ => .unsupported
  else .invalidScope

/-- Declarative specification, not an axiom about the checker. -/
inductive HeadDerives (fdepth : Nat) : Expr → Expr → Prop where
  | sort (level : Level) :
      HeadDerives fdepth (.sort level) (.sort (.succ level))
  | fvar {index : Nat} {type : Expr} :
      index < fdepth → Scoped 0 index type →
      HeadDerives fdepth (.fvar index type) type

end Expr
end PskernelC1Independent
