module

@[expose] public section

/-!
# Independent universe operations

This module owns its representation and executable functions. It imports
no ConLeche or Lean checker implementation. Parameter IDs are natural
numbers; a future source-name interner must establish their correspondence.

The contract is evaluation at EVERY assignment of parameter values, not
agreement at a finite sample. Proofs live in `UniverseProofs`.
`compareFast` is deliberately incomplete: `unknown` requires another
verified comparison procedure and is never a negative equality verdict.
-/

namespace PskernelC1Independent

/-- The five exported universe constructors, with explicit parameter IDs. -/
inductive Level where
  | zero
  | succ (level : Level)
  | max (left right : Level)
  | imax (left right : Level)
  | param (id : Nat)
  deriving DecidableEq, Repr

namespace Level

/-- Interpretation of a universe, including impredicative `imax`. -/
def eval (assignment : Nat → Nat) : Level → Nat
  | .zero => 0
  | .succ level => Nat.succ (eval assignment level)
  | .max left right => Nat.max (eval assignment left) (eval assignment right)
  | .imax left right =>
    let r := eval assignment right
    if r = 0 then 0 else Nat.max (eval assignment left) r
  | .param id => assignment id

/-- Simultaneous substitution; replacement levels are not substituted again. -/
def substitute (replacement : Nat → Level) : Level → Level
  | .zero => .zero
  | .succ level => .succ (substitute replacement level)
  | .max left right => .max (substitute replacement left) (substitute replacement right)
  | .imax left right => .imax (substitute replacement left) (substitute replacement right)
  | .param id => replacement id

/-- Parameter renaming is a special case of simultaneous substitution. -/
def rename (mapping : Nat → Nat) (level : Level) : Level :=
  substitute (fun id => .param (mapping id)) level

/-- Remove only the unconditional zero identities. No ordering assumption. -/
def maxSmart : Level → Level → Level
  | .zero, right => right
  | left, .zero => left
  | left, right => .max left right

/-- Only a syntactically positive right side licenses this `imax` reduction. -/
def imaxSmart (left : Level) : Level → Level
  | .zero => .zero
  | .succ right => maxSmart left (.succ right)
  | right => .imax left right

/-- A total, conservative normalizer. This is not a canonical normal form. -/
def normalize : Level → Level
  | .zero => .zero
  | .param id => .param id
  | .succ level => .succ (normalize level)
  | .max left right => maxSmart (normalize left) (normalize right)
  | .imax left right => imaxSmart (normalize left) (normalize right)

/-- Semantic equality is a specification, not a finite-assignment test. -/
def Equivalent (left right : Level) : Prop :=
  ∀ assignment, eval assignment left = eval assignment right

/-- `unknown` is NOT `unequal`, `invalid`, or `unsupported`. -/
inductive EqualityResult where
  | equal
  | unknown
  deriving DecidableEq, Repr

/-- A sound positive fast path; a complete comparator is a separate task. -/
def compareFast (left right : Level) : EqualityResult :=
  if normalize left = normalize right then .equal else .unknown

end Level
end PskernelC1Independent
