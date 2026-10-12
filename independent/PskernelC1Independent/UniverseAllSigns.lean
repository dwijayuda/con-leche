module

public import PskernelC1Independent.UniverseSignCases

@[expose] public section

/-!
# Exhaustive finite-sign universe comparison: specification baseline

For an imax expression, the sign-case compiler gives an exact polynomial
under a fixed zero/positive choice for each parameter. The following
algorithm enumerates all such choices and checks each polynomial case.

This is a TOTAL semantic-equivalence *reference*, not a production
performance claim. Enumeration is exponential in the parameter-occurrence
list (including duplicates). No kernel hot path imports this module.
A production comparator should refine this contract with a more efficient
case analysis and explicit resource limits; semantic equivalence is also
not necessarily the pinned official Lean kernel's operational equality.
-/

namespace PskernelC1Independent.Level

/-- Every parameter occurrence in a source universe expression. -/
def parameterIds : Level → List Nat
  | .zero => []
  | .param id => [id]
  | .succ level => parameterIds level
  | .max left right => parameterIds left ++ parameterIds right
  | .imax left right => parameterIds left ++ parameterIds right

/-- Update one sign in a finite sign assignment. -/
def setSign (flags : Nat → Bool) (key : Nat) (value : Bool) (id : Nat) : Bool :=
  if id = key then value else flags id

/-- Exhaust all finite zero/positive choices, without assuming no duplicates. -/
def signPatterns : List Nat → List (Nat → Bool)
  | [] => [fun _ => false]
  | id :: rest =>
    let tail := signPatterns rest
    tail.map (fun flags => setSign flags id false) ++
      tail.map (fun flags => setSign flags id true)

/-- Every natural number is zero or a successor. -/
def signsOf (assignment : Nat → Nat) (id : Nat) : Bool :=
  decide (assignment id ≠ 0)

def residualOf (assignment : Nat → Nat) (id : Nat) : Nat :=
  assignment id - 1

/-- Unoptimized complete semantic comparison, intended as a proof and
differential oracle, not as a production hot-path comparator. -/
def compareExhaustive (left right : Level) : Bool :=
  (signPatterns (parameterIds left ++ parameterIds right)).all
    (fun positive => compareSigned positive left right)

end PskernelC1Independent.Level
