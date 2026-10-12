module

public import PskernelC1Independent.Universe

public section

/-!
# Contracts for the independent universe functions

These statements quantify over every parameter assignment. They prove
properties of the actual functions, without assuming a field asserting
that an implementation is sound. They do not claim expression checking,
complete universe comparison, or the full declaration/model bridge.
-/

namespace PskernelC1Independent.Level

/-- Substituting syntax agrees with substituting the semantic assignment. -/
theorem eval_substitute (replacement : Nat → Level) (assignment : Nat → Nat)
    (level : Level) :
    eval assignment (substitute replacement level) =
      eval (fun id => eval assignment (replacement id)) level := by
  induction level <;> simp [substitute, eval, *]

/-- Identity substitution preserves the entire universe syntax. -/
theorem substitute_identity (level : Level) :
    substitute Level.param level = level := by
  induction level <;> simp [substitute, *]

/-- Substitution composition fixes the direction and simultaneous semantics. -/
theorem substitute_compose (first second : Nat → Level) (level : Level) :
    substitute second (substitute first level) =
      substitute (fun id => substitute second (first id)) level := by
  induction level <;> simp [substitute, *]

/-- Renaming changes only the interpretation of parameter IDs. -/
theorem eval_rename (mapping : Nat → Nat) (assignment : Nat → Nat)
    (level : Level) :
    eval assignment (rename mapping level) =
      eval (fun id => assignment (mapping id)) level := by
  simpa only [rename, eval] using
    eval_substitute (fun id => Level.param (mapping id)) assignment level

/-- Every smart maximum computes the intended maximum. -/
theorem eval_maxSmart (assignment : Nat → Nat) (left right : Level) :
    eval assignment (maxSmart left right) =
      Nat.max (eval assignment left) (eval assignment right) := by
  cases left <;> cases right <;> simp [maxSmart, eval]

/-- The impredicative zero case is preserved, including parameterized inputs. -/
theorem eval_imaxSmart (assignment : Nat → Nat) (left right : Level) :
    eval assignment (imaxSmart left right) =
      if eval assignment right = 0 then 0
      else Nat.max (eval assignment left) (eval assignment right) := by
  cases right <;> simp [imaxSmart, eval_maxSmart, eval]

/-- The actual normalizer preserves evaluation at all assignments. -/
theorem eval_normalize (assignment : Nat → Nat) (level : Level) :
    eval assignment (normalize level) = eval assignment level := by
  induction level <;>
    simp [normalize, eval_maxSmart, eval_imaxSmart, eval, *]

/-- Normalization is an equivalence-preserving transformation. -/
theorem normalize_sound (level : Level) : Equivalent level (normalize level) := by
  intro assignment
  exact (eval_normalize assignment level).symm

/-- A positive result from this executable fast path is semantically sound. -/
theorem compareFast_sound (left right : Level)
    (accepted : compareFast left right = .equal) : Equivalent left right := by
  unfold compareFast at accepted
  split at accepted
  next h =>
    intro assignment
    calc
      eval assignment left = eval assignment (normalize left) :=
        (eval_normalize assignment left).symm
      _ = eval assignment (normalize right) := congrArg (eval assignment) h
      _ = eval assignment right := eval_normalize assignment right
  next _ => cases accepted

/-- The positive fast path is useful on every reflexive input. -/
theorem compareFast_reflexive (level : Level) : compareFast level level = .equal := by
  simp [compareFast]

/-- Regression contract: a semantic equality may yield unknown.
A caller treating unknown as unequal violates this proved example. -/
theorem unknown_can_be_equivalent :
    compareFast (.max (.param 0) (.param 1)) (.max (.param 1) (.param 0)) = .unknown ∧
    Equivalent (.max (.param 0) (.param 1)) (.max (.param 1) (.param 0)) := by
  constructor
  · rfl
  · intro assignment
    exact Nat.max_comm (assignment 0) (assignment 1)

end PskernelC1Independent.Level
