module

public import ConLeche.Verify.Level
public import PskernelC1Independent.UniverseProofs

public section

/-!
# Independent universe operations meet the inherited semantic interface

This is a PROOF-ONLY adapter, outside the independent runtime package.
It never calls either checker's universe comparison implementation.

The interpretation bridge itself needs no injectivity assumption. The
source-input equality corollary additionally requires a faithful codec:
decoding the encoded source names must return those names. Establishing
that property for the future input interner is a separate obligation.
-/

namespace PskernelC1Bridge

abbrev Level := PskernelC1Independent.Level

/-- Decode the independent representation under an explicit name map. -/
@[expose] def toReference (names : Nat → ConLeche.Name) : Level → ConLeche.Level
  | .zero => .zero
  | .succ level => .succ (toReference names level)
  | .max left right => .max (toReference names left) (toReference names right)
  | .imax left right => .imax (toReference names left) (toReference names right)
  | .param id => .param (names id)

/-- Encode an exported reference level under an explicit parameter map. -/
@[expose] def fromReference (ids : ConLeche.Name → Nat) : ConLeche.Level → Level
  | .zero => .zero
  | .succ level => .succ (fromReference ids level)
  | .max left right => .max (fromReference ids left) (fromReference ids right)
  | .imax left right => .imax (fromReference ids left) (fromReference ids right)
  | .param name => .param (ids name)

/-- Every decoded universe has precisely the inherited evaluation. -/
theorem toReference_eval (names : Nat → ConLeche.Name)
    (assignment : ConLeche.Name → Nat) (level : Level) :
    ConLeche.Level.eval assignment (toReference names level) =
      Level.eval (fun id => assignment (names id)) level := by
  induction level <;> simp [toReference, ConLeche.Level.eval, Level.eval, *]

/-- Encoding commutes with interpretation at all parameter assignments. -/
theorem fromReference_eval (ids : ConLeche.Name → Nat)
    (assignment : Nat → Nat) (level : ConLeche.Level) :
    Level.eval assignment (fromReference ids level) =
      ConLeche.Level.eval (fun name => assignment (ids name)) level := by
  induction level <;> simp [fromReference, ConLeche.Level.eval, Level.eval, *]

/-- A faithful name codec preserves the complete source universe syntax. -/
theorem source_roundtrip (ids : ConLeche.Name → Nat) (names : Nat → ConLeche.Name)
    (faithful : ∀ name, names (ids name) = name) (level : ConLeche.Level) :
    toReference names (fromReference ids level) = level := by
  induction level <;> simp [toReference, fromReference, faithful, *]

/-- The independent normalizer preserves the reference semantic meaning. -/
theorem normalize_reference_sound (names : Nat → ConLeche.Name)
    (assignment : ConLeche.Name → Nat) (level : Level) :
    ConLeche.Level.eval assignment (toReference names (Level.normalize level)) =
      ConLeche.Level.eval assignment (toReference names level) := by
  rw [toReference_eval, toReference_eval]
  exact Level.eval_normalize _ level

/-- A positive independent fast path preserves the reference interpretation. -/
theorem compareFast_reference_sound (names : Nat → ConLeche.Name)
    (left right : Level) (accepted : Level.compareFast left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment (toReference names left) =
      ConLeche.Level.eval assignment (toReference names right) := by
  intro assignment
  rw [toReference_eval, toReference_eval]
  exact Level.compareFast_sound left right accepted _

/-- Source equality requires the codec proof; aliasing source names is not
silently licensed by correctness of the internal comparison operation. -/
theorem compareFast_source_sound (ids : ConLeche.Name → Nat)
    (names : Nat → ConLeche.Name) (faithful : ∀ name, names (ids name) = name)
    (left right : ConLeche.Level)
    (accepted : Level.compareFast (fromReference ids left) (fromReference ids right) = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment left = ConLeche.Level.eval assignment right := by
  intro assignment
  have h := compareFast_reference_sound names _ _ accepted assignment
  simpa only [source_roundtrip ids names faithful] using h

/-- Even a per-input roundtrip proof is sufficient: a parser need not claim
that its finite parameter table represents every name in the language. -/
theorem compareFast_inputs_sound (names : Nat → ConLeche.Name)
    (left right : Level) (sourceLeft sourceRight : ConLeche.Level)
    (leftFaithful : toReference names left = sourceLeft)
    (rightFaithful : toReference names right = sourceRight)
    (accepted : Level.compareFast left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment sourceLeft =
      ConLeche.Level.eval assignment sourceRight := by
  intro assignment
  rw [← leftFaithful, ← rightFaithful]
  exact compareFast_reference_sound names left right accepted assignment

#print axioms toReference_eval
#print axioms fromReference_eval
#print axioms source_roundtrip
#print axioms normalize_reference_sound
#print axioms compareFast_reference_sound
#print axioms compareFast_source_sound
#print axioms compareFast_inputs_sound

end PskernelC1Bridge
