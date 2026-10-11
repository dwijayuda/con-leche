module

import PskernelC1Independent.UniverseSignCasesProofs
public meta import PskernelC1Independent.UniverseSignCases

public section

open PskernelC1Independent.Level

-- With a zero RHS, any imax collapses regardless of its left operand.
#guard compareSigned (fun _ => false) (.imax (.param 1) (.param 0)) .zero = true
#guard compareSigned (fun id => id == 1) (.imax (.param 1) (.param 0)) .zero = true

-- A known-positive RHS makes imax a max, but the left term still matters.
#guard compareSigned (fun id => id == 0) (.imax (.param 1) (.param 0))
  (.max (.param 1) (.param 0)) = true
-- If only the right parameter is positive, the left is exactly zero:
-- imax(0, succ n) = succ n. With BOTH positive, the left can dominate.
#guard compareSigned (fun id => id == 0) (.imax (.param 1) (.param 0))
  (.param 0) = true
#guard compareSigned (fun _ => true) (.imax (.param 1) (.param 0))
  (.param 0) = false

-- Nested imax, repeated terms, and successor offsets.
#guard compareSigned (fun _ => true)
  (.imax (.param 0) (.imax (.param 1) (.param 2)))
  (.max (.param 0) (.max (.param 1) (.param 2))) = true
#guard compareSigned (fun _ => false)
  (.imax (.param 0) (.imax (.param 1) (.param 2))) .zero = true
#guard compareSigned (fun _ => false)
  (.succ (.imax (.param 0) (.param 1)))
  (.imax (.param 0) (.param 1)) = false
#guard compareSigned (fun _ => true)
  (.succ (.imax (.param 0) (.param 1)))
  (.imax (.param 0) (.param 1)) = false

example (positive : Nat → Bool) (left right : PskernelC1Independent.Level) :
    compareSigned positive left right = true ↔
      ∀ residual, eval (signedAssignment positive residual) left =
        eval (signedAssignment positive residual) right :=
  compareSigned_correct positive left right

#print axioms PskernelC1Independent.Level.zeroAtSigns_spec
#print axioms PskernelC1Independent.Level.compileSigned_eval
#print axioms PskernelC1Independent.Level.compareSigned_correct
#print axioms PskernelC1Independent.Level.compareSigned_successor_different
