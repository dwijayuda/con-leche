module

import PskernelC1Independent.UniversePolynomialProofs
import PskernelC1Independent.PolynomialTests
import PskernelC1Independent.NameCodecTests
-- Non-public imports in the test module are not re-exported into this root.
import PskernelC1Independent.NameCodecProofs
-- #guard evaluates these functions during elaboration as well as using their
-- logical definitions; the module system requires an explicit meta import.
public meta import PskernelC1Independent.Universe

public section

open PskernelC1Independent
open PskernelC1Independent.Level

-- All five constructors and both impredicative branches.
#guard eval (fun _ => 4) .zero = 0
#guard eval (fun _ => 4) (.param 91) = 4
#guard eval (fun _ => 4) (.succ (.param 91)) = 5
#guard eval (fun id => id) (.max (.param 3) (.param 9)) = 9
#guard eval (fun _ => 0) (.imax (.succ (.succ .zero)) (.param 8)) = 0
#guard eval (fun _ => 1) (.imax (.succ (.succ .zero)) (.param 8)) = 2
#guard eval (fun _ => 5) (.imax (.param 0) (.succ .zero)) = 5

-- Replacement is simultaneous: the inserted parameter is not rewritten again.
#guard substitute (fun id => .param (id + 1)) (.param 0) = .param 1
#guard substitute (fun id => .succ (.param id)) (.imax (.param 0) (.param 1)) =
  .imax (.succ (.param 0)) (.succ (.param 1))
#guard rename (fun id => id + 7) (.max (.param 0) (.param 3)) =
  .max (.param 7) (.param 10)

-- Sound positive simplifications and explicit incompleteness.
#guard normalize (.max .zero (.param 3)) = .param 3
#guard normalize (.max (.param 3) .zero) = .param 3
#guard normalize (.imax (.param 3) .zero) = .zero
#guard normalize (.imax .zero (.succ (.param 4))) = .succ (.param 4)
#guard compareFast (.max .zero (.param 3)) (.param 3) = .equal
#guard compareFast (.imax (.param 3) .zero) .zero = .equal
#guard compareFast (.succ .zero) .zero = .unknown
#guard compareFast (.param 0) (.param 1) = .unknown
#guard compareFast (.max (.param 0) (.param 1)) (.max (.param 1) (.param 0)) = .unknown
#guard compareFast (.imax (.param 0) (.param 1)) (.max (.param 0) (.param 1)) = .unknown

example (l : Level) : Equivalent l (normalize l) := normalize_sound l
example (a b : Level) (h : compareFast a b = .equal) : Equivalent a b :=
  compareFast_sound a b h

#print axioms eval_substitute
#print axioms substitute_identity
#print axioms substitute_compose
#print axioms eval_rename
#print axioms eval_maxSmart
#print axioms eval_imaxSmart
#print axioms eval_normalize
#print axioms normalize_sound
#print axioms compareFast_sound
#print axioms compareFast_reflexive
#print axioms unknown_can_be_equivalent
#print axioms toPolynomial_sound
#print axioms comparePolynomial_sound
#print axioms comparePolynomial_different
#print axioms comparePolynomial_complete
#print axioms comparePolynomial_decides

-- The whole independent package's axiom census lives at one root.
#print axioms PskernelC1Independent.NameCodec.get?_mem
#print axioms PskernelC1Independent.NameCodec.index?_sound
#print axioms PskernelC1Independent.NameCodec.index?_complete
#print axioms PskernelC1Independent.NameCodec.index?_none_iff
#print axioms PskernelC1Independent.NameCodec.index?_injective
#print axioms PskernelC1Independent.NameCodec.index?_append_left
