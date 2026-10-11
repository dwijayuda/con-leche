module

public import PskernelC1.Soundness

public section

/-!
# The axiom boundary of the owned capstones

These guards pin the axioms in the proof terms. `SetTheory V` remains
an explicit premise of the statements; this audit does not discharge it
or certify Lean's compiler and runtime.
-/

namespace PskernelC1Tests.Axioms

/--
info: 'PskernelC1.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.model_exists

/--
info: 'PskernelC1.chunks_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.chunks_model_exists

/--
info: 'PskernelC1.Accepted.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.Accepted.model_exists

/--
info: 'PskernelC1.AcceptedChunks.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.AcceptedChunks.model_exists

/--
info: 'PskernelC1.AcceptedStream.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.AcceptedStream.model_exists

/--
info: 'PskernelC1.no_False_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.no_False_constant

/--
info: 'PskernelC1.no_Empty_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.no_Empty_constant

/--
info: 'PskernelC1.Accepted.no_False_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.Accepted.no_False_constant

/--
info: 'PskernelC1.AcceptedChunks.no_False_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.AcceptedChunks.no_False_constant

/--
info: 'PskernelC1.AcceptedStream.no_False_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.AcceptedStream.no_False_constant

/--
info: 'PskernelC1.no_False_theorem_accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.no_False_theorem_accepted

/--
info: 'PskernelC1.no_False_parsed_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.no_False_parsed_theorem

/--
info: 'PskernelC1.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PskernelC1.no_False_declaration

end PskernelC1Tests.Axioms
