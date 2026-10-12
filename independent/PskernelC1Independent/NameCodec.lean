module

@[expose] public section

/-!
# Finite source-name codec

An exported identifier may appear more than once in the input. We assign
its FIRST table position as a stable internal ID. The table may contain
duplicates without compromising decoding or name separation.

The executable representation is intentionally plain: a list and a natural
index. A faster lookup table can later refine these laws without changing
their meaning. Decoding is partial; an invalid ID never silently acquires
the identity of some other source name.
-/

namespace PskernelC1Independent.NameCodec

universe u
variable {α : Type u}

/-- Total as a function; a missing index returns none rather than a name. -/
def get? : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, id + 1 => get? tail id

/-- The first matching position, if it exists. No default or hash alias. -/
def index? [DecidableEq α] (table : List α) (name : α) : Option Nat :=
  match table with
  | [] => none
  | head :: tail =>
    if name = head then some 0 else (index? tail name).map Nat.succ

end PskernelC1Independent.NameCodec
