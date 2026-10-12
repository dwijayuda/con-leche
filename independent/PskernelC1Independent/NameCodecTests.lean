module

import PskernelC1Independent.NameCodecProofs
public meta import PskernelC1Independent.NameCodec

public section

open PskernelC1Independent

#guard NameCodec.index? ([7, 4, 7] : List Nat) 7 = some 0
#guard NameCodec.index? ([7, 4, 7] : List Nat) 4 = some 1
#guard NameCodec.index? ([7, 4, 7] : List Nat) 9 = none
#guard NameCodec.get? ([7, 4, 7] : List Nat) 2 = some 7
#guard NameCodec.get? ([7, 4, 7] : List Nat) 3 = none
#guard NameCodec.index? (([7, 4] : List Nat) ++ [7, 9]) 4 = some 1
#guard NameCodec.index? ([7, 4, 7] : List Nat) 7 =
    NameCodec.index? ([7] : List Nat) 7

example {α : Type} [DecidableEq α] (table : List α) (a b : α) (id : Nat)
    (ha : NameCodec.index? table a = some id)
    (hb : NameCodec.index? table b = some id) : a = b :=
  NameCodec.index?_injective table a b id ha hb

example {α : Type} [DecidableEq α] (table more : List α) (value : α)
    (id : Nat) (h : NameCodec.index? table value = some id) :
    NameCodec.index? (table ++ more) value = some id :=
  NameCodec.index?_append_left table more value id h

