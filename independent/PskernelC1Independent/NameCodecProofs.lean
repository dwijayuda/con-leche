module

public import PskernelC1Independent.NameCodec

public section

/-!
# Source-name codec contracts

No assumption that the table contains distinct entries is needed.
Every successful encode really decodes to its original value. Two
different source names cannot share an ID, and adding names AFTER an
existing entry does not renumber its first occurrence.
-/

namespace PskernelC1Independent.NameCodec

universe u
variable {α : Type u}

/-- Every successfully decoded name actually occurs in the finite table. -/
theorem get?_mem (table : List α) (id : Nat) (name : α)
    (decoded : get? table id = some name) : name ∈ table := by
  induction table generalizing id with
  | nil => simp [get?] at decoded
  | cons head tail ih =>
    cases id with
    | zero =>
      simp [get?] at decoded
      subst name
      simp
    | succ id =>
      exact List.mem_cons_of_mem _ (ih id (by simpa [get?] using decoded))

/-- Encoding never aliases a source name to another source name. -/
theorem index?_sound [DecidableEq α] (table : List α) (name : α) (id : Nat)
    (encoded : index? table name = some id) : get? table id = some name := by
  induction table generalizing id with
  | nil => simp [index?] at encoded
  | cons head tail ih =>
    by_cases heq : name = head
    · simp [index?, heq] at encoded
      subst id
      simp [get?, heq]
    · cases htail : index? tail name with
      | none => simp [index?, heq, htail] at encoded
      | some k =>
        simp [index?, heq, htail] at encoded
        subst id
        simpa [get?] using ih k htail

/-- Every source name in the finite input table has a valid encoded ID. -/
theorem index?_complete [DecidableEq α] (table : List α) (name : α)
    (present : name ∈ table) : ∃ id, index? table name = some id := by
  induction table with
  | nil => cases present
  | cons head tail ih =>
    by_cases heq : name = head
    · exact ⟨0, by simp [index?, heq]⟩
    · have htail : name ∈ tail := by
        rcases List.mem_cons.mp present with h | h
        · exact (heq h).elim
        · exact h
      obtain ⟨id, hid⟩ := ih htail
      exact ⟨Nat.succ id, by simp [index?, heq, hid]⟩

/-- An absent name cannot be encoded as some other name's index. -/
theorem index?_none_iff [DecidableEq α] (table : List α) (name : α) :
    index? table name = none ↔ name ∉ table := by
  constructor
  · intro absent present
    obtain ⟨id, found⟩ := index?_complete table name present
    rw [absent] at found
    cases found
  · intro absent
    cases found : index? table name with
    | none => rfl
    | some id =>
      exact (absent (get?_mem table id name (index?_sound table name id found))).elim

/-- Equality of internal IDs entails equality of source names, even if
    the supplied finite table contains duplicate entries. -/
theorem index?_injective [DecidableEq α] (table : List α)
    (first second : α) (id : Nat)
    (hfirst : index? table first = some id)
    (hsecond : index? table second = some id) : first = second := by
  have a := index?_sound table first id hfirst
  have b := index?_sound table second id hsecond
  exact Option.some.inj (a.symm.trans b)

/-- Appending new names cannot change an already published source ID. -/
theorem index?_append_left [DecidableEq α] (table extra : List α)
    (name : α) (id : Nat) (h : index? table name = some id) :
    index? (table ++ extra) name = some id := by
  induction table generalizing id with
  | nil => simp [index?] at h
  | cons head tail ih =>
    by_cases heq : name = head
    · simp [index?, heq] at h
      subst id
      simp [index?, heq]
    · cases ht : index? tail name with
      | none => simp [index?, heq, ht] at h
      | some k =>
        simp [index?, heq, ht] at h
        subst id
        simpa [index?, heq] using congrArg (Option.map Nat.succ) (ih k ht)

end PskernelC1Independent.NameCodec
