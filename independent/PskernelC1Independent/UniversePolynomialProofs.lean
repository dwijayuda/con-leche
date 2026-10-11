module

public import PskernelC1Independent.UniversePolynomial
public import PskernelC1Independent.UniverseProofs

public section

/-!
# Polynomial universe contracts

The crucial completeness argument is an explicit separating assignment:
if the right side has no dominating occurrence of a left parameter, set
that parameter above the entire right-side floor and every other parameter
to zero. Then every right atom is strictly below that left atom.

This proves the actual finite dominance procedure, without assuming
canonical lists, unique atoms, or a field asserting soundness/completeness.
-/

namespace PskernelC1Independent.Level
namespace Polynomial

theorem evalTerms_constant (assignment : Nat → Nat) (constant : Nat) :
    ∀ terms, constant ≤ evalTerms assignment constant terms
  | [] => Nat.le_refl _
  | atom :: rest => Nat.le_trans (evalTerms_constant assignment constant rest)
      (Nat.le_max_right _ _)

theorem evalTerms_term (assignment : Nat → Nat) (constant : Nat) :
    ∀ terms atom, atom ∈ terms → Atom.eval assignment atom ≤ evalTerms assignment constant terms
  | [], _, h => by cases h
  | head :: rest, atom, h => by
    rcases List.mem_cons.mp h with heq | hrest
    · subst atom
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (evalTerms_term assignment constant rest atom hrest)
        (Nat.le_max_right _ _)

theorem evalTerms_le (assignment : Nat → Nat) (constant bound : Nat) :
    ∀ terms, constant ≤ bound →
      (∀ atom ∈ terms, Atom.eval assignment atom ≤ bound) →
      evalTerms assignment constant terms ≤ bound
  | [], hconstant, _ => hconstant
  | atom :: rest, hconstant, hatoms => by
    have hhead := hatoms atom (by simp)
    have hrest := evalTerms_le assignment constant bound rest hconstant
      (fun other h => hatoms other (by simp [h]))
    change Nat.max (Atom.eval assignment atom) (evalTerms assignment constant rest) ≤ bound
    omega

theorem evalTerms_lt (assignment : Nat → Nat) (constant bound : Nat) :
    ∀ terms, constant < bound →
      (∀ atom ∈ terms, Atom.eval assignment atom < bound) →
      evalTerms assignment constant terms < bound
  | [], hconstant, _ => hconstant
  | atom :: rest, hconstant, hatoms => by
    have hhead := hatoms atom (by simp)
    have hrest := evalTerms_lt assignment constant bound rest hconstant
      (fun other h => hatoms other (by simp [h]))
    change Nat.max (Atom.eval assignment atom) (evalTerms assignment constant rest) < bound
    omega

theorem evalTerms_mono (first second : Nat → Nat)
    (ordered : ∀ id, first id ≤ second id) (constant : Nat) :
    ∀ terms, evalTerms first constant terms ≤ evalTerms second constant terms
  | [] => Nat.le_refl _
  | atom :: rest => by
    have hhead : Atom.eval first atom ≤ Atom.eval second atom :=
      Nat.add_le_add_right (ordered atom.parameter) atom.offset
    have hrest := evalTerms_mono first second ordered constant rest
    change Nat.max (Atom.eval first atom) (evalTerms first constant rest) ≤
      Nat.max (Atom.eval second atom) (evalTerms second constant rest)
    omega

theorem constant_le_least (polynomial : Polynomial) : polynomial.constant ≤ least polynomial :=
  evalTerms_constant (fun _ => 0) polynomial.constant polynomial.terms

theorem least_le_eval (assignment : Nat → Nat) (polynomial : Polynomial) :
    least polynomial ≤ eval assignment polynomial :=
  evalTerms_mono (fun _ => 0) assignment (fun id => Nat.zero_le (assignment id))
    polynomial.constant polynomial.terms

theorem offset_le_least (polynomial : Polynomial) (atom : Atom) (member : atom ∈ polynomial.terms) :
    atom.offset ≤ least polynomial := by
  simpa only [Atom.eval, Nat.zero_add] using
    evalTerms_term (fun _ => 0) polynomial.constant polynomial.terms atom member

theorem evalTerms_baseMax (assignment : Nat → Nat) (first second : Nat) :
    ∀ terms, evalTerms assignment (Nat.max first second) terms =
      Nat.max first (evalTerms assignment second terms)
  | [] => rfl
  | atom :: rest => by
    simp only [evalTerms]
    rw [evalTerms_baseMax assignment first second rest]
    omega

theorem evalTerms_append (assignment : Nat → Nat) (first second : Nat) :
    ∀ left right, evalTerms assignment (Nat.max first second) (left ++ right) =
      Nat.max (evalTerms assignment first left) (evalTerms assignment second right)
  | [], right => evalTerms_baseMax assignment first second right
  | atom :: rest, right => by
    simp only [List.cons_append, evalTerms]
    rw [evalTerms_append assignment first second rest right]
    omega

theorem evalTerms_successor (assignment : Nat → Nat) (constant : Nat) :
    ∀ terms, evalTerms assignment (constant + 1)
      (terms.map (fun atom => { atom with offset := atom.offset + 1 })) =
      evalTerms assignment constant terms + 1
  | [] => rfl
  | atom :: rest => by
    simp only [List.map_cons, evalTerms]
    rw [evalTerms_successor assignment constant rest]
    simp only [Atom.eval]
    omega

theorem eval_zero (assignment : Nat → Nat) : eval assignment zero = 0 := rfl

theorem eval_parameter (assignment : Nat → Nat) (id : Nat) :
    eval assignment (parameter id) = assignment id := by
  simp [eval, parameter, evalTerms, Atom.eval]

theorem eval_successor (assignment : Nat → Nat) (polynomial : Polynomial) :
    eval assignment (successor polynomial) = eval assignment polynomial + 1 :=
  evalTerms_successor assignment polynomial.constant polynomial.terms

theorem eval_join (assignment : Nat → Nat) (left right : Polynomial) :
    eval assignment (join left right) = Nat.max (eval assignment left) (eval assignment right) :=
  evalTerms_append assignment left.constant right.constant left.terms right.terms

theorem dominates_sound (right : Polynomial) (atom : Atom) (accepted : dominates right atom = true) :
    ∀ assignment, Atom.eval assignment atom ≤ eval assignment right := by
  simp only [dominates, List.any_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨other, member, same, offset⟩ := accepted
  intro assignment
  have hterm := evalTerms_term assignment right.constant right.terms other member
  have hhead : Atom.eval assignment atom ≤ Atom.eval assignment other := by
    simp only [Atom.eval, same]
    omega
  exact Nat.le_trans hhead hterm

theorem leq_sound (left right : Polynomial) (accepted : leq left right = true) :
    ∀ assignment, eval assignment left ≤ eval assignment right := by
  simp only [leq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  intro assignment
  apply evalTerms_le assignment left.constant (eval assignment right) left.terms
  · exact Nat.le_trans (constant_le_least left)
      (Nat.le_trans accepted.1 (least_le_eval assignment right))
  · intro atom member
    exact dominates_sound right atom (accepted.2 atom member) assignment

/-- Completeness follows from a concrete separating parameter assignment. -/
theorem leq_complete (left right : Polynomial)
    (ordered : ∀ assignment, eval assignment left ≤ eval assignment right) :
    leq left right = true := by
  classical
  simp only [leq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · exact ordered (fun _ => 0)
  · intro atom member
    have exists_dominator : ∃ other ∈ right.terms,
        atom.parameter = other.parameter ∧ atom.offset ≤ other.offset := by
      by_contra absent
      let probe : Nat → Nat := fun id => if id = atom.parameter then least right + 1 else 0
      have own : Atom.eval probe atom = least right + 1 + atom.offset := by
        simp [Atom.eval, probe]
      have hconstant : right.constant < Atom.eval probe atom := by
        have hfloor := constant_le_least right
        rw [own]
        omega
      have hatoms : ∀ other ∈ right.terms, Atom.eval probe other < Atom.eval probe atom := by
        intro other present
        by_cases same : other.parameter = atom.parameter
        · have hoffset : other.offset < atom.offset := by
            by_contra notLess
            have hle : atom.offset ≤ other.offset := by omega
            exact absent ⟨other, present, same.symm, hle⟩
          have hvalue : Atom.eval probe other = least right + 1 + other.offset := by
            simp [Atom.eval, probe, same]
          rw [own, hvalue]
          omega
        · have hfloor := offset_le_least right other present
          have hvalue : Atom.eval probe other = other.offset := by
            simp [Atom.eval, probe, same]
          rw [own, hvalue]
          omega
      have hright := evalTerms_lt probe right.constant (Atom.eval probe atom)
        right.terms hconstant hatoms
      have hleft := evalTerms_term probe left.constant left.terms atom member
      have horder := ordered probe
      change eval probe right < Atom.eval probe atom at hright
      change Atom.eval probe atom ≤ eval probe left at hleft
      omega
    simpa only [dominates, List.any_eq_true, decide_eq_true_eq] using exists_dominator

theorem equivalent_sound (left right : Polynomial) (accepted : equivalent left right = true) :
    ∀ assignment, eval assignment left = eval assignment right := by
  obtain ⟨forward, backward⟩ := Bool.and_eq_true.mp accepted
  intro assignment
  exact Nat.le_antisymm (leq_sound left right forward assignment)
    (leq_sound right left backward assignment)

theorem equivalent_complete (left right : Polynomial)
    (same : ∀ assignment, eval assignment left = eval assignment right) :
    equivalent left right = true := by
  apply Bool.and_eq_true.mpr
  exact ⟨leq_complete left right (fun assignment => Nat.le_of_eq (same assignment)),
    leq_complete right left (fun assignment => Nat.le_of_eq (same assignment).symm)⟩

end Polynomial

theorem toPolynomial_sound (level : Level) (polynomial : Polynomial)
    (converted : toPolynomial level = some polynomial) :
    ∀ assignment, Polynomial.eval assignment polynomial = eval assignment level := by
  induction level generalizing polynomial with
  | zero =>
    simp only [toPolynomial, Option.some.injEq] at converted
    subst polynomial
    exact Polynomial.eval_zero
  | param id =>
    simp only [toPolynomial, Option.some.injEq] at converted
    subst polynomial
    exact fun assignment => Polynomial.eval_parameter assignment id
  | succ level ih =>
    cases hlevel : toPolynomial level with
    | none => simp [toPolynomial, hlevel] at converted
    | some inner =>
      simp [toPolynomial, hlevel] at converted
      subst polynomial
      intro assignment
      rw [Polynomial.eval_successor, ih inner hlevel assignment]
      rfl
  | max left right ihleft ihright =>
    cases hleft : toPolynomial left with
    | none => simp [toPolynomial, hleft] at converted
    | some first =>
      cases hright : toPolynomial right with
      | none => simp [toPolynomial, hleft, hright] at converted
      | some second =>
        simp [toPolynomial, hleft, hright] at converted
        subst polynomial
        intro assignment
        rw [Polynomial.eval_join, ihleft first hleft assignment, ihright second hright assignment]
        rfl
  | imax _ _ _ _ => simp [toPolynomial] at converted

theorem toPolynomial_total (level : Level) (covered : IsPolynomial level) :
    ∃ polynomial, toPolynomial level = some polynomial := by
  induction level with
  | zero => exact ⟨Polynomial.zero, rfl⟩
  | param id => exact ⟨Polynomial.parameter id, rfl⟩
  | succ level ih =>
    obtain ⟨inner, hinner⟩ := ih covered
    exact ⟨Polynomial.successor inner, by simp [toPolynomial, hinner]⟩
  | max left right ihleft ihright =>
    obtain ⟨first, hfirst⟩ := ihleft covered.1
    obtain ⟨second, hsecond⟩ := ihright covered.2
    exact ⟨Polynomial.join first second, by simp [toPolynomial, hfirst, hsecond]⟩
  | imax _ _ _ _ => exact False.elim covered

/-- Every positive result is semantic equality at all assignments. -/
theorem comparePolynomial_sound (left right : Level)
    (accepted : comparePolynomial left right = .equal) : Equivalent left right := by
  cases hleft : toPolynomial left with
  | none => simp [comparePolynomial, hleft] at accepted
  | some first =>
    cases hright : toPolynomial right with
    | none => simp [comparePolynomial, hleft, hright] at accepted
    | some second =>
      by_cases heq : Polynomial.equivalent first second = true
      · intro assignment
        calc
          eval assignment left = Polynomial.eval assignment first :=
            (toPolynomial_sound left first hleft assignment).symm
          _ = Polynomial.eval assignment second := Polynomial.equivalent_sound first second heq assignment
          _ = eval assignment right := toPolynomial_sound right second hright assignment
      · simp [comparePolynomial, hleft, hright, heq] at accepted

/-- A negative result cannot discard a semantically equivalent universe. -/
theorem comparePolynomial_different (left right : Level)
    (different : comparePolynomial left right = .different) : ¬ Equivalent left right := by
  intro same
  cases hleft : toPolynomial left with
  | none => simp [comparePolynomial, hleft] at different
  | some first =>
    cases hright : toPolynomial right with
    | none => simp [comparePolynomial, hleft, hright] at different
    | some second =>
      have equalPolynomials : ∀ assignment,
          Polynomial.eval assignment first = Polynomial.eval assignment second := by
        intro assignment
        rw [toPolynomial_sound left first hleft assignment,
            toPolynomial_sound right second hright assignment]
        exact same assignment
      have heq := Polynomial.equivalent_complete first second equalPolynomials
      simp [comparePolynomial, hleft, hright, heq] at different

/-- Completeness, not only soundness, for the complete max/successor fragment. -/
theorem comparePolynomial_complete (left right : Level)
    (coveredLeft : IsPolynomial left) (coveredRight : IsPolynomial right) :
    comparePolynomial left right = .equal ↔ Equivalent left right := by
  constructor
  · exact comparePolynomial_sound left right
  · intro same
    obtain ⟨first, hfirst⟩ := toPolynomial_total left coveredLeft
    obtain ⟨second, hsecond⟩ := toPolynomial_total right coveredRight
    have heq := Polynomial.equivalent_complete first second (fun assignment => by
      rw [toPolynomial_sound left first hfirst assignment,
          toPolynomial_sound right second hsecond assignment]
      exact same assignment)
    simp [comparePolynomial, hfirst, hsecond, heq]

/-- The covered fragment always has a conclusive result. -/
theorem comparePolynomial_decides (left right : Level)
    (coveredLeft : IsPolynomial left) (coveredRight : IsPolynomial right) :
    comparePolynomial left right ≠ .unknown := by
  obtain ⟨first, hfirst⟩ := toPolynomial_total left coveredLeft
  obtain ⟨second, hsecond⟩ := toPolynomial_total right coveredRight
  cases heq : Polynomial.equivalent first second <;>
    simp [comparePolynomial, hfirst, hsecond, heq]

end PskernelC1Independent.Level
