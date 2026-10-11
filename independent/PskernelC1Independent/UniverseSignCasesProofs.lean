module

public import PskernelC1Independent.UniverseSignCases
public import PskernelC1Independent.UniversePolynomialProofs

public section

/-!
# Proof of the imax sign-case compiler

The only decomposition is Nat = 0 OR Nat = successor.
The zero-test proof is for every residual assignment and every imax
nesting. Complete polynomial equivalence can then be reused unchanged.
No finite testing assumption or new axiom is introduced.
-/

namespace PskernelC1Independent.Level

/-- The syntactic zero flag is exact under its chosen sign assignment. -/
theorem zeroAtSigns_spec (positive : Nat → Bool) (residual : Nat → Nat)
    (level : Level) :
    zeroAtSigns positive level = true ↔
      eval (signedAssignment positive residual) level = 0 := by
  induction level with
  | zero =>
    simp [zeroAtSigns, eval]
  | param id =>
    cases h : positive id <;>
      simp [zeroAtSigns, signedAssignment, eval, h]
  | succ level ih =>
    simp [zeroAtSigns, eval]
  | max left right ihLeft ihRight =>
    simp only [zeroAtSigns, Bool.and_eq_true, eval]
    constructor
    · rintro ⟨hl, hr⟩
      rw [ihLeft.mp hl, ihRight.mp hr]
      rfl
    · intro h
      have hl : eval (signedAssignment positive residual) left = 0 :=
        Nat.eq_zero_of_le_zero (by
          calc
            eval (signedAssignment positive residual) left ≤
                Nat.max (eval (signedAssignment positive residual) left)
                  (eval (signedAssignment positive residual) right) :=
              Nat.le_max_left _ _
            _ = 0 := h)
      have hr : eval (signedAssignment positive residual) right = 0 :=
        Nat.eq_zero_of_le_zero (by
          calc
            eval (signedAssignment positive residual) right ≤
                Nat.max (eval (signedAssignment positive residual) left)
                  (eval (signedAssignment positive residual) right) :=
              Nat.le_max_right _ _
            _ = 0 := h)
      exact ⟨ihLeft.mpr hl, ihRight.mpr hr⟩
  | imax left right ihLeft ihRight =>
    simp only [zeroAtSigns, eval]
    constructor
    · intro hz
      simp [ihRight.mp hz]
    · intro hz
      by_cases hr : eval (signedAssignment positive residual) right = 0
      · exact ihRight.mpr hr
      · have hbound := Nat.le_max_right
          (eval (signedAssignment positive residual) left)
          (eval (signedAssignment positive residual) right)
        simp [hr] at hz

/-- The branch compilation preserves evaluation for EVERY residual
assignment; positive variables are genuinely arbitrary successors. -/
theorem compileSigned_eval (positive : Nat → Bool) (residual : Nat → Nat)
    (level : Level) :
    Polynomial.eval residual (compileSigned positive level) =
      eval (signedAssignment positive residual) level := by
  induction level with
  | zero => rfl
  | param id =>
    cases h : positive id <;>
      simp [compileSigned, Polynomial.eval_zero, Polynomial.eval_successor,
        Polynomial.eval_parameter, signedAssignment, eval, h]
  | succ level ih =>
    simp [compileSigned, Polynomial.eval_successor, eval, ih]
  | max left right ihLeft ihRight =>
    simp [compileSigned, Polynomial.eval_join, eval, ihLeft, ihRight]
  | imax left right ihLeft ihRight =>
    by_cases hzero : zeroAtSigns positive right = true
    · have hright := (zeroAtSigns_spec positive residual right).mp hzero
      simp [compileSigned, hzero, Polynomial.eval_zero, eval, hright]
    · have hright : eval (signedAssignment positive residual) right ≠ 0 := by
        intro hz
        exact hzero ((zeroAtSigns_spec positive residual right).mpr hz)
      simp [compileSigned, hzero, Polynomial.eval_join, eval, ihLeft,
        ihRight, hright]

/-- Exact soundness AND completeness for a single fixed sign pattern.
The global comparator must cover all patterns used by its input. -/
theorem compareSigned_correct (positive : Nat → Bool) (left right : Level) :
    compareSigned positive left right = true ↔
      ∀ residual, eval (signedAssignment positive residual) left =
        eval (signedAssignment positive residual) right := by
  constructor
  · intro accepted residual
    have h := Polynomial.equivalent_sound
      (compileSigned positive left) (compileSigned positive right) accepted residual
    simpa only [compileSigned_eval] using h
  · intro equal
    apply Polynomial.equivalent_complete
    intro residual
    rw [compileSigned_eval, compileSigned_eval]
    exact equal residual

/-- A crucial general negative regression: a successor must never be
identified with its predecessor, even through nested imax. -/
theorem compareSigned_successor_different (positive : Nat → Bool) (level : Level) :
    compareSigned positive (.succ level) level = false := by
  cases h : compareSigned positive (.succ level) level with
  | false => rfl
  | true =>
    have same := (compareSigned_correct positive (.succ level) level).mp h
      (fun _ => 0)
    simp only [eval] at same
    omega

end PskernelC1Independent.Level
