module

public import PskernelC1Independent.ExprSubst
public import PskernelC1Independent.ExprProofs

public section

/-!
# Correctness of de Bruijn binder instantiation

Proof plan: first show lifting by zero is an identity for all ten
constructors, then induct on the *input expression* and carry the
outer-context depth, the binder offset, and the replacement's scoped
environment as explicit parameters.

At a variable equal to the removed binder, reusing the proven lift
preservation theorem handles arbitrary open replacements. Under
lambdas/foralls/lets, the domain or value remains at the same offset,
whereas the body moves one binder deeper. This prevents variable
capture and is not a collection of special-case tests.
-/

namespace PskernelC1Independent.Expr

/-- Zero raising is the identity, independent of cutoff or binder shape. -/
theorem lift_zero (term : Expr) (cutoff : Nat) : lift 0 cutoff term = term := by
  induction term generalizing cutoff with
  | bvar i =>
    by_cases h : cutoff ≤ i <;> simp [lift, h]
  | fvar i type ih => rfl
  | sort level => rfl
  | const name levels => rfl
  | app function argument ihf iha =>
    simp [lift, ihf cutoff, iha cutoff]
  | lam domain body binder ihd ihb =>
    simp [lift, ihd cutoff, ihb (cutoff + 1)]
  | forallE domain body binder ihd ihb =>
    simp [lift, ihd cutoff, ihb (cutoff + 1)]
  | letE type value body iht ihv ihb =>
    simp [lift, iht cutoff, ihv cutoff, ihb (cutoff + 1)]
  | lit literal => rfl
  | proj name field value ih =>
    simp [lift, ih cutoff]

/-- Raising above every loose bound variable changes nothing.
This applies under arbitrarily nested binders and is the premise for
matching the inherited, closed-replacement instantiation algorithm. -/
theorem lift_above_scope (term : Expr) (db fv cutoff amount : Nat)
    (hc : db ≤ cutoff) (h : Scoped db fv term) :
    lift amount cutoff term = term := by
  induction term generalizing db fv cutoff with
  | bvar i =>
    cases h with
    | bvar hi =>
      have hnot : ¬ cutoff ≤ i := by omega
      simp [lift, hnot]
  | fvar index type ih =>
    rfl
  | sort level => rfl
  | const name levels => rfl
  | app function argument ihf iha =>
    cases h with
    | app hf ha =>
      simp [lift, ihf db fv cutoff hc hf, iha db fv cutoff hc ha]
  | lam domain body binder ihd ihb =>
    cases h with
    | lam hd hb =>
      have hcBody : db + 1 ≤ cutoff + 1 := Nat.add_le_add_right hc 1
      simp [lift, ihd db fv cutoff hc hd,
        ihb (db + 1) fv (cutoff + 1) hcBody hb]
  | forallE domain body binder ihd ihb =>
    cases h with
    | forallE hd hb =>
      have hcBody : db + 1 ≤ cutoff + 1 := Nat.add_le_add_right hc 1
      simp [lift, ihd db fv cutoff hc hd,
        ihb (db + 1) fv (cutoff + 1) hcBody hb]
  | letE type value body iht ihv ihb =>
    cases h with
    | letE ht hv hb =>
      have hcBody : db + 1 ≤ cutoff + 1 := Nat.add_le_add_right hc 1
      simp [lift, iht db fv cutoff hc ht, ihv db fv cutoff hc hv,
        ihb (db + 1) fv (cutoff + 1) hcBody hb]
  | lit literal => rfl
  | proj name field value ih =>
    cases h with
    | proj hv =>
      simp [lift, ih db fv cutoff hc hv]

/-- An fvar-opened, bound-variable-closed argument never needs shifting,
regardless of the number of intervening binders. -/
theorem lift_closed (term : Expr) (fv amount cutoff : Nat)
    (h : Scoped 0 fv term) : lift amount cutoff term = term :=
  lift_above_scope term 0 fv cutoff amount (Nat.zero_le _) h

/-- The first bound variable instantiates to the replacement verbatim. -/
theorem instantiate1_bvar0 (replacement : Expr) :
    instantiate1 (.bvar 0) replacement = replacement := by
  simp [instantiate1, instantiateAt, lift_zero]

/-- At any depth, replacing a well-scoped binder with a well-scoped term
preserves scope of the result. The offset counts intervening binders,
while the outer context remains the replacement's own context. -/
theorem instantiateAt_preserves_scope (term replacement : Expr)
    (outer fv offset : Nat)
    (hreplacement : Scoped outer fv replacement)
    (hterm : Scoped (outer + offset + 1) fv term) :
    Scoped (outer + offset) fv (instantiateAt offset replacement term) := by
  induction term generalizing outer fv offset with
  | bvar index =>
    cases hterm with
    | bvar hi =>
      by_cases hless : index < offset
      · have hs : index < outer + offset := by omega
        simpa [instantiateAt, hless] using
          (Scoped.bvar (db := outer + offset) (fv := fv) hs)
      · by_cases heq : index = offset
        · have hv := lift_preserves_scope replacement outer fv offset 0
            hreplacement (Nat.zero_le outer)
          simpa [instantiateAt, hless, heq] using hv
        · have hs : index - 1 < outer + offset := by omega
          simpa [instantiateAt, hless, heq] using
            (Scoped.bvar (db := outer + offset) (fv := fv) hs)
  | fvar index type ih =>
    cases hterm with
    | fvar hi ht =>
      simpa [instantiateAt] using (Scoped.fvar hi ht)
  | sort level => exact Scoped.sort
  | const name levels => exact Scoped.const
  | app function argument ihf iha =>
    cases hterm with
    | app hf ha =>
      simpa [instantiateAt] using Scoped.app
        (ihf outer fv offset hreplacement hf)
        (iha outer fv offset hreplacement ha)
  | lam domain body binder ihd ihb =>
    cases hterm with
    | lam hd hb =>
      have hd' := ihd outer fv offset hreplacement hd
      have hbInput : Scoped (outer + (offset + 1) + 1) fv body := by
        simpa [Nat.add_assoc] using hb
      have hb' := ihb outer fv (offset + 1) hreplacement hbInput
      have hbResult : Scoped (outer + offset + 1) fv
          (instantiateAt (offset + 1) replacement body) := by
        simpa [Nat.add_assoc] using hb'
      simpa [instantiateAt] using Scoped.lam hd' hbResult
  | forallE domain body binder ihd ihb =>
    cases hterm with
    | forallE hd hb =>
      have hd' := ihd outer fv offset hreplacement hd
      have hbInput : Scoped (outer + (offset + 1) + 1) fv body := by
        simpa [Nat.add_assoc] using hb
      have hb' := ihb outer fv (offset + 1) hreplacement hbInput
      have hbResult : Scoped (outer + offset + 1) fv
          (instantiateAt (offset + 1) replacement body) := by
        simpa [Nat.add_assoc] using hb'
      simpa [instantiateAt] using Scoped.forallE hd' hbResult
  | letE type value body iht ihv ihb =>
    cases hterm with
    | letE ht hv hb =>
      have ht' := iht outer fv offset hreplacement ht
      have hv' := ihv outer fv offset hreplacement hv
      have hbInput : Scoped (outer + (offset + 1) + 1) fv body := by
        simpa [Nat.add_assoc] using hb
      have hb' := ihb outer fv (offset + 1) hreplacement hbInput
      have hbResult : Scoped (outer + offset + 1) fv
          (instantiateAt (offset + 1) replacement body) := by
        simpa [Nat.add_assoc] using hb'
      simpa [instantiateAt] using Scoped.letE ht' hv' hbResult
  | lit literal => exact Scoped.lit
  | proj name field value ih =>
    cases hterm with
    | proj hv =>
      simpa [instantiateAt] using Scoped.proj
        (ih outer fv offset hreplacement hv)

/-- The executable scope test is preserved by actual instantiation. -/
theorem instantiate1_preserves_scope (body replacement : Expr)
    (outer fv : Nat)
    (hbody : checkScoped (outer + 1) fv body = true)
    (hvalue : checkScoped outer fv replacement = true) :
    checkScoped outer fv (instantiate1 body replacement) = true := by
  apply checkScoped_complete
  simpa only [instantiate1, Nat.add_zero] using
    instantiateAt_preserves_scope body replacement outer fv 0
      (checkScoped_sound replacement outer fv hvalue)
      (checkScoped_sound body (outer + 1) fv hbody)

end PskernelC1Independent.Expr
