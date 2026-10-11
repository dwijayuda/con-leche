module

public import PskernelC1Independent.Expr

public section

/-!
# Structural scoping and raising laws

These proofs concern ALL ten constructors. The checker may reuse a
scoping result, but it may not admit a term that violates the judgment.

The local depth for free variables and the bound-variable cutoff are
different quantities. Only bound variables are raised. Scope checking
is a pure decision procedure equivalent to the structural judgment.
-/

namespace PskernelC1Independent.Expr

theorem checkScoped_sound (term : Expr) (db fv : Nat)
    (h : checkScoped db fv term = true) : Scoped db fv term := by
  induction term generalizing db fv with
  | bvar index =>
    exact Scoped.bvar (by simpa [checkScoped] using h)
  | fvar index type ih =>
    have hs : index < fv ∧ checkScoped db fv type = true := by
      simpa [checkScoped, Bool.and_eq_true, decide_eq_true_eq] using h
    exact Scoped.fvar hs.1 (ih db fv hs.2)
  | sort universe => exact Scoped.sort
  | const name universes => exact Scoped.const
  | app function argument ihf iha =>
    have hs : checkScoped db fv function = true ∧
        checkScoped db fv argument = true := by
      simpa [checkScoped, Bool.and_eq_true] using h
    exact Scoped.app (ihf db fv hs.1) (iha db fv hs.2)
  | lam domain body binder ihd ihb =>
    have hs : checkScoped db fv domain = true ∧
        checkScoped (db + 1) fv body = true := by
      simpa [checkScoped, Bool.and_eq_true] using h
    exact Scoped.lam (ihd db fv hs.1) (ihb (db + 1) fv hs.2)
  | forallE domain body binder ihd ihb =>
    have hs : checkScoped db fv domain = true ∧
        checkScoped (db + 1) fv body = true := by
      simpa [checkScoped, Bool.and_eq_true] using h
    exact Scoped.forallE (ihd db fv hs.1) (ihb (db + 1) fv hs.2)
  | letE type value body iht ihv ihb =>
    have hs : checkScoped db fv type = true ∧
        checkScoped db fv value = true ∧
        checkScoped (db + 1) fv body = true := by
      simpa [checkScoped, Bool.and_eq_true, Bool.and_assoc] using h
    exact Scoped.letE (iht db fv hs.1) (ihv db fv hs.2.1)
      (ihb (db + 1) fv hs.2.2)
  | lit literal => exact Scoped.lit
  | proj name field value ih =>
    exact Scoped.proj (ih db fv (by simpa [checkScoped] using h))

theorem checkScoped_complete {db fv : Nat} {term : Expr}
    (h : Scoped db fv term) : checkScoped db fv term = true := by
  induction h with
  | bvar h => simpa [checkScoped] using (show decide (_ < _) = true from decide_eq_true h)
  | fvar h _ ih => simp [checkScoped, h, ih]
  | sort => rfl
  | const => rfl
  | app _ _ ihf iha => simp [checkScoped, ihf, iha]
  | lam _ _ ihd ihb => simp [checkScoped, ihd, ihb]
  | forallE _ _ ihd ihb => simp [checkScoped, ihd, ihb]
  | letE _ _ _ iht ihv ihb => simp [checkScoped, iht, ihv, ihb]
  | lit => rfl
  | proj _ ih => simpa [checkScoped] using ih

theorem checkScoped_iff (db fv : Nat) (term : Expr) :
    checkScoped db fv term = true ↔ Scoped db fv term :=
  ⟨checkScoped_sound term db fv, checkScoped_complete⟩

/-- Raising preserves scope for any cutoff within the current binder
depth. This covers nested binders, let bodies and fvar type annotations. -/
theorem Scoped.lift {db fv : Nat} {term : Expr}
    (h : Scoped db fv term) (amount cutoff : Nat) (hc : cutoff ≤ db) :
    Scoped (db + amount) fv (Expr.lift amount cutoff term) := by
  induction h generalizing cutoff with
  | @bvar db fv index hi =>
    by_cases hcut : cutoff ≤ index
    · simpa [Expr.lift, hcut] using
        (Scoped.bvar (db := db + amount) (fv := fv)
          (show index + amount < db + amount by omega))
    · have hb : index < db + amount := by omega
      simpa [Expr.lift, hcut] using (Scoped.bvar (db := db + amount) (fv := fv) hb)
  | fvar hi _ ih =>
    simpa [Expr.lift] using (Scoped.fvar hi (ih cutoff hc))
  | sort => exact Scoped.sort
  | const => exact Scoped.const
  | app _ _ ihf iha =>
    simpa [Expr.lift] using Scoped.app (ihf cutoff hc) (iha cutoff hc)
  | lam _ _ ihd ihb =>
    have hbody : cutoff + 1 ≤ db + 1 := by omega
    simpa [Expr.lift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Scoped.lam (ihd cutoff hc) (ihb (cutoff + 1) hbody)
  | forallE _ _ ihd ihb =>
    have hbody : cutoff + 1 ≤ db + 1 := by omega
    simpa [Expr.lift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Scoped.forallE (ihd cutoff hc) (ihb (cutoff + 1) hbody)
  | letE _ _ _ iht ihv ihb =>
    have hbody : cutoff + 1 ≤ db + 1 := by omega
    simpa [Expr.lift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Scoped.letE (iht cutoff hc) (ihv cutoff hc) (ihb (cutoff + 1) hbody)
  | lit => exact Scoped.lit
  | proj _ ih =>
    simpa [Expr.lift] using Scoped.proj (ih cutoff hc)

/-- Executable bound-scope checking cannot be broken by a correct lift. -/
theorem checkScoped_lift (term : Expr) (db fv amount cutoff : Nat)
    (h : checkScoped db fv term = true) (hc : cutoff ≤ db) :
    checkScoped (db + amount) fv (Expr.lift amount cutoff term) = true :=
  checkScoped_complete ((checkScoped_sound term db fv h).lift amount cutoff hc)

end PskernelC1Independent.Expr
