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
  | sort level => exact Scoped.sort
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

/-- Raising preserves scope for any cutoff inside the ambient binder
depth. Induction is over the expression's structure, so the depth at
each nested binder is explicit and cannot be confused with the
original theorem's outer depth. -/
theorem lift_preserves_scope (term : Expr) (db fv amount cutoff : Nat)
    (h : Scoped db fv term) (hc : cutoff ≤ db) :
    Scoped (db + amount) fv (Expr.lift amount cutoff term) := by
  induction term generalizing db fv cutoff with
  | bvar index =>
    cases h with
    | bvar hi =>
      by_cases hcut : cutoff ≤ index
      · have hb : index + amount < db + amount := by omega
        simpa [Expr.lift, hcut] using
          (Scoped.bvar (db := db + amount) (fv := fv) hb)
      · have hb : index < db + amount := by omega
        simpa [Expr.lift, hcut] using
          (Scoped.bvar (db := db + amount) (fv := fv) hb)
  | fvar index type ih =>
    cases h with
    | fvar hi htype =>
      simpa [Expr.lift] using
        (Scoped.fvar hi (ih db fv cutoff htype hc))
  | sort level =>
    exact Scoped.sort
  | const name levels =>
    exact Scoped.const
  | app function argument ihFunction ihArgument =>
    cases h with
    | app hf ha =>
      simpa [Expr.lift] using
        (Scoped.app (ihFunction db fv cutoff hf hc)
          (ihArgument db fv cutoff ha hc))
  | lam domain body binder ihDomain ihBody =>
    cases h with
    | lam hd hb =>
      have hcBody : cutoff + 1 ≤ db + 1 := by omega
      have hdomain := ihDomain db fv cutoff hd hc
      have hbody := ihBody (db + 1) fv (cutoff + 1) hb hcBody
      have hbody' : Scoped (db + amount + 1) fv (Expr.lift amount (cutoff + 1) body) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody
      simpa [Expr.lift] using Scoped.lam hdomain hbody'
  | forallE domain body binder ihDomain ihBody =>
    cases h with
    | forallE hd hb =>
      have hcBody : cutoff + 1 ≤ db + 1 := by omega
      have hdomain := ihDomain db fv cutoff hd hc
      have hbody := ihBody (db + 1) fv (cutoff + 1) hb hcBody
      have hbody' : Scoped (db + amount + 1) fv (Expr.lift amount (cutoff + 1) body) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody
      simpa [Expr.lift] using Scoped.forallE hdomain hbody'
  | letE type value body ihType ihValue ihBody =>
    cases h with
    | letE ht hv hb =>
      have hcBody : cutoff + 1 ≤ db + 1 := by omega
      have htype := ihType db fv cutoff ht hc
      have hvalue := ihValue db fv cutoff hv hc
      have hbody := ihBody (db + 1) fv (cutoff + 1) hb hcBody
      have hbody' : Scoped (db + amount + 1) fv (Expr.lift amount (cutoff + 1) body) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody
      simpa [Expr.lift] using Scoped.letE htype hvalue hbody'
  | lit literal =>
    exact Scoped.lit
  | proj name field value ih =>
    cases h with
    | proj hvalue =>
      simpa [Expr.lift] using
        (Scoped.proj (ih db fv cutoff hvalue hc))

/-- A usable proof method on the actual structural scope judgment. -/
theorem Scoped.lift {db fv : Nat} {term : Expr}
    (h : Scoped db fv term) (amount cutoff : Nat) (hc : cutoff ≤ db) :
    Scoped (db + amount) fv (Expr.lift amount cutoff term) :=
  lift_preserves_scope term db fv amount cutoff h hc

/-- Executable bound-scope checking cannot be broken by a correct lift. -/
theorem checkScoped_lift (term : Expr) (db fv amount cutoff : Nat)
    (h : checkScoped db fv term = true) (hc : cutoff ≤ db) :
    checkScoped (db + amount) fv (Expr.lift amount cutoff term) = true :=
  checkScoped_complete ((checkScoped_sound term db fv h).lift amount cutoff hc)

end PskernelC1Independent.Expr
