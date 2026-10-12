module

public import PskernelC1Independent.ExprAbstract
public import PskernelC1Independent.ExprProofs

public section

/-!
# Soundness of closing an opened binder

The input is scoped under target+1 fvar levels (the new fvar and all
earlier ones), with base+cursor bound-variable levels. Closing the
target removes that fvar from scope and adds one bound-variable level.
This is proved for the actual recursive algorithm, including nested
binders and opaque fvar-type annotations.
-/

namespace PskernelC1Independent.Expr

theorem abstractAt_preserves_scope
    (term : Expr) (base target cursor : Nat)
    (h : Scoped (base + cursor) (target + 1) term) :
    Scoped (base + cursor + 1) target (abstractAt target cursor term) := by
  induction term generalizing base cursor with
  | bvar index =>
    cases h with
    | bvar hi =>
      have hi' : index < base + cursor + 1 := by omega
      simpa [abstractAt] using
        (Scoped.bvar (db := base + cursor + 1) (fv := target) hi')
  | fvar index type ih =>
    cases h with
    | fvar hi ht =>
      by_cases heq : index = target
      · have hcursor : cursor < base + cursor + 1 := by omega
        simpa [abstractAt, heq] using
          (Scoped.bvar (db := base + cursor + 1) (fv := target) hcursor)
      · have hin : index < target := by omega
        simpa [abstractAt, heq] using
          (Scoped.fvar (db := base + cursor + 1) (fv := target) hin ht)
  | sort level => exact Scoped.sort
  | const name levels => exact Scoped.const
  | app function argument ihf iha =>
    cases h with
    | app hf ha =>
      simpa [abstractAt] using
        (Scoped.app (ihf base cursor hf) (iha base cursor ha))
  | lam domain body binder ihd ihb =>
    cases h with
    | lam hd hb =>
      have hbody : Scoped (base + (cursor + 1)) (target + 1) body := by
        simpa [Nat.add_assoc] using hb
      have bodyResult := ihb base (cursor + 1) hbody
      have bodyScoped : Scoped (base + cursor + 1 + 1) target
          (abstractAt target (cursor + 1) body) := by
        simpa [Nat.add_assoc] using bodyResult
      simpa [abstractAt] using
        (Scoped.lam (ihd base cursor hd) bodyScoped)
  | forallE domain body binder ihd ihb =>
    cases h with
    | forallE hd hb =>
      have hbody : Scoped (base + (cursor + 1)) (target + 1) body := by
        simpa [Nat.add_assoc] using hb
      have bodyResult := ihb base (cursor + 1) hbody
      have bodyScoped : Scoped (base + cursor + 1 + 1) target
          (abstractAt target (cursor + 1) body) := by
        simpa [Nat.add_assoc] using bodyResult
      simpa [abstractAt] using
        (Scoped.forallE (ihd base cursor hd) bodyScoped)
  | letE type value body iht ihv ihb =>
    cases h with
    | letE ht hv hb =>
      have hbody : Scoped (base + (cursor + 1)) (target + 1) body := by
        simpa [Nat.add_assoc] using hb
      have bodyResult := ihb base (cursor + 1) hbody
      have bodyScoped : Scoped (base + cursor + 1 + 1) target
          (abstractAt target (cursor + 1) body) := by
        simpa [Nat.add_assoc] using bodyResult
      simpa [abstractAt] using
        (Scoped.letE (iht base cursor ht) (ihv base cursor hv) bodyScoped)
  | lit literal => exact Scoped.lit
  | proj name field value ih =>
    cases h with
    | proj hv =>
      simpa [abstractAt] using (Scoped.proj (ih base cursor hv))

/-- Actual single-binder root operation preserves the scope judgment. -/
theorem abstract1_preserves_scope (term : Expr) (base target : Nat)
    (h : Scoped base (target + 1) term) :
    Scoped (base + 1) target (abstract1 term target) := by
  simpa [abstract1] using abstractAt_preserves_scope term base target 0
    (by simpa only [Nat.add_zero] using h)

/-- Executable source-level scope certificate, no admitted proof token. -/
theorem checkScoped_abstract1 (term : Expr) (base target : Nat)
    (h : checkScoped base (target + 1) term = true) :
    checkScoped (base + 1) target (abstract1 term target) = true :=
  checkScoped_complete (abstract1_preserves_scope term base target
    (checkScoped_sound term base (target + 1) h))

end PskernelC1Independent.Expr
