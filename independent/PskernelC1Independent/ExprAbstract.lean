module

public import PskernelC1Independent.Expr

@[expose] public section

/-!
# Closing a fresh free variable over a binder

A lambda/forall body may be checked in an opened context, with
`fvar d ty` representing the new binder. Closing that body replaces
that free-variable level with `bvar k`, raising `k` under each
intervening binder. The fvar annotation is atomic, exactly as the
independent scoping invariant and inherited kernel require.

This is the inverse-direction building block of locally nameless
binder checking, not a complete type-inference algorithm.
-/

namespace PskernelC1Independent.Expr

/-- Close one free variable, retaining all other constructors unchanged. -/
def abstractAt (target cursor : Nat) : Expr → Expr
  | .bvar index => .bvar index
  | .fvar index type =>
      if index = target then .bvar cursor else .fvar index type
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .app function argument =>
      .app (abstractAt target cursor function) (abstractAt target cursor argument)
  | .lam domain body binder =>
      .lam (abstractAt target cursor domain)
        (abstractAt target (cursor + 1) body) binder
  | .forallE domain body binder =>
      .forallE (abstractAt target cursor domain)
        (abstractAt target (cursor + 1) body) binder
  | .letE type value body =>
      .letE (abstractAt target cursor type)
        (abstractAt target cursor value)
        (abstractAt target (cursor + 1) body)
  | .lit literal => .lit literal
  | .proj name field value =>
      .proj name field (abstractAt target cursor value)

/-- Close the newest free variable into a binder's innermost bvar. -/
def abstract1 (term : Expr) (target : Nat) : Expr :=
  abstractAt target 0 term

end PskernelC1Independent.Expr
