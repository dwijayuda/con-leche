module

import PskernelC1Independent.ExprSubstProofs
public meta import PskernelC1Independent.ExprSubst

public section

open PskernelC1Independent
open PskernelC1Independent.Expr

#guard instantiate1 (.bvar 0) (.lit (.nat 7)) = .lit (.nat 7)
#guard instantiate1 (.bvar 1) (.lit (.nat 7)) = .bvar 0
#guard instantiate1 (.app (.bvar 0) (.bvar 1)) (.lit (.nat 7)) =
  .app (.lit (.nat 7)) (.bvar 0)
#guard instantiate1 (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)) .never)
    (.lit (.nat 7)) =
  .lam (.sort .zero) (.app (.lit (.nat 7)) (.bvar 0)) .never
#guard instantiate1 (.forallE (.sort .zero) (.app (.bvar 1) (.bvar 0)) .never)
    (.lit (.nat 7)) =
  .forallE (.sort .zero) (.app (.lit (.nat 7)) (.bvar 0)) .never
#guard instantiate1 (.letE (.sort .zero) (.bvar 0) (.app (.bvar 1) (.bvar 0)))
    (.lit (.nat 7)) =
  .letE (.sort .zero) (.lit (.nat 7)) (.app (.lit (.nat 7)) (.bvar 0))
#guard instantiate1 (.proj .anonymous 0 (.bvar 0)) (.lit (.nat 7)) =
  .proj .anonymous 0 (.lit (.nat 7))
#guard instantiate1 (.fvar 1 (.bvar 0)) (.lit (.nat 7)) =
  .fvar 1 (.lit (.nat 7))

-- An open replacement's bound variables must be raised under lambdas.
#guard instantiate1 (.lam (.sort .zero) (.bvar 1) .never) (.bvar 0) =
  .lam (.sort .zero) (.bvar 1) .never
#guard instantiate1 (.lam (.sort .zero) (.bvar 0) .never) (.bvar 0) =
  .lam (.sort .zero) (.bvar 0) .never
#guard checkScoped 1 0
  (instantiate1 (.lam (.sort .zero) (.bvar 1) .never) (.bvar 0)) = true
#guard checkScoped 0 0
  (instantiate1 (.lam (.sort .zero) (.bvar 1) .never) (.lit (.nat 7))) = true

example (value : Expr) : instantiate1 (.bvar 0) value = value :=
  instantiate1_bvar0 value

example (body value : Expr) (outer fv : Nat)
    (hb : checkScoped (outer + 1) fv body = true)
    (hv : checkScoped outer fv value = true) :
    checkScoped outer fv (instantiate1 body value) = true :=
  instantiate1_preserves_scope body value outer fv hb hv
