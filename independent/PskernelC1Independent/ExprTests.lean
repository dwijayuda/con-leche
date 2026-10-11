module

import PskernelC1Independent.ExprProofs
public meta import PskernelC1Independent.Expr

public section

open PskernelC1Independent
open PskernelC1Independent.Expr

#guard checkScoped 0 0 (.bvar 0) = false
#guard checkScoped 1 0 (.bvar 0) = true
#guard checkScoped 0 0 (.lam (.sort .zero) (.bvar 0) .never) = true
#guard checkScoped 0 0 (.lam (.bvar 0) (.bvar 0) .never) = false
#guard checkScoped 0 0 (.forallE (.sort .zero) (.bvar 0) .never) = true
#guard checkScoped 0 0 (.letE (.sort .zero) (.sort .zero) (.bvar 0)) = true
#guard checkScoped 0 0 (.letE (.sort .zero) (.bvar 0) (.bvar 0)) = false
#guard checkScoped 0 0 (.app (.bvar 0) (.sort .zero)) = false
#guard checkScoped 0 0 (.fvar 0 (.sort .zero)) = false
#guard checkScoped 0 1 (.fvar 0 (.sort .zero)) = true
#guard checkScoped 0 1 (.fvar 0 (.bvar 0)) = false
#guard checkScoped 1 1 (.fvar 0 (.bvar 0)) = true
#guard checkScoped 0 0 (.proj .anonymous 0 (.bvar 0)) = false
#guard checkScoped 0 0 (.lit (.nat 9)) = true
#guard checkScoped 0 0 (.lit (.str "ok")) = true
#guard checkScoped 0 0 (.const (.num .anonymous 42) [.param 1]) = true
#guard checkScoped 0 0 (.sort (.imax (.param 0) (.param 1))) = true

-- Under a binder, index 0 remains locally bound, index 1 is raised.
#guard lift 1 0 (.lam (.sort .zero) (.app (.bvar 0) (.bvar 1)) .never) =
  (.lam (.sort .zero) (.app (.bvar 0) (.bvar 2)) .never)
#guard lift 2 0 (.letE (.sort .zero) (.bvar 0) (.app (.bvar 0) (.bvar 1))) =
  (.letE (.sort .zero) (.bvar 2) (.app (.bvar 0) (.bvar 3)))
#guard lift 2 0 (.fvar 1 (.bvar 0)) = (.fvar 1 (.bvar 2))
#guard lift 100 0 (.lam (.sort .zero) (.bvar 0) .never) =
  (.lam (.sort .zero) (.bvar 0) .never)
#guard checkScoped 3 2
  (.forallE (.fvar 0 (.bvar 1)) (.proj .anonymous 0 (.bvar 0)) .never) = true

example (db fv : Nat) (e : Expr) :
    checkScoped db fv e = true ↔ Scoped db fv e :=
  checkScoped_iff db fv e

example (db fv n cutoff : Nat) (e : Expr) (h : checkScoped db fv e = true)
    (hc : cutoff ≤ db) :
    checkScoped (db + n) fv (lift n cutoff e) = true :=
  checkScoped_lift e db fv n cutoff h hc
