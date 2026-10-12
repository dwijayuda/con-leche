module

import PskernelC1Independent.InferHeadProofs
public meta import PskernelC1Independent.InferHead

public section
open PskernelC1Independent
open PskernelC1Independent.Expr

#guard inferHead 0 (.sort .zero) = .inferred (.sort (.succ .zero))
#guard inferHead 0 (.sort (.imax (.param 0) (.param 1))) =
  .inferred (.sort (.succ (.imax (.param 0) (.param 1))))
#guard inferHead 1 (.fvar 0 (.sort .zero)) = .inferred (.sort .zero)
#guard inferHead 2 (.fvar 1 (.fvar 0 (.sort .zero))) =
  .inferred (.fvar 0 (.sort .zero))
#guard inferHead 0 (.fvar 0 (.sort .zero)) = .invalidScope
#guard inferHead 2 (.fvar 1 (.fvar 1 (.sort .zero))) = .invalidScope
#guard inferHead 2 (.fvar 1 (.bvar 0)) = .invalidScope
#guard inferHead 0 (.bvar 0) = .invalidScope
#guard inferHead 0 (.app (.sort .zero) (.sort .zero)) = .unsupported
#guard inferHead 0 (.lit (.nat 2)) = .unsupported
#guard inferHead 0 (.lam (.sort .zero) (.bvar 0) .never) = .unsupported
#guard inferHead 0 (.lam (.sort .zero) (.bvar 2) .never) = .invalidScope

example (depth : Nat) (term typ : Expr) :
    inferHead depth term = .inferred typ ↔ HeadDerives depth term typ :=
  inferHead_iff depth term typ
example (depth : Nat) (term typ : Expr)
    (h : inferHead depth term = .inferred typ) : Scoped 0 depth typ :=
  inferHead_output_scoped depth term typ h
