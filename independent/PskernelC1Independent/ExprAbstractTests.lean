module

import PskernelC1Independent.ExprAbstractProofs
public meta import PskernelC1Independent.ExprAbstract

public section

open PskernelC1Independent
open PskernelC1Independent.Expr

#guard abstract1 (.fvar 0 (.sort .zero)) 0 = .bvar 0
#guard abstract1 (.fvar 0 (.sort .zero)) 1 = .fvar 0 (.sort .zero)
#guard abstract1 (.fvar 1 (.fvar 0 (.sort .zero))) 1 = .bvar 0
#guard abstract1 (.lam (.sort .zero) (.fvar 0 (.sort .zero)) .never) 0 =
    .lam (.sort .zero) (.bvar 1) .never
#guard abstract1 (.forallE (.sort .zero) (.fvar 0 (.sort .zero)) .never) 0 =
    .forallE (.sort .zero) (.bvar 1) .never
#guard abstract1 (.letE (.sort .zero) (.fvar 0 (.sort .zero))
                  (.app (.fvar 0 (.sort .zero)) (.bvar 0))) 0 =
    .letE (.sort .zero) (.bvar 0) (.app (.bvar 1) (.bvar 0))
#guard abstract1 (.fvar 1 (.fvar 0 (.sort .zero))) 0 =
    .fvar 1 (.fvar 0 (.sort .zero))
#guard checkScoped 1 0 (abstract1 (.fvar 0 (.sort .zero)) 0) = true
#guard checkScoped 1 0
  (abstract1 (.lam (.sort .zero) (.fvar 0 (.sort .zero)) .never) 0) = true

example (term : Expr) (base target : Nat)
    (h : checkScoped base (target + 1) term = true) :
    checkScoped (base + 1) target (abstract1 term target) = true :=
  checkScoped_abstract1 term base target h
