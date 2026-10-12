module

import PskernelC1Independent.InferContextProofs
public meta import PskernelC1Independent.InferContext

public section

open PskernelC1Independent
open PskernelC1Independent.Expr

#guard LocalContext.lookup ([.sort .zero, .fvar 0 (.sort .zero)] : List Expr) 0 =
  some (.sort .zero)
#guard LocalContext.lookup ([.sort .zero] : List Expr) 1 = none
#guard inferHeadIn [(.sort .zero)] (.fvar 0 (.sort .zero)) =
  .inferred (.sort .zero)
#guard inferHeadIn [(.sort .zero)] (.fvar 0 (.sort (.succ .zero))) =
  .contextMismatch
#guard inferHeadIn [(.sort .zero)] (.fvar 1 (.sort .zero)) =
  .invalidScope
#guard inferHeadIn [(.sort .zero)] (.sort .zero) =
  .inferred (.sort (.succ .zero))
#guard inferHeadIn [(.sort .zero)] (.lit (.nat 42)) = .unsupported
#guard inferHeadIn [(.sort .zero)] (.lam (.sort .zero) (.bvar 5) .never) =
  .invalidScope
#guard inferHeadIn [(.sort .zero), (.fvar 0 (.sort .zero))]
    (.fvar 1 (.fvar 0 (.sort .zero))) =
  .inferred (.fvar 0 (.sort .zero))

example (context : LocalContext) (term type : Expr) :
    inferHeadIn context term = .inferred type ↔
      ContextHeadDerives context term type :=
  inferHeadIn_iff context term type
