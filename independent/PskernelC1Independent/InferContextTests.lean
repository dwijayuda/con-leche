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

#guard LocalContext.checkContext ([] : LocalContext) = true
#guard LocalContext.checkContext [(.sort .zero)] = true
#guard LocalContext.checkContext [(.bvar 0)] = false
#guard LocalContext.checkContext
  [(.sort .zero), (.fvar 0 (.sort .zero))] = true
#guard LocalContext.checkContext
  [(.sort .zero), (.fvar 1 (.sort .zero))] = false
#guard inferChecked [(.bvar 0)] (.sort .zero) = .malformedContext
#guard inferChecked [(.sort .zero)] (.fvar 0 (.sort .zero)) =
  .inferred (.sort .zero)
#guard inferChecked [(.sort .zero)] (.fvar 0 (.sort (.succ .zero))) =
  .contextMismatch
#guard inferChecked [(.sort .zero)] (.sort .zero) =
  .inferred (.sort (.succ .zero))

example (context : LocalContext) (term type : Expr) :
    inferHeadIn context term = .inferred type ↔
      ContextHeadDerives context term type :=
  inferHeadIn_iff context term type
