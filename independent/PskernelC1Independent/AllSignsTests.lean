module

import PskernelC1Independent.UniverseAllSignsProofs
public meta import PskernelC1Independent.UniverseAllSigns

public section
open PskernelC1Independent.Level

-- All cases, not just one favorable parameter assignment.
#guard compareExhaustive .zero .zero = true
#guard compareExhaustive (.param 0) (.param 1) = false
#guard compareExhaustive (.max (.param 0) (.param 1))
  (.max (.param 1) (.param 0)) = true
#guard compareExhaustive (.imax (.param 0) (.param 1))
  (.imax (.param 0) (.param 1)) = true
#guard compareExhaustive (.imax (.param 0) (.param 1))
  (.max (.param 0) (.param 1)) = false
#guard compareExhaustive (.imax (.param 0) (.succ (.param 1)))
  (.max (.param 0) (.succ (.param 1))) = true
#guard compareExhaustive (.succ (.imax (.param 0) (.param 1)))
  (.imax (.param 0) (.param 1)) = false

example (left right : PskernelC1Independent.Level) :
    compareExhaustive left right = true ↔ Equivalent left right :=
  compareExhaustive_correct left right
