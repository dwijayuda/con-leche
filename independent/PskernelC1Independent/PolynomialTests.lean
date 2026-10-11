module

import PskernelC1Independent.UniversePolynomialProofs
public meta import PskernelC1Independent.UniversePolynomial

public section

open PskernelC1Independent
open PskernelC1Independent.Level

#guard comparePolynomial .zero .zero = .equal
#guard comparePolynomial (.param 0) (.param 0) = .equal
#guard comparePolynomial (.param 0) (.param 1) = .different
#guard comparePolynomial (.param 0) .zero = .different
#guard comparePolynomial .zero (.succ .zero) = .different
#guard comparePolynomial (.max (.param 0) (.param 1)) (.max (.param 1) (.param 0)) = .equal
#guard comparePolynomial (.max (.max (.param 0) (.param 1)) (.param 2))
  (.max (.param 0) (.max (.param 2) (.param 1))) = .equal
#guard comparePolynomial (.max (.param 0) (.param 0)) (.param 0) = .equal
#guard comparePolynomial (.succ (.max (.param 0) (.param 1)))
  (.max (.succ (.param 0)) (.succ (.param 1))) = .equal
#guard comparePolynomial (.max (.succ (.param 0)) (.param 0)) (.succ (.param 0)) = .equal
#guard comparePolynomial (.max (.succ .zero) (.param 0)) (.param 0) = .different
#guard comparePolynomial (.max (.succ (.succ .zero)) (.param 0))
  (.max (.succ .zero) (.param 0)) = .different
#guard comparePolynomial (.max (.succ .zero) (.succ (.param 0))) (.succ (.param 0)) = .equal
#guard comparePolynomial (.imax (.param 0) (.param 1)) (.max (.param 0) (.param 1)) = .unknown
#guard comparePolynomial (.imax (.param 0) (.param 1)) (.imax (.param 0) (.param 1)) = .unknown
#guard comparePolynomial (normalize (.imax (.param 0) (.succ (.param 1))))
  (.max (.param 0) (.succ (.param 1))) = .equal

example (left right : Level) (hleft : IsPolynomial left) (hright : IsPolynomial right) :
    comparePolynomial left right = .equal ↔ Equivalent left right :=
  comparePolynomial_complete left right hleft hright

example (left right : Level) (h : comparePolynomial left right = .different) :
    ¬ Equivalent left right := comparePolynomial_different left right h
