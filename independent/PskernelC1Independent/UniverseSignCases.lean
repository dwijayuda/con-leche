module

public import PskernelC1Independent.UniversePolynomial

@[expose] public section

/-!
# An exact semantic reduction of imax to polynomial branches

Every Nat-valued parameter is either zero or one plus a residual Nat.
Fixing these *signs* resolves the zero-test of every imax right operand.
The resulting branch is a max/successor polynomial; no example-specific
rewrite or semantic approximation is involved.

This is a correctness reference for future complete imax comparison.
It is not itself the production comparator: enumerating all sign cases
can be exponential and strict Lean-kernel conversion can be more
restrictive than semantic equivalence.
-/

namespace PskernelC1Independent.Level

/-- Interpret zero-sign parameters as zero, positive-sign parameters as
one plus an arbitrary residual. Every Nat is representable this way. -/
def signedAssignment (positive : Nat → Bool) (residual : Nat → Nat)
    (id : Nat) : Nat :=
  if positive id then residual id + 1 else 0

/-- A syntax-directed zero test for the chosen parameter sign pattern.
For imax, zero-ness depends on the right operand alone. -/
def zeroAtSigns (positive : Nat → Bool) : Level → Bool
  | .zero => true
  | .param id => !(positive id)
  | .succ _ => false
  | .max left right => zeroAtSigns positive left && zeroAtSigns positive right
  | .imax _ right => zeroAtSigns positive right

/-- Every imax on a fixed sign pattern becomes either zero or an
ordinary max. This function always returns a polynomial. -/
def compileSigned (positive : Nat → Bool) : Level → Polynomial
  | .zero => Polynomial.zero
  | .param id =>
      if positive id then Polynomial.successor (Polynomial.parameter id)
      else Polynomial.zero
  | .succ level => Polynomial.successor (compileSigned positive level)
  | .max left right =>
      Polynomial.join (compileSigned positive left) (compileSigned positive right)
  | .imax left right =>
      if zeroAtSigns positive right then Polynomial.zero
      else Polynomial.join (compileSigned positive left) (compileSigned positive right)

/-- Comparison is total on ONE fixed sign pattern. It is not a
global result until the sign patterns for all parameters are covered. -/
def compareSigned (positive : Nat → Bool) (left right : Level) : Bool :=
  Polynomial.equivalent (compileSigned positive left) (compileSigned positive right)

end PskernelC1Independent.Level
