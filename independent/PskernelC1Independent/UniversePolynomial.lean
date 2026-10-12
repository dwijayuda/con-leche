module

public import PskernelC1Independent.Universe

@[expose] public section

/-!
# Complete comparison for the max/successor universe fragment

A polynomial is a maximum of a constant and finitely many parameter-plus-
offset atoms. The representation is deliberately transparent: duplicate
atoms are allowed, and comparison checks dominance rather than relying on
hashes, a sort order, or a hidden canonicalization invariant.

`comparePolynomial` decides all levels built from zero, parameters,
successor and max. An imax requires the separate zero-case analysis and
returns unknown here. The existing sound normalizer may eliminate some
imax nodes before this operation is used. This component does not pretend
that an inconclusive result is inequality.

The list-based dominance pass is a correctness baseline, not a claim of
optimal hot-path performance. A future indexed implementation must refine
these contracts and justify its complexity with measurements.
-/

namespace PskernelC1Independent.Level

structure Atom where
  parameter : Nat
  offset : Nat
  deriving DecidableEq, Repr

def Atom.eval (assignment : Nat → Nat) (atom : Atom) : Nat :=
  assignment atom.parameter + atom.offset

structure Polynomial where
  constant : Nat
  terms : List Atom
  deriving Repr

namespace Polynomial

def evalTerms (assignment : Nat → Nat) (constant : Nat) : List Atom → Nat
  | [] => constant
  | atom :: rest => Nat.max (Atom.eval assignment atom) (evalTerms assignment constant rest)

def eval (assignment : Nat → Nat) (polynomial : Polynomial) : Nat :=
  evalTerms assignment polynomial.constant polynomial.terms

/-- The minimum value over all nonnegative parameter assignments. -/
def least (polynomial : Polynomial) : Nat := eval (fun _ => 0) polynomial

def zero : Polynomial := ⟨0, []⟩

def parameter (id : Nat) : Polynomial := ⟨0, [⟨id, 0⟩]⟩

def successor (polynomial : Polynomial) : Polynomial :=
  ⟨polynomial.constant + 1, polynomial.terms.map (fun atom => { atom with offset := atom.offset + 1 })⟩

def join (left right : Polynomial) : Polynomial :=
  ⟨Nat.max left.constant right.constant, left.terms ++ right.terms⟩

/-- A matching parameter with at least this offset dominates an atom at every assignment. -/
def dominates (right : Polynomial) (atom : Atom) : Bool :=
  right.terms.any (fun other =>
    decide (atom.parameter = other.parameter ∧ atom.offset ≤ other.offset))

/-- Pointwise order: the constant floor and every unbounded parameter contribution. -/
def leq (left right : Polynomial) : Bool :=
  decide (least left ≤ least right) && left.terms.all (dominates right)

def equivalent (left right : Polynomial) : Bool := leq left right && leq right left

end Polynomial

/-- Exact conversion of the imax-free fragment, not a guessed approximation. -/
def toPolynomial : Level → Option Polynomial
  | .zero => some Polynomial.zero
  | .param id => some (Polynomial.parameter id)
  | .succ level => (toPolynomial level).map Polynomial.successor
  | .max left right => do
    let left ← toPolynomial left
    let right ← toPolynomial right
    return Polynomial.join left right
  | .imax _ _ => none

/-- The syntactic fragment for which the complete-comparison theorem applies. -/
def IsPolynomial : Level → Prop
  | .zero | .param _ => True
  | .succ level => IsPolynomial level
  | .max left right => IsPolynomial left ∧ IsPolynomial right
  | .imax _ _ => False

inductive PolynomialResult where
  | equal
  | different
  | unknown
  deriving DecidableEq, Repr

/-- Both conclusive outcomes have proofs. Unknown is reserved for this operation's missing fragment. -/
def comparePolynomial (left right : Level) : PolynomialResult :=
  match toPolynomial left, toPolynomial right with
  | some left, some right =>
    if Polynomial.equivalent left right then .equal else .different
  | _, _ => .unknown

end PskernelC1Independent.Level
