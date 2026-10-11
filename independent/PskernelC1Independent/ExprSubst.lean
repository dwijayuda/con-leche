module

public import PskernelC1Independent.Expr

@[expose] public section

/-!
# Capture-safe single-variable instantiation

The removed binder occurs at the given *index* relative to the current
syntax position. Under a binder body we increase that index. A matching
occurrence is replaced by the input expression raised by exactly that
number of intervening binders; variables above it are decremented.

A locally opened free variable carries a bound-variable-closed type,
which is atomic for this walk, matching ConLeche's actual substitution.

This is one checked operation, not a speculative evaluator. The root
scope theorem establishes the semantic precondition needed to use it in
future beta/zeta reduction and dependent type inference.
-/

namespace PskernelC1Independent.Expr

/-- Substitute the bound variable at `index`; variables beyond the
removed binder decrease by one. This is the general core operation used
by `instantiate1`. -/
def instantiateAt (index : Nat) (replacement : Expr) : Expr → Expr
  | .bvar i =>
      if i < index then .bvar i
      else if i = index then lift index 0 replacement
      else .bvar (i - 1)
  | .fvar i type => .fvar i type
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .app function argument =>
      .app (instantiateAt index replacement function)
        (instantiateAt index replacement argument)
  | .lam domain body binder =>
      .lam (instantiateAt index replacement domain)
        (instantiateAt (index + 1) replacement body) binder
  | .forallE domain body binder =>
      .forallE (instantiateAt index replacement domain)
        (instantiateAt (index + 1) replacement body) binder
  | .letE type value body =>
      .letE (instantiateAt index replacement type)
        (instantiateAt index replacement value)
        (instantiateAt (index + 1) replacement body)
  | .lit literal => .lit literal
  | .proj name field value =>
      .proj name field (instantiateAt index replacement value)

/-- Eliminate the innermost binder. -/
def instantiate1 (body replacement : Expr) : Expr :=
  instantiateAt 0 replacement body

end PskernelC1Independent.Expr
