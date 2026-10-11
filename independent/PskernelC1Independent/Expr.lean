module

public import PskernelC1Independent.Universe

@[expose] public section

/-!
# Independently represented kernel expression syntax

Every constructor mirrors a kernel-relevant expression form, including
locally nameless free variables, projections, both literal types, lets,
and binder annotations. An annotation remains untrusted data until
its future inference/checking invariant is proved: list order is NOT
assumed canonical and raw annotation equality is not semantic equality.

The hierarchy and source codec will receive an explicit proof-only
bridge later. This module has no dependency on Lean.Expr or ConLeche.
-/

namespace PskernelC1Independent

inductive Name where
  | anonymous
  | str (prefix : Name) (part : String)
  | num (prefix : Name) (index : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Unvalidated binder proposition-zeroness representation. Later
checking must validate/canonicalize this datum before it affects
conversion or reduction. -/
inductive BinderZero where
  | never
  | allZero (parameterIds : List Nat)
  deriving DecidableEq, Repr

inductive Literal where
  | nat (value : Nat)
  | str (value : String)
  deriving DecidableEq, Repr

/-- Internal bvars are de Bruijn indices, fvars are de Bruijn levels
with an explicit type as in ConLeche; they are distinct constructors. -/
inductive Expr where
  | bvar (index : Nat)
  | fvar (index : Nat) (type : Expr)
  | sort (universe : Level)
  | const (name : Name) (universes : List Level)
  | app (function argument : Expr)
  | lam (domain body : Expr) (binder : BinderZero)
  | forallE (domain body : Expr) (binder : BinderZero)
  | letE (type value body : Expr)
  | lit (literal : Literal)
  | proj (structureName : Name) (field : Nat) (value : Expr)
  deriving DecidableEq, Repr

namespace Expr

/-- Executable syntactic scope validation. Binder domains and let values
are OUTSIDE the introduced binder; only binder bodies are under it.
An fvar has an explicit type that must itself be scoped. -/
def checkScoped (bdepth fdepth : Nat) : Expr → Bool
  | .bvar index => decide (index < bdepth)
  | .fvar index type => decide (index < fdepth) && checkScoped bdepth fdepth type
  | .sort _ | .const _ _ | .lit _ => true
  | .app function argument =>
      checkScoped bdepth fdepth function && checkScoped bdepth fdepth argument
  | .lam domain body _ | .forallE domain body _ =>
      checkScoped bdepth fdepth domain && checkScoped (bdepth + 1) fdepth body
  | .letE type value body =>
      checkScoped bdepth fdepth type && checkScoped bdepth fdepth value &&
        checkScoped (bdepth + 1) fdepth body
  | .proj _ _ value => checkScoped bdepth fdepth value

/-- Capture-avoiding raising of outer de Bruijn indices.
The cutoff rises only when entering a *body*, not in binder domains,
nor in let declaration types or values. -/
def lift (amount cutoff : Nat) : Expr → Expr
  | .bvar index =>
      if cutoff ≤ index then .bvar (index + amount) else .bvar index
  | .fvar index type => .fvar index (lift amount cutoff type)
  | .sort universe => .sort universe
  | .const name universes => .const name universes
  | .app function argument =>
      .app (lift amount cutoff function) (lift amount cutoff argument)
  | .lam domain body binder =>
      .lam (lift amount cutoff domain) (lift amount (cutoff + 1) body) binder
  | .forallE domain body binder =>
      .forallE (lift amount cutoff domain) (lift amount (cutoff + 1) body) binder
  | .letE type value body =>
      .letE (lift amount cutoff type) (lift amount cutoff value)
        (lift amount (cutoff + 1) body)
  | .lit literal => .lit literal
  | .proj structureName field value =>
      .proj structureName field (lift amount cutoff value)

/-- Structural kernel scope judgment, independent of the executable
Boolean check. Scope invariants will become preconditions of inference. -/
inductive Scoped : Nat → Nat → Expr → Prop where
  | bvar {db fv index} : index < db → Scoped db fv (.bvar index)
  | fvar {db fv index type} :
      index < fv → Scoped db fv type → Scoped db fv (.fvar index type)
  | sort {db fv u} : Scoped db fv (.sort u)
  | const {db fv name universes} : Scoped db fv (.const name universes)
  | app {db fv function argument} :
      Scoped db fv function → Scoped db fv argument →
      Scoped db fv (.app function argument)
  | lam {db fv domain body binder} :
      Scoped db fv domain → Scoped (db + 1) fv body →
      Scoped db fv (.lam domain body binder)
  | forallE {db fv domain body binder} :
      Scoped db fv domain → Scoped (db + 1) fv body →
      Scoped db fv (.forallE domain body binder)
  | letE {db fv type value body} :
      Scoped db fv type → Scoped db fv value →
      Scoped (db + 1) fv body → Scoped db fv (.letE type value body)
  | lit {db fv literal} : Scoped db fv (.lit literal)
  | proj {db fv name field value} :
      Scoped db fv value → Scoped db fv (.proj name field value)

end Expr
end PskernelC1Independent
