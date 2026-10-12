module

public import ConLeche.Kernel.ExprOps
public import PskernelC1Independent.ExprSubstProofs

public section

/-!
# Independent expression to reference-kernel operation refinement

Proof-only bridge: the executable independent package does not import
ConLeche. Source names, universe parameter IDs, all ten term constructors
and binder-zero annotations are explicitly translated.

A reference bound-variable instantiation never shifts its replacement.
Its documented precondition is that the replacement is closed against
loose bound variables. Our independently implemented instantiator is
capture-safe even for open replacements. The theorem below only asserts
agreement in the *shared supported domain* where the replacement is
proved closed. This does not claim full type inference, validated
annotations, model soundness or runtime independence from Lean.
-/

namespace PskernelC1ExprBridge

open PskernelC1Independent

/-- Exact representation of an independently owned hierarchical name. -/
@[expose] def nameToReference : Name → ConLeche.Name
  | .anonymous => .anonymous
  | .str parent label => .str (nameToReference parent) label
  | .num parent index => .num (nameToReference parent) index

/-- Map all five universe constructors under explicit parameter names. -/
@[expose] def levelToReference (names : Nat → ConLeche.Name) : Level → ConLeche.Level
  | .zero => .zero
  | .succ level => .succ (levelToReference names level)
  | .max left right => .max (levelToReference names left) (levelToReference names right)
  | .imax left right => .imax (levelToReference names left) (levelToReference names right)
  | .param index => .param (names index)

/-- This is a representation translation only. Semantic validation of the
resulting proposition-zero datum remains the responsibility of checking. -/
@[expose] def binderToReference (names : Nat → ConLeche.Name) :
    BinderZero → ConLeche.BinderMeta
  | .never => ⟨.never⟩
  | .allZero ids => ⟨ConLeche.PropWhen.ifAllZero (ids.map names)⟩

@[expose] def literalToReference : Literal → ConLeche.Literal
  | .nat value => .natVal value
  | .str value => .strVal value

/-- Pure translation: it never invokes ConLeche's checker or converter. -/
@[expose] def exprToReference (names : Nat → ConLeche.Name) : Expr → ConLeche.Expr
  | .bvar index => .bvar index
  | .fvar index type => .fvar index (exprToReference names type)
  | .sort level => .sort (levelToReference names level)
  | .const name levels => .const (nameToReference name) (levels.map (levelToReference names))
  | .app function argument =>
      .app (exprToReference names function) (exprToReference names argument)
  | .lam domain body binder =>
      .lam (exprToReference names domain) (exprToReference names body)
        (binderToReference names binder)
  | .forallE domain body binder =>
      .forallE (exprToReference names domain) (exprToReference names body)
        (binderToReference names binder)
  | .letE type value body =>
      .letE (exprToReference names type) (exprToReference names value)
        (exprToReference names body)
  | .lit literal => .lit (literalToReference literal)
  | .proj name field value =>
      .proj (nameToReference name) field (exprToReference names value)

/-- The reference expression's bound-variable test follows the already
checked independent structural scope judgment. Free-variable type
annotations are atomic to both traversals. -/
theorem scoped_reference_bvars (names : Nat → ConLeche.Name)
    {db fv : Nat} {term : Expr} (scoped : Expr.Scoped db fv term) :
    ConLeche.Expr.looseBVarsBounded db (exprToReference names term) = true := by
  induction scoped with
  | bvar hi =>
    simpa [exprToReference, ConLeche.Expr.looseBVarsBounded] using
      (show decide (_ < _) = true from decide_eq_true hi)
  | fvar hi htype ih =>
    rfl
  | sort => rfl
  | const => rfl
  | app hf ha ihf iha =>
    simp [exprToReference, ConLeche.Expr.looseBVarsBounded, ihf, iha]
  | lam hd hb ihd ihb =>
    simp [exprToReference, ConLeche.Expr.looseBVarsBounded, ihd, ihb]
  | forallE hd hb ihd ihb =>
    simp [exprToReference, ConLeche.Expr.looseBVarsBounded, ihd, ihb]
  | letE ht hv hb iht ihv ihb =>
    simp [exprToReference, ConLeche.Expr.looseBVarsBounded, iht, ihv, ihb]
  | lit => rfl
  | proj hv ih =>
    simpa [exprToReference, ConLeche.Expr.looseBVarsBounded] using ih

/-- Refinement of the actual independent executable operation.
This uses ConLeche's executable reference *definition*, not its result
as an oracle to admit new C1 checking outcomes. -/
theorem instantiateAt_reference_closed (names : Nat → ConLeche.Name)
    (replacement term : Expr) (fv : Nat)
    (closed : Expr.Scoped 0 fv replacement) :
    ∀ offset : Nat,
      exprToReference names (Expr.instantiateAt offset replacement term) =
        ConLeche.Expr.instantiate1
          (exprToReference names term) (exprToReference names replacement) offset := by
  induction term with
  | bvar index =>
    intro offset
    by_cases heq : index = offset
    · subst index
      have hzero : Expr.lift offset 0 replacement = replacement :=
        Expr.lift_closed replacement fv offset 0 closed
      simp [Expr.instantiateAt, ConLeche.Expr.instantiate1, exprToReference, hzero]
    · by_cases hlt : index < offset
      · have hnot : ¬ index > offset := by omega
        simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
          exprToReference, heq, hlt, hnot]
      · have hgreater : index > offset := by omega
        simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
          exprToReference, heq, hlt, hgreater]
  | fvar index type ih =>
    intro offset
    rfl
  | sort level => intro offset; rfl
  | const name levels => intro offset; rfl
  | app function argument ihf iha =>
    intro offset
    simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
      exprToReference, ihf offset, iha offset]
  | lam domain body binder ihd ihb =>
    intro offset
    simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
      exprToReference, ihd offset, ihb (offset + 1)]
  | forallE domain body binder ihd ihb =>
    intro offset
    simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
      exprToReference, ihd offset, ihb (offset + 1)]
  | letE type value body iht ihv ihb =>
    intro offset
    simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
      exprToReference, iht offset, ihv offset, ihb (offset + 1)]
  | lit literal => intro offset; rfl
  | proj name field value ih =>
    intro offset
    simp [Expr.instantiateAt, ConLeche.Expr.instantiate1,
      exprToReference, ih offset]

/-- The central binder-opening theorem, at the public root entry point. -/
theorem instantiate1_reference_closed (names : Nat → ConLeche.Name)
    (replacement body : Expr) (fv : Nat)
    (closed : Expr.Scoped 0 fv replacement) :
    exprToReference names (Expr.instantiate1 body replacement) =
      ConLeche.Expr.instantiate1
        (exprToReference names body) (exprToReference names replacement) := by
  exact instantiateAt_reference_closed names replacement body fv closed 0

/-- The executable Boolean scope validation is sufficient to invoke
the operational refinement; this does not assume a hidden proof token. -/
theorem instantiate1_checked_reference (names : Nat → ConLeche.Name)
    (replacement body : Expr) (fv : Nat)
    (closed : Expr.checkScoped 0 fv replacement = true) :
    exprToReference names (Expr.instantiate1 body replacement) =
      ConLeche.Expr.instantiate1
        (exprToReference names body) (exprToReference names replacement) :=
  instantiate1_reference_closed names replacement body fv
    (Expr.checkScoped_sound replacement 0 fv closed)

-- The artifact audits exactly these four proof obligations.
#print axioms scoped_reference_bvars
#print axioms instantiateAt_reference_closed
#print axioms instantiate1_reference_closed
#print axioms instantiate1_checked_reference

end PskernelC1ExprBridge
