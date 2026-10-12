module

public import PskernelC1Independent.InferContext
public import PskernelC1Independent.InferHeadProofs

public section

/-!
# Exact local-context lookup and soundness/completeness of contextual
leaf inference. This is structural consistency, not an environment
model, and so it cannot justify arbitrary source axioms.
-/

namespace PskernelC1Independent

namespace LocalContext

/-- If a type is stored at index, that index is in the context. -/
theorem lookup_bounded (context : LocalContext) (index : Nat)
    (type : Expr) (h : lookup context index = some type) :
    index < context.length := by
  induction context generalizing index with
  | nil =>
    cases index <;> simp [lookup] at h
  | cons head more ih =>
    cases index with
    | zero => simp
    | succ index =>
      have htail : lookup more index = some type := by
        simpa [lookup] using h
      have hb := ih index htail
      simpa using Nat.succ_lt_succ hb

/-- A context cannot assign two distinct types at the same index. -/
theorem lookup_unique (context : LocalContext) (index : Nat)
    (first second : Expr)
    (a : lookup context index = some first)
    (b : lookup context index = some second) : first = second :=
  Option.some.inj (a.symm.trans b)

end LocalContext

namespace Expr

/-- Every successful result has a declarative derivation tied to the
actual registered local-variable type. -/
theorem inferHeadIn_sound (context : LocalContext) (term type : Expr)
    (accepted : inferHeadIn context term = .inferred type) :
    ContextHeadDerives context term type := by
  cases term with
  | sort level =>
    have ht : Expr.sort (.succ level) = type := by
      simpa [inferHeadIn, inferHead, checkScoped] using accepted
    subst type
    exact ContextHeadDerives.sort level
  | fvar index annotation =>
    by_cases hs : checkScoped 0 context.length (.fvar index annotation) = true
    · have hparts : index < context.length ∧
          checkScoped 0 index annotation = true := by
        simpa [checkScoped, Bool.and_eq_true, decide_eq_true_eq] using hs
      by_cases hm : LocalContext.lookup context index = some annotation
      · have ht : annotation = type := by
          simpa [inferHeadIn, inferHead, hs, hm] using accepted
        subst type
        exact ContextHeadDerives.fvar hm
          (checkScoped_sound annotation 0 index hparts.2)
      · simp [inferHeadIn, inferHead, hs, hm] at accepted
    · simp [inferHeadIn, inferHead, hs] at accepted
  | bvar index =>
    simp [inferHeadIn, inferHead, checkScoped] at accepted
  | const name levels =>
    cases hs : checkScoped 0 context.length (.const name levels) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | app function argument =>
    cases hs : checkScoped 0 context.length (.app function argument) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | lam domain body binder =>
    cases hs : checkScoped 0 context.length (.lam domain body binder) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | forallE domain body binder =>
    cases hs : checkScoped 0 context.length (.forallE domain body binder) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | letE annotation value body =>
    cases hs : checkScoped 0 context.length (.letE annotation value body) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | lit value =>
    cases hs : checkScoped 0 context.length (.lit value) <;>
      simp [inferHeadIn, inferHead, hs] at accepted
  | proj name field value =>
    cases hs : checkScoped 0 context.length (.proj name field value) <;>
      simp [inferHeadIn, inferHead, hs] at accepted

/-- Completeness for exactly the two supported, context-justified rules:
an always-decline implementation would fail this theorem. -/
theorem inferHeadIn_complete (context : LocalContext)
    {term type : Expr} (h : ContextHeadDerives context term type) :
    inferHeadIn context term = .inferred type := by
  cases h with
  | sort level => simp [inferHeadIn, inferHead, checkScoped]
  | fvar hlookup hscope =>
    have hb := LocalContext.lookup_bounded _ _ _ hlookup
    have hsc := checkScoped_complete hscope
    simp [inferHeadIn, inferHead, checkScoped, hb, hsc, hlookup]

theorem inferHeadIn_iff (context : LocalContext) (term type : Expr) :
    inferHeadIn context term = .inferred type ↔
      ContextHeadDerives context term type :=
  ⟨inferHeadIn_sound context term type, inferHeadIn_complete context⟩

/-- No two different outputs can be accepted for one input/context. -/
theorem inferHeadIn_unique (context : LocalContext) (term first second : Expr)
    (a : inferHeadIn context term = .inferred first)
    (b : inferHeadIn context term = .inferred second) : first = second :=
  Option.some.inj (by
    have h : ContextOutcome.inferred first = ContextOutcome.inferred second :=
      a.symm.trans b
    exact congrArg (fun x => match x with
      | .inferred v => some v
      | _ => none) h)

end Expr
end PskernelC1Independent
