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

/-- The entire executable context check is EQUIVALENT to
the lookup-indexed syntactic context invariant, including every tail
entry and its actual fvar level. -/
theorem checkFrom_correct (start : Nat) (context : LocalContext) :
    checkFrom start context = true ↔
      ∀ index type, lookup context index = some type →
        Expr.Scoped 0 (start + index) type := by
  induction context generalizing start with
  | nil =>
    constructor
    · intro _ index type h
      cases index <;> simp [lookup] at h
    · intro _
      rfl
  | cons head rest ih =>
    constructor
    · intro h index type found
      have hparts : Expr.checkScoped 0 start head = true ∧
          checkFrom (start + 1) rest = true := by
        simpa [checkFrom, Bool.and_eq_true] using h
      cases index with
      | zero =>
        have heq : type = head := by simpa [lookup] using found.symm
        subst type
        simpa using (Expr.checkScoped_sound head 0 start hparts.1)
      | succ index =>
        have ht : lookup rest index = some type := by
          simpa [lookup] using found
        have htail := (ih (start + 1)).mp hparts.2 index type ht
        simpa [Nat.add_assoc] using htail
    · intro h
      apply Bool.and_eq_true.mpr
      constructor
      · apply Expr.checkScoped_complete
        have hh := h 0 head (by simp [lookup])
        simpa using hh
      · apply (ih (start + 1)).mpr
        intro index type found
        have hh := h (index + 1) type (by simpa [lookup] using found)
        simpa [Nat.add_assoc] using hh

theorem checkContext_correct (context : LocalContext) :
    checkContext context = true ↔ WellScoped context := by
  simpa [checkContext, WellScoped, Nat.zero_add] using
    checkFrom_correct 0 context

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

/-- A context-checked leaf judgment refines the original local
inference rule, with the missing premise discharged by the actual
bounded context lookup. This is not the missing global CtxOk/model. -/
theorem ContextHeadDerives.toHeadDerives (context : LocalContext)
    {term type : Expr} (h : ContextHeadDerives context term type) :
    HeadDerives context.length term type := by
  cases h with
  | sort level => exact HeadDerives.sort level
  | fvar hlookup hscope =>
    exact HeadDerives.fvar (LocalContext.lookup_bounded _ _ _ hlookup) hscope

/-- Successful contextual inference refines the ordinary independent
head-inference executable judgment, never vice versa without context. -/
theorem inferHeadIn_toHead (context : LocalContext) (term type : Expr)
    (h : inferHeadIn context term = .inferred type) :
    inferHead context.length term = .inferred type := by
  exact inferHead_complete
    ((inferHeadIn_sound context term type h).toHeadDerives context)

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

/-- Global syntactic-context validity and locally contextual
inference both follow from successful executable checking. A model
invariant for the stored types is still a separate obligation. -/
theorem inferChecked_sound (context : LocalContext) (term type : Expr)
    (accepted : inferChecked context term = .inferred type) :
    LocalContext.WellScoped context ∧
      ContextHeadDerives context term type := by
  by_cases hc : LocalContext.checkContext context = true
  · have hinfer : inferHeadIn context term = .inferred type := by
      simpa [inferChecked, hc] using accepted
    exact ⟨(LocalContext.checkContext_correct context).mp hc,
      inferHeadIn_sound context term type hinfer⟩
  · simp [inferChecked, hc] at accepted

theorem inferChecked_complete (context : LocalContext) {term type : Expr}
    (valid : LocalContext.WellScoped context)
    (h : ContextHeadDerives context term type) :
    inferChecked context term = .inferred type := by
  have hv := (LocalContext.checkContext_correct context).mpr valid
  simp [inferChecked, hv, inferHeadIn_complete context h]

theorem inferChecked_iff (context : LocalContext) (term type : Expr) :
    inferChecked context term = .inferred type ↔
      LocalContext.WellScoped context ∧
        ContextHeadDerives context term type := by
  constructor
  · exact inferChecked_sound context term type
  · rintro ⟨valid, derived⟩
    exact inferChecked_complete context valid derived

end Expr
end PskernelC1Independent
