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
  have hh : ∃ inferred, inferHead context.length term = .inferred inferred := by
    unfold inferHeadIn at accepted
    cases hc : inferHead context.length term with
    | inferred inferred => exact ⟨inferred, rfl⟩
    | invalidScope => simp [hc] at accepted
    | unsupported => simp [hc] at accepted
  obtain ⟨inferred, hinfer⟩ := hh
  have base := inferHead_sound context.length term inferred hinfer
  cases base with
  | sort level =>
    simp [inferHeadIn, hinfer] at accepted
    subst type
    exact ContextHeadDerives.sort level
  | fvar hb hscope =>
    by_cases hlookup : LocalContext.lookup context index = some inferred
    · simp [inferHeadIn, hinfer, hlookup] at accepted
      subst type
      exact ContextHeadDerives.fvar hlookup hscope
    · simp [inferHeadIn, hinfer, hlookup] at accepted

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
