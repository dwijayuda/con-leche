module

public import PskernelC1Independent.InferHead
public import PskernelC1Independent.ExprProofs

public section

/-!
# Sound and complete inference for the independently implemented leaf
fragment, plus a reusable monotonicity law for locally-nameless scope.

None of these statements claims a valid environment or a global kernel
model. The reference rules are connected by a separate proof-only
refinement. A future checker must extend this fragment without turning
its `unsupported` response into mathematical rejection.
-/

namespace PskernelC1Independent.Expr

/-- An existing well-scoped expression remains scoped when the ambient
free-variable context is extended by fresh, higher-level variables.
An fvar's own annotation remains scoped at its original index. -/
theorem Scoped.weakenFVars {db fv more : Nat} {term : Expr}
    (h : Scoped db fv term) (hf : fv ≤ more) :
    Scoped db more term := by
  induction h with
  | bvar hi => exact Scoped.bvar hi
  | fvar hi hty ih =>
    exact Scoped.fvar (Nat.lt_of_lt_of_le hi hf) hty
  | sort => exact Scoped.sort
  | const => exact Scoped.const
  | app _ _ ihf iha => exact Scoped.app (ihf hf) (iha hf)
  | lam _ _ ihd ihb => exact Scoped.lam (ihd hf) (ihb hf)
  | forallE _ _ ihd ihb => exact Scoped.forallE (ihd hf) (ihb hf)
  | letE _ _ _ iht ihv ihb => exact Scoped.letE (iht hf) (ihv hf) (ihb hf)
  | lit => exact Scoped.lit
  | proj _ ih => exact Scoped.proj (ih hf)

/-- Successful executable inference constructs a real declarative
head-inference derivation, rather than relying on a runtime flag. -/
theorem inferHead_sound (fdepth : Nat) (term type : Expr)
    (accepted : inferHead fdepth term = .inferred type) :
    HeadDerives fdepth term type := by
  have hscope : checkScoped 0 fdepth term = true := by
    cases hs : checkScoped 0 fdepth term <;>
      simp [inferHead, hs] at accepted ⊢
  cases term with
  | sort level =>
    simp [inferHead, hscope] at accepted
    subst type
    exact HeadDerives.sort level
  | fvar index annotation =>
    have hparts : index < fdepth ∧ checkScoped 0 index annotation = true := by
      simpa [checkScoped, Bool.and_eq_true, decide_eq_true_eq] using hscope
    simp [inferHead, hscope] at accepted
    subst type
    exact HeadDerives.fvar hparts.1
      (checkScoped_sound annotation 0 index hparts.2)
  | bvar index => simp [inferHead, hscope] at accepted
  | const name levels => simp [inferHead, hscope] at accepted
  | app function argument => simp [inferHead, hscope] at accepted
  | lam domain body binder => simp [inferHead, hscope] at accepted
  | forallE domain body binder => simp [inferHead, hscope] at accepted
  | letE type value body => simp [inferHead, hscope] at accepted
  | lit literal => simp [inferHead, hscope] at accepted
  | proj name field value => simp [inferHead, hscope] at accepted

/-- All derivable heads are accepted. This rules out the trivial
always-decline implementation for the covered fragment. -/
theorem inferHead_complete {fdepth : Nat} {term type : Expr}
    (h : HeadDerives fdepth term type) :
    inferHead fdepth term = .inferred type := by
  cases h with
  | sort level => simp [inferHead, checkScoped]
  | @fvar index annotation hi hannotation =>
    have ha := checkScoped_complete hannotation
    simp [inferHead, checkScoped, hi, ha]

theorem inferHead_iff (fdepth : Nat) (term type : Expr) :
    inferHead fdepth term = .inferred type ↔
      HeadDerives fdepth term type :=
  ⟨inferHead_sound fdepth term type, inferHead_complete⟩

/-- An invalid-scope result is genuine failed syntactic scope
validation, not a statement that a well-formed theorem is false. -/
theorem inferHead_invalidScope (fdepth : Nat) (term : Expr)
    (h : inferHead fdepth term = .invalidScope) :
    checkScoped 0 fdepth term = false := by
  cases hs : checkScoped 0 fdepth term with
  | false => rfl
  | true =>
    cases term <;> simp [inferHead, hs] at h

/-- Unsupported is returned only after valid syntactic scoping was
established. This prevents conflating unimplemented syntax with a
malformed variable/context. -/
theorem inferHead_unsupported_scoped (fdepth : Nat) (term : Expr)
    (h : inferHead fdepth term = .unsupported) :
    checkScoped 0 fdepth term = true := by
  cases hs : checkScoped 0 fdepth term with
  | true => rfl
  | false => simp [inferHead, hs] at h

/-- The type returned by this leaf checker is itself properly scoped.
This is a necessary input to the full inference/model proof. -/
theorem inferHead_output_scoped (fdepth : Nat) (term type : Expr)
    (h : inferHead fdepth term = .inferred type) :
    Scoped 0 fdepth type := by
  cases inferHead_sound fdepth term type h with
  | sort level => exact Scoped.sort
  | fvar hi htype => exact htype.weakenFVars (Nat.le_of_lt hi)

end PskernelC1Independent.Expr
