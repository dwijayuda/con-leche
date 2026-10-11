module

public import PskernelC1Independent.UniverseAllSigns
public import PskernelC1Independent.UniverseSignCasesProofs

public section

/-!
# Completeness of the finite sign enumeration

Every input assignment has a matching zero/positive pattern in the
finite list and an appropriate successor residual for every parameter.
The exact branch polynomial theorem then gives global equivalence.
Conversely, any failure of a branch witnesses a real semantic
inequality. This is a proof reference for an optimized comparator.
-/

namespace PskernelC1Independent.Level

/-- A universe reads an assignment only at its own parameter IDs. -/
theorem eval_ext_parameterIds (level : Level) (first second : Nat → Nat)
    (same : ∀ id ∈ parameterIds level, first id = second id) :
    eval first level = eval second level := by
  induction level with
  | zero => rfl
  | param id =>
    exact same id (by simp [parameterIds])
  | succ level ih =>
    have inner := ih (by
      intro id present
      exact same id (by simpa [parameterIds] using present))
    simpa [eval] using congrArg Nat.succ inner
  | max left right ihLeft ihRight =>
    have hl := ihLeft (by
      intro id present
      exact same id (by simp [parameterIds, present]))
    have hr := ihRight (by
      intro id present
      exact same id (by simp [parameterIds, present]))
    simp [eval, hl, hr]
  | imax left right ihLeft ihRight =>
    have hl := ihLeft (by
      intro id present
      exact same id (by simp [parameterIds, present]))
    have hr := ihRight (by
      intro id present
      exact same id (by simp [parameterIds, present]))
    simp [eval, hl, hr]

/-- Decomposition of every natural assignment into its sign and residual. -/
theorem signed_reconstruct (assignment : Nat → Nat) (id : Nat) :
    signedAssignment (signsOf assignment) (residualOf assignment) id =
      assignment id := by
  by_cases h : assignment id = 0
  · simp [signedAssignment, signsOf, h]
  · simp [signedAssignment, signsOf, residualOf, h]
    omega

/-- Every target sign pattern is represented on all parameter IDs in the
finite list, even if it repeats an ID. -/
theorem signPatterns_cover (ids : List Nat) (target : Nat → Bool) :
    ∃ flags ∈ signPatterns ids, ∀ id ∈ ids, flags id = target id := by
  induction ids with
  | nil =>
    refine ⟨fun _ => false, by simp [signPatterns], ?_⟩
    intro id present
    cases present
  | cons key rest ih =>
    obtain ⟨flags, hflags, hrest⟩ := ih
    let chosen := setSign flags key (target key)
    refine ⟨chosen, ?_, ?_⟩
    · cases hv : target key with
      | false =>
        simp only [signPatterns, List.mem_append]
        left
        exact List.mem_map.mpr ⟨flags, hflags, by simp [chosen, hv]⟩
      | true =>
        simp only [signPatterns, List.mem_append]
        right
        exact List.mem_map.mpr ⟨flags, hflags, by simp [chosen, hv]⟩
    · intro id present
      rcases List.mem_cons.mp present with first | later
      · subst id
        simp [chosen, setSign]
      · by_cases hkey : id = key
        · subst id
          simp [chosen, setSign]
        · simpa [chosen, setSign, hkey] using hrest id later

/-- All sign patterns agreeing proves semantic equivalence for EVERY
parameter assignment; semantic equivalence proves all branch comparisons. -/
theorem compareExhaustive_correct (left right : Level) :
    compareExhaustive left right = true ↔ Equivalent left right := by
  constructor
  · intro accepted assignment
    obtain ⟨flags, hmem, hagree⟩ :=
      signPatterns_cover (parameterIds left ++ parameterIds right) (signsOf assignment)
    have hall : ∀ flags ∈ signPatterns (parameterIds left ++ parameterIds right),
        compareSigned flags left right = true := by
      simpa only [compareExhaustive, List.all_eq_true] using accepted
    have hbranch := (compareSigned_correct flags left right).mp
      (hall flags hmem) (residualOf assignment)
    have reconstruct : ∀ id ∈ parameterIds left ++ parameterIds right,
        signedAssignment flags (residualOf assignment) id = assignment id := by
      intro id present
      change (if flags id then residualOf assignment id + 1 else 0) = assignment id
      rw [hagree id present]
      exact signed_reconstruct assignment id
    have hl := eval_ext_parameterIds left
      (signedAssignment flags (residualOf assignment)) assignment (by
        intro id present
        exact reconstruct id (by simp [present]))
    have hr := eval_ext_parameterIds right
      (signedAssignment flags (residualOf assignment)) assignment (by
        intro id present
        exact reconstruct id (by simp [present]))
    exact hl.symm.trans (hbranch.trans hr)
  · intro equivalent
    simp only [compareExhaustive, List.all_eq_true]
    intro flags present
    exact (compareSigned_correct flags left right).mpr
      (fun residual => equivalent (signedAssignment flags residual))

/-- A complete negative result is a semantic counterexample, not an
inconclusive comparison or a resource failure. -/
theorem compareExhaustive_different (left right : Level)
    (different : compareExhaustive left right = false) : ¬ Equivalent left right := by
  intro same
  have accepted := (compareExhaustive_correct left right).mpr same
  rw [different] at accepted
  cases accepted

end PskernelC1Independent.Level
