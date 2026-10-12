module

public import ConLeche.Verify.Level
public import PskernelC1Independent.UniverseProofs
public import PskernelC1Independent.UniversePolynomialProofs
public import PskernelC1Independent.NameCodecProofs
public import PskernelC1Independent.UniverseAllSignsProofs

public section

/-!
# Independent universe operations meet the inherited semantic interface

This is a PROOF-ONLY adapter, outside the independent runtime package.
It never calls either checker's universe comparison implementation.

The interpretation bridge itself needs no injectivity assumption. The
source-input equality corollary additionally requires a faithful codec:
decoding the encoded source names must return those names. Establishing
that property for the future input interner is a separate obligation.
-/

namespace PskernelC1Bridge

open PskernelC1Independent

/-- Decode the independent representation under an explicit name map. -/
@[expose] def toReference (names : Nat → ConLeche.Name) : Level → ConLeche.Level
  | .zero => .zero
  | .succ level => .succ (toReference names level)
  | .max left right => .max (toReference names left) (toReference names right)
  | .imax left right => .imax (toReference names left) (toReference names right)
  | .param id => .param (names id)

/-- Encode an exported reference level under an explicit parameter map. -/
@[expose] def fromReference (ids : ConLeche.Name → Nat) : ConLeche.Level → Level
  | .zero => .zero
  | .succ level => .succ (fromReference ids level)
  | .max left right => .max (fromReference ids left) (fromReference ids right)
  | .imax left right => .imax (fromReference ids left) (fromReference ids right)
  | .param name => .param (ids name)

/-- Every decoded universe has precisely the inherited evaluation. -/
theorem toReference_eval (names : Nat → ConLeche.Name)
    (assignment : ConLeche.Name → Nat) (level : Level) :
    ConLeche.Level.eval assignment (toReference names level) =
      Level.eval (fun id => assignment (names id)) level := by
  induction level <;> simp [toReference, ConLeche.Level.eval, Level.eval, *]

/-- Encoding commutes with interpretation at all parameter assignments. -/
theorem fromReference_eval (ids : ConLeche.Name → Nat)
    (assignment : Nat → Nat) (level : ConLeche.Level) :
    Level.eval assignment (fromReference ids level) =
      ConLeche.Level.eval (fun name => assignment (ids name)) level := by
  induction level <;> simp [fromReference, ConLeche.Level.eval, Level.eval, *]

/-- A faithful name codec preserves the complete source universe syntax. -/
theorem source_roundtrip (ids : ConLeche.Name → Nat) (names : Nat → ConLeche.Name)
    (faithful : ∀ name, names (ids name) = name) (level : ConLeche.Level) :
    toReference names (fromReference ids level) = level := by
  induction level <;> simp [toReference, fromReference, *]

/-- The independent normalizer preserves the reference semantic meaning. -/
theorem normalize_reference_sound (names : Nat → ConLeche.Name)
    (assignment : ConLeche.Name → Nat) (level : Level) :
    ConLeche.Level.eval assignment (toReference names (Level.normalize level)) =
      ConLeche.Level.eval assignment (toReference names level) := by
  rw [toReference_eval, toReference_eval]
  exact Level.eval_normalize _ level

/-- A positive independent fast path preserves the reference interpretation. -/
theorem compareFast_reference_sound (names : Nat → ConLeche.Name)
    (left right : Level) (accepted : Level.compareFast left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment (toReference names left) =
      ConLeche.Level.eval assignment (toReference names right) := by
  intro assignment
  rw [toReference_eval, toReference_eval]
  exact Level.compareFast_sound left right accepted _

/-- Source equality requires the codec proof; aliasing source names is not
silently licensed by correctness of the internal comparison operation. -/
theorem compareFast_source_sound (ids : ConLeche.Name → Nat)
    (names : Nat → ConLeche.Name) (faithful : ∀ name, names (ids name) = name)
    (left right : ConLeche.Level)
    (accepted : Level.compareFast (fromReference ids left) (fromReference ids right) = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment left = ConLeche.Level.eval assignment right := by
  intro assignment
  have h := compareFast_reference_sound names _ _ accepted assignment
  simpa only [source_roundtrip ids names faithful] using h

/-- Even a per-input roundtrip proof is sufficient: a parser need not claim
that its finite parameter table represents every name in the language. -/
theorem compareFast_inputs_sound (names : Nat → ConLeche.Name)
    (left right : Level) (sourceLeft sourceRight : ConLeche.Level)
    (leftFaithful : toReference names left = sourceLeft)
    (rightFaithful : toReference names right = sourceRight)
    (accepted : Level.compareFast left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment sourceLeft =
      ConLeche.Level.eval assignment sourceRight := by
  intro assignment
  rw [← leftFaithful, ← rightFaithful]
  exact compareFast_reference_sound names left right accepted assignment

/-!
## Finite input-name codec and source-level polynomial comparison

Unlike a globally supplied map from every source name to a Nat, this
encoder requires no impossible promise that a finite input table can
encode all names. It checks every parameter in the actual input.

Source-to-internal decoding is proved on every successful encoding,
including nested imax syntax. Negative and positive polynomial verdicts
are transported through the actual input encoder, not a guessed codec.
-/

/-- Collect every parameter occurrence, retaining duplicates on purpose.
First-occurrence indexing gives duplicates the same stable internal ID. -/
@[expose] def sourceParameters : ConLeche.Level → List ConLeche.Name
  | .zero => []
  | .succ level => sourceParameters level
  | .max left right => sourceParameters left ++ sourceParameters right
  | .imax left right => sourceParameters left ++ sourceParameters right
  | .param name => [name]

/-- Decode a finite name ID. The fallback is never used by a successful
encoding; the accompanying theorem proves this for every source node. -/
@[expose] def decodedName (table : List ConLeche.Name) (id : Nat) : ConLeche.Name :=
  (NameCodec.get? table id).getD .anonymous

/-- Fail rather than fabricate an ID when a source parameter is missing. -/
@[expose] def encodeReferenceFinite (table : List ConLeche.Name) : ConLeche.Level → Option Level
  | .zero => some .zero
  | .succ level => (encodeReferenceFinite table level).map .succ
  | .max left right => do
      let left ← encodeReferenceFinite table left
      let right ← encodeReferenceFinite table right
      pure (.max left right)
  | .imax left right => do
      let left ← encodeReferenceFinite table left
      let right ← encodeReferenceFinite table right
      pure (.imax left right)
  | .param name => (NameCodec.index? table name).map .param

/-- Interpret any independent parameter assignment back on source names.
Missing names map to zero only in this proof auxiliary; the actual
encoder explicitly declines when an input uses a missing name. -/
@[expose] def sourceAssignment (table : List ConLeche.Name) (assignment : Nat → Nat)
    (name : ConLeche.Name) : Nat :=
  match NameCodec.index? table name with
  | some id => assignment id
  | none => 0

/-- Every successful finite encoding preserves the exact original syntax. -/
theorem encodeReferenceFinite_roundtrip (table : List ConLeche.Name)
    (source : ConLeche.Level) (internal : Level)
    (encoded : encodeReferenceFinite table source = some internal) :
    toReference (decodedName table) internal = source := by
  induction source generalizing internal with
  | zero =>
    simp [encodeReferenceFinite] at encoded
    subst internal
    rfl
  | succ level ih =>
    cases h : encodeReferenceFinite table level with
    | none => simp [encodeReferenceFinite, h] at encoded
    | some child =>
      simp [encodeReferenceFinite, h] at encoded
      subst internal
      simpa [toReference] using congrArg ConLeche.Level.succ (ih child h)
  | max left right ihLeft ihRight =>
    cases hl : encodeReferenceFinite table left with
    | none => simp [encodeReferenceFinite, hl] at encoded
    | some il =>
      cases hr : encodeReferenceFinite table right with
      | none => simp [encodeReferenceFinite, hl, hr] at encoded
      | some ir =>
        simp [encodeReferenceFinite, hl, hr] at encoded
        subst internal
        simp [toReference, ihLeft il hl, ihRight ir hr]
  | imax left right ihLeft ihRight =>
    cases hl : encodeReferenceFinite table left with
    | none => simp [encodeReferenceFinite, hl] at encoded
    | some il =>
      cases hr : encodeReferenceFinite table right with
      | none => simp [encodeReferenceFinite, hl, hr] at encoded
      | some ir =>
        simp [encodeReferenceFinite, hl, hr] at encoded
        subst internal
        simp [toReference, ihLeft il hl, ihRight ir hr]
  | param name =>
    cases hname : NameCodec.index? table name with
    | none => simp [encodeReferenceFinite, hname] at encoded
    | some id =>
      simp [encodeReferenceFinite, hname] at encoded
      subst internal
      have hget := NameCodec.index?_sound table name id hname
      simp [toReference, decodedName, hget]

/-- Every successfully encoded universe has exactly the source meaning
under the induced assignment, including arbitrary imax expressions. -/
theorem encodeReferenceFinite_eval (table : List ConLeche.Name)
    (source : ConLeche.Level) (internal : Level)
    (encoded : encodeReferenceFinite table source = some internal) :
    ∀ assignment, Level.eval assignment internal =
      ConLeche.Level.eval (sourceAssignment table assignment) source := by
  induction source generalizing internal with
  | zero =>
    simp [encodeReferenceFinite] at encoded
    subst internal
    intro assignment
    rfl
  | succ level ih =>
    cases h : encodeReferenceFinite table level with
    | none => simp [encodeReferenceFinite, h] at encoded
    | some child =>
      simp [encodeReferenceFinite, h] at encoded
      subst internal
      intro assignment
      simp [Level.eval, ConLeche.Level.eval, ih child h assignment]
  | max left right ihLeft ihRight =>
    cases hl : encodeReferenceFinite table left with
    | none => simp [encodeReferenceFinite, hl] at encoded
    | some il =>
      cases hr : encodeReferenceFinite table right with
      | none => simp [encodeReferenceFinite, hl, hr] at encoded
      | some ir =>
        simp [encodeReferenceFinite, hl, hr] at encoded
        subst internal
        intro assignment
        simp [Level.eval, ConLeche.Level.eval, ihLeft il hl assignment,
          ihRight ir hr assignment]
  | imax left right ihLeft ihRight =>
    cases hl : encodeReferenceFinite table left with
    | none => simp [encodeReferenceFinite, hl] at encoded
    | some il =>
      cases hr : encodeReferenceFinite table right with
      | none => simp [encodeReferenceFinite, hl, hr] at encoded
      | some ir =>
        simp [encodeReferenceFinite, hl, hr] at encoded
        subst internal
        intro assignment
        simp [Level.eval, ConLeche.Level.eval, ihLeft il hl assignment,
          ihRight ir hr assignment]
  | param name =>
    cases hname : NameCodec.index? table name with
    | none => simp [encodeReferenceFinite, hname] at encoded
    | some id =>
      simp [encodeReferenceFinite, hname] at encoded
      subst internal
      intro assignment
      simp [Level.eval, ConLeche.Level.eval, sourceAssignment, hname]

/-- A table containing every source parameter makes encoding total. -/
theorem encodeReferenceFinite_complete (table : List ConLeche.Name)
    (source : ConLeche.Level)
    (covered : ∀ name ∈ sourceParameters source, name ∈ table) :
    ∃ internal, encodeReferenceFinite table source = some internal := by
  induction source with
  | zero => exact ⟨.zero, rfl⟩
  | succ level ih =>
    obtain ⟨child, hchild⟩ := ih (by
      intro name hname
      exact covered name (by simpa [sourceParameters] using hname))
    exact ⟨.succ child, by simp [encodeReferenceFinite, hchild]⟩
  | max left right ihLeft ihRight =>
    obtain ⟨il, hl⟩ := ihLeft (by
      intro name hname
      exact covered name (by simp [sourceParameters, hname]))
    obtain ⟨ir, hr⟩ := ihRight (by
      intro name hname
      exact covered name (by simp [sourceParameters, hname]))
    exact ⟨.max il ir, by simp [encodeReferenceFinite, hl, hr]⟩
  | imax left right ihLeft ihRight =>
    obtain ⟨il, hl⟩ := ihLeft (by
      intro name hname
      exact covered name (by simp [sourceParameters, hname]))
    obtain ⟨ir, hr⟩ := ihRight (by
      intro name hname
      exact covered name (by simp [sourceParameters, hname]))
    exact ⟨.imax il ir, by simp [encodeReferenceFinite, hl, hr]⟩
  | param name =>
    obtain ⟨id, hid⟩ := NameCodec.index?_complete table name
      (covered name (by simp [sourceParameters]))
    exact ⟨.param id, by simp [encodeReferenceFinite, hid]⟩

/-- Compare actual exported input syntax with a shared finite name table. -/
@[expose] def compareSourceWith (table : List ConLeche.Name)
    (left right : ConLeche.Level) : Level.PolynomialResult :=
  match encodeReferenceFinite table left, encodeReferenceFinite table right with
  | some il, some ir => Level.comparePolynomial il ir
  | _, _ => .unknown

/-- A conclusive positive result is semantically valid on the exact
source inputs, not merely on renamed internal approximations. -/
theorem compareSourceWith_sound (table : List ConLeche.Name)
    (left right : ConLeche.Level)
    (accepted : compareSourceWith table left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right := by
  unfold compareSourceWith at accepted
  cases hl : encodeReferenceFinite table left with
  | none => simp [hl] at accepted
  | some il =>
    cases hr : encodeReferenceFinite table right with
    | none => simp [hl, hr] at accepted
    | some ir =>
      have hp : Level.comparePolynomial il ir = .equal := by
        simpa [hl, hr] using accepted
      have hleft := encodeReferenceFinite_roundtrip table left il hl
      have hright := encodeReferenceFinite_roundtrip table right ir hr
      intro assignment
      rw [← hleft, ← hright, toReference_eval, toReference_eval]
      exact Level.comparePolynomial_sound il ir hp _

/-- A conclusive negative result is also justified: any source equality
would entail internal equality under every Nat-valued assignment. -/
theorem compareSourceWith_different (table : List ConLeche.Name)
    (left right : ConLeche.Level)
    (different : compareSourceWith table left right = .different) :
    ¬ (∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right) := by
  intro same
  unfold compareSourceWith at different
  cases hl : encodeReferenceFinite table left with
  | none => simp [hl] at different
  | some il =>
    cases hr : encodeReferenceFinite table right with
    | none => simp [hl, hr] at different
    | some ir =>
      have hp : Level.comparePolynomial il ir = .different := by
        simpa [hl, hr] using different
      apply Level.comparePolynomial_different il ir hp
      intro assignment
      rw [encodeReferenceFinite_eval table left il hl assignment,
        encodeReferenceFinite_eval table right ir hr assignment]
      exact same (sourceAssignment table assignment)

/-- Construct the finite name table from the two actual inputs, rather
than accepting an arbitrary map which might identify distinct names. -/
@[expose] def compareSource (left right : ConLeche.Level) : Level.PolynomialResult :=
  compareSourceWith (sourceParameters left ++ sourceParameters right) left right

/-- Every source parameter is included in the automatically built table. -/
theorem compareSource_encoding_total (left right : ConLeche.Level) :
    (∃ il, encodeReferenceFinite (sourceParameters left ++ sourceParameters right)
      left = some il) ∧
    (∃ ir, encodeReferenceFinite (sourceParameters left ++ sourceParameters right)
      right = some ir) := by
  constructor
  · exact encodeReferenceFinite_complete _ left (by
      intro name hname
      simp [hname])
  · exact encodeReferenceFinite_complete _ right (by
      intro name hname
      simp [hname])

theorem compareSource_sound (left right : ConLeche.Level)
    (accepted : compareSource left right = .equal) :
    ∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right :=
  compareSourceWith_sound _ left right accepted

theorem compareSource_different (left right : ConLeche.Level)
    (different : compareSource left right = .different) :
    ¬ (∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right) :=
  compareSourceWith_different _ left right different

-- These are finite source expressions, not a presumed global encoding.
example :
    compareSource (.max (.param (.str .anonymous "u")) (.param (.str .anonymous "v")))
      (.max (.param (.str .anonymous "v")) (.param (.str .anonymous "u"))) = .equal := by decide

example :
    compareSource (.param (.str .anonymous "u")) (.param (.str .anonymous "v")) =
      .different := by decide

example :
    compareSource (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v")))
      (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v"))) =
      .unknown := by decide

/-!
## An exhaustive semantic source oracle, separate from kernel conversion

The exact internal sign-enumeration comparator can also be used on the
ORIGINAL exported syntax via the finite codec. Unlike a partial
polynomial front door, this source operation always has a conclusive
Boolean result after building the complete table from both inputs.
It is a potentially exponential proof/differential reference and must
not silently replace Lean's operational definitional equality.
-/

@[expose] def compareSourceExactWith (table : List ConLeche.Name)
    (left right : ConLeche.Level) : Option Bool :=
  match encodeReferenceFinite table left, encodeReferenceFinite table right with
  | some il, some ir => some (Level.compareExhaustive il ir)
  | _, _ => none

/-- A successful positive source comparison is true at EVERY level
assignment. Missing source names are represented by none, never false. -/
theorem compareSourceExactWith_true (table : List ConLeche.Name)
    (left right : ConLeche.Level)
    (accepted : compareSourceExactWith table left right = some true) :
    ∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right := by
  unfold compareSourceExactWith at accepted
  cases hl : encodeReferenceFinite table left with
  | none => simp [hl] at accepted
  | some il =>
    cases hr : encodeReferenceFinite table right with
    | none => simp [hl, hr] at accepted
    | some ir =>
      have hp : Level.compareExhaustive il ir = true := by
        simpa [hl, hr] using accepted
      have hleft := encodeReferenceFinite_roundtrip table left il hl
      have hright := encodeReferenceFinite_roundtrip table right ir hr
      intro assignment
      rw [← hleft, ← hright, toReference_eval, toReference_eval]
      exact (Level.compareExhaustive_correct il ir).mp hp _

/-- A negative verdict from a completed source encoding also has
semantic justification, not merely an omitted or malformed input. -/
theorem compareSourceExactWith_false (table : List ConLeche.Name)
    (left right : ConLeche.Level)
    (different : compareSourceExactWith table left right = some false) :
    ¬ (∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right) := by
  intro same
  unfold compareSourceExactWith at different
  cases hl : encodeReferenceFinite table left with
  | none => simp [hl] at different
  | some il =>
    cases hr : encodeReferenceFinite table right with
    | none => simp [hl, hr] at different
    | some ir =>
      have hp : Level.compareExhaustive il ir = false := by
        simpa [hl, hr] using different
      apply Level.compareExhaustive_different il ir hp
      intro residual
      rw [encodeReferenceFinite_eval table left il hl residual,
        encodeReferenceFinite_eval table right ir hr residual]
      exact same (sourceAssignment table residual)

/-- Construct the complete finite input-name table first. -/
@[expose] def compareSourceExact (left right : ConLeche.Level) : Option Bool :=
  compareSourceExactWith (sourceParameters left ++ sourceParameters right) left right

/-- No name-table omission is possible for two concrete source inputs. -/
theorem compareSourceExact_total (left right : ConLeche.Level) :
    ∃ verdict, compareSourceExact left right = some verdict := by
  obtain ⟨⟨il, hl⟩, ⟨ir, hr⟩⟩ := compareSource_encoding_total left right
  exact ⟨Level.compareExhaustive il ir, by
    simp [compareSourceExact, compareSourceExactWith, hl, hr]⟩

/-- Full semantic iff for arbitrary source levels, including nested imax. -/
theorem compareSourceExact_correct (left right : ConLeche.Level) :
    compareSourceExact left right = some true ↔
      ∀ assignment, ConLeche.Level.eval assignment left =
        ConLeche.Level.eval assignment right := by
  constructor
  · exact compareSourceExactWith_true _ left right
  · intro same
    obtain ⟨⟨il, hl⟩, ⟨ir, hr⟩⟩ := compareSource_encoding_total left right
    have internalEq : Level.Equivalent il ir := by
      intro residual
      rw [encodeReferenceFinite_eval _ left il hl residual,
        encodeReferenceFinite_eval _ right ir hr residual]
      exact same (sourceAssignment (sourceParameters left ++ sourceParameters right) residual)
    have eq := (Level.compareExhaustive_correct il ir).mpr internalEq
    simp [compareSourceExact, compareSourceExactWith, hl, hr, eq]

/-- If the result is false, it cannot be a disguised inconclusive case. -/
theorem compareSourceExact_different (left right : ConLeche.Level)
    (different : compareSourceExact left right = some false) :
    ¬ (∀ assignment, ConLeche.Level.eval assignment left =
      ConLeche.Level.eval assignment right) := by
  exact compareSourceExactWith_false _ left right different

-- Source-level semantic regression examples, distinct from official
-- version-pinned algorithmic conversion conformance.
example :
    compareSourceExact
      (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v")))
      (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v"))) =
      some true := by decide

example :
    compareSourceExact
      (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v")))
      (.max (.param (.str .anonymous "u")) (.param (.str .anonymous "v"))) =
      some false := by decide

example :
    compareSourceExact
      (.succ (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v"))))
      (.imax (.param (.str .anonymous "u")) (.param (.str .anonymous "v"))) =
      some false := by decide

#print axioms toReference_eval
#print axioms fromReference_eval
#print axioms source_roundtrip
#print axioms normalize_reference_sound
#print axioms compareFast_reference_sound
#print axioms compareFast_source_sound
#print axioms compareFast_inputs_sound

#print axioms encodeReferenceFinite_roundtrip
#print axioms encodeReferenceFinite_eval
#print axioms encodeReferenceFinite_complete
#print axioms compareSourceWith_sound
#print axioms compareSourceWith_different
#print axioms compareSource_encoding_total
#print axioms compareSource_sound
#print axioms compareSource_different
#print axioms compareSourceExactWith_true
#print axioms compareSourceExactWith_false
#print axioms compareSourceExact_total
#print axioms compareSourceExact_correct
#print axioms compareSourceExact_different

end PskernelC1Bridge
