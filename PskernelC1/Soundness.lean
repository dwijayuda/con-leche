module

public import PskernelC1.Kernel
public import ConLeche.MainTheorem
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Cached.MainC
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Frontend.Prepare

public section

/-!
# Models for the owned executable entry points

These theorems are about `PskernelC1.checkDeclarations` and
`PskernelC1.checkChunks`, the functions called by the certified runtime
boundary. They reuse ConLeche's model theorem by definitional reduction;
there is no new semantic assumption about the implementation.

All model and consistency claims remain relative to `SetTheory V`.
The no-constant and parsed-record corollaries concern the pinned `False`
and `Empty` constants. The byte-template corollary retains the exact
scope of `ConLeche.jsonWithTheoremFalse`; it is not claimed to recognize
every spelling of a theorem of type `False`.
-/

namespace PskernelC1

open ConLeche

universe w

/-- Every environment returned by the owned declaration checker has a model. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : Array Declaration) (env : Env)
    (accepted : checkDeclarations ds = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  exact ConLeche.model_exists V natOpPinSets ds env accepted

/-- The model guarantee applies to the complete executable chunks pipeline. -/
theorem chunks_model_exists (V : Type w) [SetTheory V]
    (chunks : List ByteArray) (env : Env)
    (accepted : checkChunks chunks = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  unfold checkChunks at accepted
  obtain ⟨pre, _, accepted⟩ := exceptBind_ok accepted
  obtain ⟨parsed, _, accepted⟩ := exceptBind_ok accepted
  exact model_exists V (Frontend.preparePrelude pre parsed.decls) env accepted

/-- A declaration receipt supplies the acceptance hypothesis itself. -/
theorem Accepted.model_exists (V : Type w) [SetTheory V]
    {ds : Array Declaration} (accepted : Accepted ds) :
    Nonempty (ConLeche.Model V accepted.val) := by
  exact PskernelC1.model_exists V ds accepted.val accepted.property

/-- A chunks receipt supplies the whole pipeline's acceptance hypothesis. -/
theorem AcceptedChunks.model_exists (V : Type w) [SetTheory V]
    {chunks : List ByteArray} (accepted : AcceptedChunks chunks) :
    Nonempty (ConLeche.Model V accepted.val) := by
  exact chunks_model_exists V chunks accepted.val accepted.property

/-- Streaming acceptance inherits the model without retaining its chunk witness. -/
theorem AcceptedStream.model_exists (V : Type w) [SetTheory V]
    (accepted : AcceptedStream) :
    Nonempty (ConLeche.Model V accepted.val) := by
  obtain ⟨chunks, hcheck⟩ := accepted.property
  exact chunks_model_exists V chunks accepted.val hcheck

/-- No constant of the pinned `False` type is stored in an accepted environment. -/
theorem no_False_constant (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env : Env}
    (accepted : checkDeclarations ds = .ok env) :
    ∀ c ∈ env.consts, c.toConstantVal.type = .const falseName [] → False := by
  exact Cached.no_proof_of_False_cached V rfl accepted

/-- The corresponding statement for the pinned empty data type. -/
theorem no_Empty_constant (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env : Env}
    (accepted : checkDeclarations ds = .ok env) :
    ∀ c ∈ env.consts, c.toConstantVal.type = .const emptyName [] → False := by
  exact Cached.no_proof_of_Empty_cached V rfl accepted

/-- The no-`False` guarantee requires only the declaration receipt. -/
theorem Accepted.no_False_constant (V : Type w) [SetTheory V]
    {ds : Array Declaration} (accepted : Accepted ds) :
    ∀ c ∈ accepted.val.consts, c.toConstantVal.type = .const falseName [] → False := by
  exact PskernelC1.no_False_constant V accepted.property

/-- The no-`False` guarantee applies to a receipt for the whole chunks pipeline. -/
theorem AcceptedChunks.no_False_constant (V : Type w) [SetTheory V]
    {chunks : List ByteArray} (accepted : AcceptedChunks chunks) :
    ∀ c ∈ accepted.val.consts, c.toConstantVal.type = .const falseName [] → False := by
  have hcheck := accepted.property
  unfold checkChunks at hcheck
  obtain ⟨pre, _, hcheck⟩ := exceptBind_ok hcheck
  obtain ⟨parsed, _, hcheck⟩ := exceptBind_ok hcheck
  exact PskernelC1.no_False_constant V
    (ds := Frontend.preparePrelude pre parsed.decls) hcheck

/-- A successful streaming receipt cannot store a constant of type `False`. -/
theorem AcceptedStream.no_False_constant (V : Type w) [SetTheory V]
    (accepted : AcceptedStream) :
    ∀ c ∈ accepted.val.consts, c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨chunks, hcheck⟩ := accepted.property
  exact AcceptedChunks.no_False_constant V (chunks := chunks) ⟨accepted.val, hcheck⟩

/-- A declaration stream containing a theorem of type `False` cannot succeed. -/
theorem no_False_theorem_accepted (V : Type w) [SetTheory V]
    (ds : Array Declaration) (cv : ConstantVal) (value : Expr)
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const falseName []) :
    ∀ env, checkDeclarations ds ≠ .ok env := by
  exact ConLeche.no_False_theorem_accepted V ds cv value hmem hty

/-- The same exclusion starts at the parser's actual output, before prelude
preparation. It is independent of the theorem's textual spelling. -/
theorem no_False_parsed_theorem (V : Type w) [SetTheory V]
    (chunks : List ByteArray) (parsed : Frontend.ParseResultD)
    (hparse : Frontend.parseChunks chunks = .ok parsed)
    (cv : ConstantVal) (value : Expr)
    (hmem : Declaration.thmDecl cv value ∈ parsed.decls)
    (hty : cv.type = .const falseName []) :
    ∀ env, checkChunks chunks ≠ .ok env := by
  intro env accepted
  unfold checkChunks at accepted
  obtain ⟨pre, _, accepted⟩ := exceptBind_ok accepted
  have hcheck :
      checkDeclarations (Frontend.preparePrelude pre parsed.decls) = .ok env := by
    simpa only [hparse, Bind.bind, Except.bind] using accepted
  exact no_False_theorem_accepted V _ cv value
    (Frontend.mem_preparePrelude hmem) hty env hcheck

/-- The upstream JSON-template corollary, stated over our concrete function.
An error can be rejection, decline, or parse/internal failure; this theorem
does not promise a particular error category. -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (chunks : List ByteArray) (h : jsonWithTheoremFalse chunks) :
    ∃ e, checkChunks chunks = .error e := by
  exact ConLeche.no_False_declaration V natOpPinSets chunks h

end PskernelC1
