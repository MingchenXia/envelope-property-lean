import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCapturedBody
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalCapturedPullbackBody

/-! # Same-original constructor readback of the rational differential statement

This is only a definitional proposition adapter. Its right-hand proposition
is captured by replacing the two original fully applied trace constructors
with their exact stored bodies, preserving all of the original expression's
other data. No native core result or desired compatibility is assumed.

Frozen providers:
* Rational.lean: f439e16bd0c6054f84db38e918c8da04418742ae8457c9e8ee6a9256dca7d18c.
* RationalDifferential.lean: 3f552e8d683e951a3c56e81c4b7fc86be7f002d7fc94d3d66d49f975f52c5d41.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private def capturedRationalStatement (stx : Lean.Syntax) :
    Lean.Elab.Term.TermElabM (Lean.Expr × Lean.Expr) := do
  let original ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  if original.hasMVar then
    throwError "the original statement still contains an unresolved metavariable"
  unless ← Lean.Meta.isProp original do
    throwError "expected the original rational differential proposition"
  let mut body := original
  for name in [``genericRationalCanonicalTrace, ``genericRationalPullbackCanonicalTrace] do
    let info ← Lean.getConstInfo name
    let some value := info.value? |
      throwError "the original trace constructor has no compiled defining body"
    let arity := info.type.getForallArity
    let replaced := body.replace fun e =>
      match e.getAppFn.consumeMData with
      | .const found levels =>
        if found == name && e.getAppNumArgs == arity &&
            info.levelParams.length == levels.length then
          some ((value.instantiateLevelParams info.levelParams levels).beta e.getAppArgs)
        else none
      | _ => none
    if replaced == body then
      throwError "the statement has no fully applied original constructor {name}"
    body := replaced
  return (original, body)

elab "capturedRationalStatementType%(" original:term ")" : term => do
  let (statement, body) ← capturedRationalStatement original
  Lean.Meta.mkEq statement body

elab "capturedRationalStatementProof%(" original:term ")" : term => do
  let (statement, _) ← capturedRationalStatement original
  Lean.Meta.mkEqRefl statement

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)

/-- Definitional readback of the actual statement with both exact stored
trace bodies. This proves no differential compatibility on its own. -/
theorem rational_differential_statement_captured_body :
    capturedRationalStatementType%(
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫
        genericRationalCanonicalTrace (X := X) (k := k)
          F n L m σ hL hD f hG hRows hm hfield =
        genericRationalPullbackCanonicalTrace (X := X) (k := k)
          F n L m σ hL hD f hG hRows hm hfield) :=
  capturedRationalStatementProof%(
    (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫
      genericRationalCanonicalTrace (X := X) (k := k)
        F n L m σ hL hD f hG hRows hm hfield =
      genericRationalPullbackCanonicalTrace (X := X) (k := k)
        F n L m σ hL hD f hG hRows hm hfield)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
