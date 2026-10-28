import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
import Lean.Elab.Term

/-! # Exact-body readback of the same original rational trace

This is a definitional adapter, with no independent trace-compatibility credit.
Both the body and its type use the original compiled application's levels and
arguments. In particular no finite-map instance, monoidal structure, generic
canonical map or whole field trace is reconstructed by the adapter.

The frozen original provider is NadelGlobalCanonicalTraceRational.lean,
SHA256 f439e16bd0c6054f84db38e918c8da04418742ae8457c9e8ee6a9256dca7d18c.
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

private def capturedOriginalRationalBody (stx : Lean.Syntax) :
    Lean.Elab.Term.TermElabM (Lean.Expr × Lean.Expr) := do
  let original ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let original := original.consumeMData
  let .const name levels := original.getAppFn.consumeMData |
    throwError "expected a fully applied original rational-trace constant"
  unless name == ``genericRationalCanonicalTrace do
    throwError "the readback only accepts the same original rational trace"
  let info ← Lean.getConstInfo name
  let some value := info.value? |
    throwError "the original rational trace has no compiled defining body"
  unless info.levelParams.length == levels.length do
    throwError "unexpected original universe-parameter count"
  if original.hasMVar then
    throwError "the original application still contains an unresolved metavariable"
  let body := (value.instantiateLevelParams info.levelParams levels).beta original.getAppArgs
  return (original, body)

elab "capturedOriginalRationalBodyType%(" original:term ")" : term => do
  let (app, body) ← capturedOriginalRationalBody original
  Lean.Meta.mkEq app body

elab "capturedOriginalRationalBodyProof%(" original:term ")" : term => do
  let (app, _) ← capturedOriginalRationalBody original
  Lean.Meta.mkEqRefl app

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

/-- Definitional equality with the exact stored body of the original trace.
The right side is captured from that definition, retaining all original data. -/
theorem genericRationalCanonicalTrace_captured_body :
    capturedOriginalRationalBodyType%(
      genericRationalCanonicalTrace (X := X) (k := k)
        F n L m σ hL hD f hG hRows hm hfield) :=
  capturedOriginalRationalBodyProof%(
    genericRationalCanonicalTrace (X := X) (k := k)
      F n L m σ hL hD f hG hRows hm hfield)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
