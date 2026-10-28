import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalDifferential
import Lean.Elab.Term

/-! # Exact-body readback of the same original pulled rational trace

This is a definitional adapter, with no independent trace-compatibility credit.
Both the body and its type use the original compiled application's levels and
arguments. In particular no finite-map instance, monoidal structure, generic
canonical map or whole field trace is reconstructed by the adapter.

The frozen baseline provider is NadelGlobalCanonicalTraceRationalDifferential.lean,
SHA256 3f552e8d683e951a3c56e81c4b7fc86be7f002d7fc94d3d66d49f975f52c5d41.
Its private helpers are the same original f439e16b rational-trace constructors.
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

private def capturedOriginalPulledRationalBody (stx : Lean.Syntax) :
    Lean.Elab.Term.TermElabM (Lean.Expr × Lean.Expr) := do
  let original ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let original := original.consumeMData
  let .const name levels := original.getAppFn.consumeMData |
    throwError "expected a fully applied original rational-trace constant"
  unless name == ``genericRationalPullbackCanonicalTrace do
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

elab "capturedOriginalPulledRationalBodyType%(" original:term ")" : term => do
  let (app, body) ← capturedOriginalPulledRationalBody original
  Lean.Meta.mkEq app body

elab "capturedOriginalPulledRationalBodyProof%(" original:term ")" : term => do
  let (app, _) ← capturedOriginalPulledRationalBody original
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
theorem genericRationalPullbackCanonicalTrace_captured_body :
    capturedOriginalPulledRationalBodyType%(
      genericRationalPullbackCanonicalTrace (X := X) (k := k)
        F n L m σ hL hD f hG hRows hm hfield) :=
  capturedOriginalPulledRationalBodyProof%(
    genericRationalPullbackCanonicalTrace (X := X) (k := k)
      F n L m σ hL hD f hG hRows hm hfield)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
