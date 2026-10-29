import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceFixedRestriction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartPullbackRestriction
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePointOriginalCandidate
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartStructureSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLine

/-! # The same actual global pulled-line trace on the entire original chart

The original global structure trace supplies the whole coefficient square
internally. Its exact original line projection formula gives the same entire
pulled-base-line square, before converting its restriction to the chart's
canonical exterior line.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  for (short, original) in [
      (`fixedChartRLeftUnit, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`fixedChartRModuleSquare, `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing original whole-chart line constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private def elaboratedActualFixedR (stx : Lean.Syntax) : Lean.Elab.Term.TermElabM Lean.Expr := do
  let h ← Lean.Elab.Term.elabTerm stx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let h ← Lean.instantiateMVars h
  let P ← Lean.instantiateMVars (← Lean.Meta.inferType h)
  if h.hasMVar || P.hasMVar then
    throwError "the original fixed-chart trace has unresolved metavariables"
  unless ← Lean.Meta.isProp P do
    throwError "the original fixed-chart trace result is not a proposition"
  let mut node := h.consumeMData
  for _ in [:32] do
    match node with
    | .letE _ _ v body _ => node := (body.instantiate1 v).headBeta.consumeMData
    | _ => pure ()
  unless node.isAppOfArity ``originalLineTrace_nativeFixedLineRestriction 19 do
    throwError "expected only the proved original fixed-line restriction application"
  return h

elab "actualFixedChartTraceType%(" h:term ")" : term => do
  Lean.Meta.inferType (← elaboratedActualFixedR h)

elab "actualFixedChartTraceProof%(" h:term ")" : term =>
  elaboratedActualFixedR h

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
local notation "Y₀" => normalizedScheme (OriginalData.data F n L m σ)
local notation "D" => NadelWholeCoverDegree.degree (NadelAdaptedChartMatching.Joined.degree F n m)
local notation "T" => originalStructureTrace F n L m σ hL hD f hG hRows hm hfield
local notation "ωX" => canonicalLineSheaf f n

include hL hD f hG hRows hm hfield

/-- The SAME original global pulled-line trace satisfies the whole actual
chart equation under the fixed native canonical differentials. Its ordinary
Eq type is inferred from the proved original construction before nominal
wrapper conversion; every map and geometric input remains literal original data. -/
theorem regularPulledCanonicalTrace_wholeChart_fixed_restriction_captured
    (C : WholeFreeChart π D) [Nonempty C.base.1] :
    actualFixedChartTraceType%((let _ := C.algebra;
      let _ : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis;
      let _ : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis;
      let _ : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion;
      let _ : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
        isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n;
      let N := canonicalLineSheaf (C.base.2.fromSpec ≫ f) n;
      let a := asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n);
      let hN : IsInvertible N :=
        ((canonicalLineSheaf_isInvertible f n).pullback C.base.2.fromSpec).of_iso a.symm;
      originalLineTrace_nativeFixedLineRestriction
        π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback
        ωX (canonicalLineSheaf_isInvertible f n) N hN a T
        (affineStructureTrace Γ(X, C.base.1) C.coeff)
        (originalStructureTrace_wholeChart_square F n L m σ hL hD f hG hRows hm hfield C))) :=
  actualFixedChartTraceProof%((let _ := C.algebra;
      let _ : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis;
      let _ : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis;
      let _ : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion;
      let _ : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
        isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n;
      let N := canonicalLineSheaf (C.base.2.fromSpec ≫ f) n;
      let a := asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n);
      let hN : IsInvertible N :=
        ((canonicalLineSheaf_isInvertible f n).pullback C.base.2.fromSpec).of_iso a.symm;
      originalLineTrace_nativeFixedLineRestriction
        π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback
        ωX (canonicalLineSheaf_isInvertible f n) N hN a T
        (affineStructureTrace Γ(X, C.base.1) C.coeff)
        (originalStructureTrace_wholeChart_square F n L m σ hL hD f hG hRows hm hfield C)))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
