import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGlobalNormalization
import EnvelopeProperty.AlgGeom.CyclicSectionAffineBaseConstantCoordinates

/-! # The whole actual chart equation as its native structure-unit square

This consumes the proved original chart restriction of the global
O-trace and the existing native open cartesian comparison.  The
coefficient algebra, basis and every chart map are the original ones.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.AlgGeom.CyclicSectionAffineBaseConstantCoordinates
    `EnvelopeProperty.CyclicSectionAffineBaseConstantCoordinates.naturality_of_restriction
  unless (← Lean.getEnv).contains name do
    throwError "missing original native open structure-square converse {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `originalNaturalityOfRestriction name :: scope.openDecls }

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
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

include hL hD f hG hRows hm hfield

/-- The SAME global trace and SAME actual whole-chart coefficient trace
satisfy their entire native structural square, on all coefficients.
No chart agreement, trace certificate or field model is an input. -/
theorem originalStructureTrace_wholeChart_square (C : WholeFreeChart π D) [Nonempty C.base.1] :
    let _ := C.algebra
    let _ : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
    let _ : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
    T ≫ SheafOfModules.unitToPushforwardObjUnit C.base.2.fromSpec.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap π C.scalarMap C.sourceMap
          C.base.2.fromSpec C.isPullback.w.symm ≫
        (pushforward C.base.2.fromSpec).map (affineStructureTrace Γ(X, C.base.1) C.coeff) := by
  let _ := C.algebra
  let _ : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let _ : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let ν := affineStructureTrace Γ(X, C.base.1) C.coeff
  have hr := originalStructureTrace_onChart F n L m σ hL hD f hG hRows hm hfield C
  have hp := congrArg (fun a :
      (restrictFunctor C.base.2.fromSpec).obj ((pushforward π).obj (unitObj Y₀)) ⟶
        (restrictFunctor C.base.2.fromSpec).obj (unitObj X) =>
      a ≫ (restrictUnitIso C.base.2.fromSpec).hom) hr
  have hc :
      (restrictPushforwardIsoOfIsPullbackApp π C.scalarMap C.sourceMap C.base.2.fromSpec
          C.isPullback (unitObj Y₀)).hom ≫
        (pushforward C.scalarMap).map (restrictUnitIso C.sourceMap).hom ≫ ν =
      (restrictFunctor C.base.2.fromSpec).map T ≫ (restrictUnitIso C.base.2.fromSpec).hom := by
    dsimp (config := { proj := false, zetaDelta := false }) only
      [WholeFreeChart.traceOnSpec, WholeFreeChart.pushforwardIso,
        CyclicGlobalRoundedChartPushforward.cartesianUnitComparison] at hp
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hp.symm
  exact (originalNaturalityOfRestriction π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback
    T ν hc).symm

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
