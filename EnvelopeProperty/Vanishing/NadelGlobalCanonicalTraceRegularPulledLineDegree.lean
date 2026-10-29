import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRegularPulledLine
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGlobalNormalization
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaAdjunctionUnit

/-! # The actual regular pulled-line trace retains the whole original degree

This degree identity has source pi_*pi^*omega_X. It uses the same original
global structure trace and same original line projection formula, and
does not yet assert a regular trace on the original omega_Y.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  for (mod, short, original) in [
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational,
        `frozenActualLeftUnit,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartNormalization,
        `frozenConjugateNsmulId,
        `EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.conjugate_nsmul_id)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing frozen original regular pulled-line degree helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem native_unit_comp_line_trace
    {X Y : Scheme.{u}} (π : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M)
    (τ : (pushforward π).obj (unitObj Y) ⟶ unitObj X) :
    (pullbackPushforwardAdjunction π).unit.app M ≫
        ((pushforward π).map (frozenActualLeftUnit ((pullback π).obj M)).inv ≫
          (SchemeLineProjectionFormula.lineProjectionFormulaObj π M hM (unitObj Y)).inv ≫
          (tensorRight M).map τ ≫ (frozenActualLeftUnit M).hom) =
      (frozenActualLeftUnit M).inv ≫
        (tensorRight M).map
          (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫ τ) ≫
        (frozenActualLeftUnit M).hom := by
  have hη : (frozenActualLeftUnit M).inv ≫
      (tensorRight M).map (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj π M hM (unitObj Y)).hom ≫
      (pushforward π).map (frozenActualLeftUnit ((pullback π).obj M)).hom =
        (pullbackPushforwardAdjunction π).unit.app M :=
    SchemeLineProjectionFormulaUnit.lineProjectionFormulaObj_adjunction_unit π M hM
  rw [← hη]
  simp only [Category.assoc]
  rw [← (pushforward π).map_comp_assoc, Iso.hom_inv_id,
    (pushforward π).map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  simp only [(tensorRight M).map_comp, Category.assoc]

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
local notation "ωX" => canonicalLineSheaf f n
local notation "D" => NadelWholeCoverDegree.degree (NadelAdaptedChartMatching.Joined.degree F n m)

include hL hD f hG hRows hm hfield

/-- The actual native canonical-line unit followed by the SAME regular
pulled-line trace is the WHOLE original cover degree on omega_X.
The original global O-trace degree and native PF normalization are used
internally. This is not a trace on omega_Y. -/
theorem unit_comp_regularPulledCanonicalTrace :
    (pullbackPushforwardAdjunction π).unit.app ωX ≫
      regularPulledCanonicalTrace F n L m σ hL hD f hG hRows hm hfield =
      D • 𝟙 ωX := by
  let : (tensorRight ωX).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence ωX
      (canonicalLineSheaf_isInvertible f n)
  let : (tensorRight ωX).Additive :=
    Functor.additive_of_preserves_binary_products (tensorRight ωX)
  dsimp (config := { proj := false, zetaDelta := false }) only [regularPulledCanonicalTrace]
  rw [native_unit_comp_line_trace,
    NadelGlobalStructureTrace.unit_comp_originalStructureTrace F n L m σ hL hD f hG hRows hm hfield]
  rw [(tensorRight ωX).map_nsmul, (tensorRight ωX).map_id]
  exact frozenConjugateNsmulId (frozenActualLeftUnit ωX).symm _

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
