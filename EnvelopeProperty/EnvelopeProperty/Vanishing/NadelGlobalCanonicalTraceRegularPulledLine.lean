import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGlobal
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRationalDifferential

/-! # The same regular structure trace with pulled canonical coefficients

This actual global morphism has source the pulled BASE canonical line.
It retains the original line PF and the original f439 unit constraints.
Its rational restriction, and any trace from the cover's canonical line,
are separate assertions.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit
  unless (← Lean.getEnv).contains name do
    throwError "missing frozen original structure-module unit constraint {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `frozenActualLeftUnit name :: scope.openDecls }

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
local notation "ωX" => canonicalLineSheaf f n

include hL hD f hG hRows hm hfield

/-- The same original global regular O-trace tensored with the original
base canonical line, through the original native projection formula. -/
def regularPulledCanonicalTrace : (pushforward π).obj ((pullback π).obj ωX) ⟶ ωX :=
  (pushforward π).map (frozenActualLeftUnit ((pullback π).obj ωX)).inv ≫
    (SchemeLineProjectionFormula.lineProjectionFormulaObj π ωX
      (canonicalLineSheaf_isInvertible f n) (unitObj Y₀)).inv ≫
    (tensorRight ωX).map
      (NadelGlobalStructureTrace.originalStructureTrace F n L m σ hL hD f hG hRows hm hfield) ≫
    (frozenActualLeftUnit ωX).hom

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
