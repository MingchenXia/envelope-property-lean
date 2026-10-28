import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational

/-! # Native whole-generic trace with the original pulled line coefficients

This independent baseline uses native restriction to the actual whole
original generic fiber, its actual cartesian source comparison and the
entire field algebra trace with the original generic canonical line.
It involves no inverse canonical differential and asserts no regularity.
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

-- Exact source-bound name lookup only: this changes the elaborator scope,
-- never the environment or any constant. The frozen source is f439e16b.
run_cmd
  for (short, original) in [
      (`frozenOriginalModuleSquareMap,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap),
      (`frozenGenericSourceComparison,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.genericSourceComparison),
      (`frozenWholeFieldLineTrace,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.wholeFieldLineTrace)] do
    let name := Lean.mkPrivateNameCore
      `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational original
    unless (← Lean.getEnv).contains name do
      throwError "missing frozen original rational-trace helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

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
local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "pη" => pullback.fst π γ
local notation "qη" => pullback.snd π γ
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n

include hL hD f hG hRows hm hfield


/-- Native whole-generic restriction and WHOLE generic algebra trace with
the original base line coefficients. This support definition involves no
canonical differential or chosen inverse. -/
def genericRationalPullbackCanonicalTrace :
    (pushforward π).obj ((Scheme.Modules.pullback π).obj ωX) ⟶
      (pushforward γ).obj ((Scheme.Modules.pullback γ).obj ωX) := by
  let : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
  let T := frozenWholeFieldLineTrace X.functionField (Field.toIsField X.functionField) qη
    ((Scheme.Modules.pullback γ).obj ωX) ((canonicalLineSheaf_isInvertible f n).pullback γ)
  exact frozenOriginalModuleSquareMap π qη pη γ pullback.condition
      ((Scheme.Modules.pullback π).obj ωX) ≫
    (pushforward γ).map ((pushforward qη).map (frozenGenericSourceComparison π ωX).hom ≫ T)


end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
