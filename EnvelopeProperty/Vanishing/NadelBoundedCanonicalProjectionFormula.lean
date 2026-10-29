import EnvelopeProperty.Vanishing.NadelBoundedCanonicalPushforward
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula

/-! # Actual original projection comparison for the whole rounded line

The original line projection formula and canonical associator/braiding give
the actual target of the twisted bounded unit. No trace, retraction or
incoming target comparison is used.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalProjectionFormula
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelBoundedCanonicalPushforward
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private def tensorIdealLineIso {Y : Scheme.{u}} (B I P : Y.Modules) :
    Scheme.Modules.tensorObj B I ⊗ P ≅
      Scheme.Modules.tensorObj B (Scheme.Modules.tensorObj P I) :=
  ((ModularCurves.monoidalTensorObjIso B I).symm ⊗ᵢ Iso.refl P) ≪≫
    (α_ B I P) ≪≫ (Iso.refl B ⊗ᵢ (β_ I P)) ≪≫
    (Iso.refl B ⊗ᵢ ModularCurves.monoidalTensorObjIso P I) ≪≫
    ModularCurves.monoidalTensorObjIso B (Scheme.Modules.tensorObj P I)

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i))
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n

/-- The original projection formula has precisely the SAME whole rounded
canonical target, with the comparison constructed internally. -/
def wholeRoundedProjectionFormulaIso (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ) :
    (pushforward π).obj
        (Scheme.Modules.tensorObj ωY (wholeRoundedIdeal F n L m σ hL a).toModules) ⊗ M ≅
      (pushforward π).obj (Scheme.Modules.tensorObj ωY (wholeRoundedLine F n L m σ hL M a)) :=
  SchemeLineProjectionFormula.lineProjectionFormulaObj π M hM
      (Scheme.Modules.tensorObj ωY (wholeRoundedIdeal F n L m σ hL a).toModules) ≪≫
    (pushforward π).mapIso
      (tensorIdealLineIso ωY (wholeRoundedIdeal F n L m σ hL a).toModules
        ((pullback π).obj M))

variable (hD : ∀ i, (F.component i).IsInvertible)
    [PerfectField k] [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

include hD hG hRows hm hfield
/-- Tensor the actual original bounded unit by the original base line and
send it through the SAME internally produced whole projection comparison. -/
def wholeRoundedCanonicalTwistedPullback (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i) :
    ωX ⊗ M ⟶
      (pushforward π).obj (Scheme.Modules.tensorObj ωY (wholeRoundedLine F n L m σ hL M a)) :=
  (tensorRight M).map
      (wholeRoundedCanonicalPullback F n L m σ hL hD f hG hRows hm hfield a ha) ≫
    (wholeRoundedProjectionFormulaIso F n L m σ hL f M hM a).hom

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalProjectionFormula
