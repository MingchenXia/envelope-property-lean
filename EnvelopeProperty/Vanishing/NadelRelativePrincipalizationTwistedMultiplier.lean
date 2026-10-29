import EnvelopeProperty.Vanishing.NadelRelativePrincipalizationAbsolute
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent

/-! # The exact original twisted multiplier is the whole BP pushforward

The original absolute multiplier isomorphism and original native line
projection formula produce the entire twisted comparison. Quasicoherence
is transported from the original ideal module and invertible lines on X.
No properness over k, affineness of the BP composite or new pushforward hypothesis is used.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalizationTwistedMultiplier
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry Char0
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

local notation "μ" => Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI)
local notation "ωX" => canonicalLineSheaf f n
local notation "J₀" => Scheme.IdealSheafData.comap I
  (Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI))
local notation "hJ₀" => NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI

/-- The entire original canonical/line-twisted multiplier module is the
actual native twisted absolute rounded pushforward on the SAME original BP.
All multiplier, projection and tensor isomorphisms are produced internally. -/
def originalTwistedMultiplierIso (q : ℚ) (A : X.Modules) (hA : IsInvertible A) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    ((ωX ⊗ A) ⊗ (schemeMultiplierIdealSheaf f I hI q).toModules) ≅
      (pushforward μ).obj
        (Scheme.Modules.tensorObj (RoundedCanonicalModule.absolute (μ ≫ f) n J₀ hJ₀ q)
          ((pullback μ).obj A)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : SmoothOfRelativeDimension n (μ ≫ f) :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : IsProper μ := NadelRelativePrincipalization.composite_isProper f n I hI
  let J := (schemeMultiplierIdealSheaf f I hI q).toModules
  let Q := RoundedCanonicalModule.absolute (μ ≫ f) n J₀ hJ₀ q
  let e := Classical.choose (NadelRelativePrincipalizationAbsolute.exists_absoluteMultiplierIso f n I hI q)
  let E : ((ωX ⊗ A) ⊗ J) ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj ωX J) A :=
    (α_ ωX A J) ≪≫ (Iso.refl ωX ⊗ᵢ (β_ A J)) ≪≫ (α_ ωX J A).symm ≪≫
      (ModularCurves.monoidalTensorObjIso ωX J ⊗ᵢ Iso.refl A) ≪≫
      ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj ωX J) A
  exact E ≪≫ tensorObjCongr e (Iso.refl A) ≪≫
    NadelPrincipalizationAbsoluteProjection.tensorProjectionIso μ A hA Q

/-- The SAME whole native twisted pushforward is globally quasicoherent
on original X, by its actual multiplier isomorphism and original ideal QC.
The original BP composite need not be affine or proper over the field. -/
theorem originalTwistedMultiplierPushforward_isQuasicoherent
    (q : ℚ) (A : X.Modules) (hA : IsInvertible A) :
    ((pushforward μ).obj
      (Scheme.Modules.tensorObj (RoundedCanonicalModule.absolute (μ ≫ f) n J₀ hJ₀ q)
        ((pullback μ).obj A))).IsQuasicoherent := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let J := (schemeMultiplierIdealSheaf f I hI q).toModules
  let W := ωX ⊗ A
  let : J.IsQuasicoherent := (schemeMultiplierIdealSheaf f I hI q).isQuasicoherent_toModules
  have hW : IsInvertible W :=
    ((canonicalLineSheaf_isInvertible f n).tensorObj hA).of_iso
      (ModularCurves.monoidalTensorObjIso ωX A)
  let : (J ⊗ W).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight J W hW
  have hD : (W ⊗ J).IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso (β_ J W) inferInstance
  exact (isQuasicoherent X).prop_of_iso
    (originalTwistedMultiplierIso f n I hI q A hA) hD

end EnvelopeProperty.Vanishing.NadelRelativePrincipalizationTwistedMultiplier
