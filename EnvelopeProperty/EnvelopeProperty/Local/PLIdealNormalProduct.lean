/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyNormal
import EnvelopeProperty.Local.NativeProductIntegrality
import EnvelopeProperty.AlgGeom.PolynomialSchemeBaseChangeStalks
import EnvelopeProperty.Local.PLIdealPrincipalization
import EnvelopeProperty.AlgGeom.ProjectiveStrongResolution

/-! # Original integral normal polynomial variety products and simultaneous blowups -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Polynomial NNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Original projective normality derives integral closedness of EVERY
stalk of the SAME actual original variety-polynomial product. -/
theorem nativeProductModel_stalk_isIntegrallyClosed (hX : X.IsProjNormal)
    (z : X.NativeProductModel) : IsIntegrallyClosed (X.NativeProductModel.presheaf.stalk z) := by
  let : IsIntegral X.NativeScheme := X.originalNativeScheme_isIntegral
  have : IsIntegrallyClosed ((pullback X.nativeStructure
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))).presheaf.stalk
      (X.nativeProductModelIso.hom z)) :=
    PolynomialSchemeBaseChangeNormal.polynomialBaseChange_stalk_isIntegrallyClosed X.nativeStructure
      (X.originalNativeScheme_stalk_isIntegrallyClosed hX) _
  exact IsIntegrallyClosed.of_equiv
    (asIso (X.nativeProductModelIso.hom.stalkMap z)).commRingCatIsoToRingEquiv

/-- The ACTUAL original coefficient-field structure on the same original
variety product, through its literal original polynomial-base structure. -/
def nativeProductFieldStructure : X.NativeProductModel ⟶ Spec (.of k) :=
  X.nativeProductStructure ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

/-- Finite type over the SAME original field is derived for the actual
variety-polynomial product, with no supplied algebraic-model hypothesis. -/
theorem nativeProductFieldStructure_locallyOfFiniteType : LocallyOfFiniteType X.nativeProductFieldStructure := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  dsimp [nativeProductFieldStructure]
  infer_instance

variable (I J : X.NativeProductModel.IdealSheafData)

/-- Finite original ideal logarithms produce actual nonemptiness and hence
integrality of the SAME constructed original simultaneous blowup. -/
theorem simultaneousIdealBlowup_isIntegral_of_finiteLogs (w : X.an)
    (hI : modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    IsIntegral (X.simultaneousIdealBlowup I J) := by
  let : IsIntegral X.NativeProductModel := X.nativeProductModel_isIntegral
  let : Nonempty (X.simultaneousIdealBlowup I J) :=
    ⟨(X.simultaneousIdealBlowupGaussPoint I J w hI hJ).1.point⟩
  exact ProjectiveStrongResolution.isIntegral_blowup_of_nonempty (I * J)

/-- The actual original simultaneous blowup's SAME original coefficient-field structure. -/
def simultaneousIdealBlowupFieldStructure : X.simultaneousIdealBlowup I J ⟶ Spec (.of k) :=
  X.simultaneousIdealBlowupStructure I J ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

/-- The actual original simultaneous blowup is locally finite type over
its SAME original field, deriving every geometric finite-type premise. -/
theorem simultaneousIdealBlowupFieldStructure_locallyOfFiniteType :
    LocallyOfFiniteType (X.simultaneousIdealBlowupFieldStructure I J) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  dsimp [simultaneousIdealBlowupFieldStructure]
  infer_instance

end EnvelopeProperty.ProjSubvariety
