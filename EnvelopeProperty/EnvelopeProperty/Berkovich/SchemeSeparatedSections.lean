/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Genuine separated affine intersection tensor sections

The actual separated diagonal and true affine product isomorphisms produce
a surjective tensor section map with both exact restriction formulas.
Lifted integer coefficients merely keep actual scheme universes aligned.
No tensor presentation of the intersection or analytic property is assumed.
-/


open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace EnvelopeProperty

/-- The canonical lifted integer action, used only to keep actual schemes in one universe. -/
@[instance_reducible]
def liftedIntegerAlgebra (A : Type u) [CommRing A] : Algebra (ULift.{u} ℤ) A :=
  ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom).toAlgebra

namespace SchemeSeparatedSections

variable {X : Scheme.{u}}

private local instance sectionCommRing (A : CommRingCat.{u}) : CommRing A := A.commRing

private local instance (priority := low) sectionIntegerAlgebra (A : Type u) [CommRing A] : Algebra (ULift.{u} ℤ) A :=
  liftedIntegerAlgebra A

private local instance sectionIntegerModule (A : Type u) [CommRing A] : Module (ULift.{u} ℤ) A :=
  Algebra.toModule



/-- The genuine scheme intersection is the actual pullback of its open inclusions. -/
def intersectionPullbackIso (U V : X.Opens) :
    (U ⊓ V).toScheme ≅ pullback U.ι V.ι :=
  (IsOpenImmersion.isPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right)
    U.ι V.ι (by simp) (by ext; simp)).isoPullback

/-- The affine product comparison uses genuine chart isomorphisms and the actual terminal coefficient scheme. -/
def affineProductSpecIso (U V : X.affineOpens) :
    pullback (U.1.ι ≫ specULiftZIsTerminal.from X) (V.1.ι ≫ specULiftZIsTerminal.from X) ≅
      Spec (CommRingCat.of (Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V))) :=
  (asIso (pullback.map _ _
    (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) Γ(X, U))))
    (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) Γ(X, V))))
    U.2.isoSpec.hom V.2.isoSpec.hom (𝟙 _) (specULiftZIsTerminal.hom_ext _ _)
    (specULiftZIsTerminal.hom_ext _ _))).trans (pullbackSpecIso (ULift.{u} ℤ) Γ(X, U) Γ(X, V))

/-- The genuine affine intersection maps to its coefficient tensor product through the actual scheme diagonal. -/
def intersectionToTensorSpec (U V : X.affineOpens) :
    (U.1 ⊓ V.1).toScheme ⟶ Spec (CommRingCat.of (Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V))) :=
  (intersectionPullbackIso U.1 V.1).hom ≫
    pullback.mapDesc U.1.ι V.1.ι (specULiftZIsTerminal.from X) ≫ (affineProductSpecIso U V).hom

/-- Actual separatedness makes the tensor comparison a genuine closed immersion. -/
theorem isClosedImmersion_intersectionToTensorSpec [X.IsSeparated] (U V : X.affineOpens) :
    IsClosedImmersion (intersectionToTensorSpec U V) := by
  dsimp only [intersectionToTensorSpec]
  infer_instance

/-- The actual tensor comparison's first scheme projection is the genuine affine inclusion. -/
theorem intersectionToTensorSpec_fst (U V : X.affineOpens) :
    intersectionToTensorSpec U V ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X, U) →+* Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V))) =
      X.homOfLE (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left) ≫ U.2.isoSpec.hom := by
  simp only [intersectionToTensorSpec, affineProductSpecIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullbackSpecIso_hom_fst, pullback.mapDesc, pullback.map,
    pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, intersectionPullbackIso,
    IsPullback.isoPullback_hom_fst_assoc]

/-- The actual tensor comparison's second scheme projection is the genuine affine inclusion. -/
theorem intersectionToTensorSpec_snd (U V : X.affineOpens) :
    intersectionToTensorSpec U V ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(X, V) →+* Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V))) =
      X.homOfLE (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right) ≫ V.2.isoSpec.hom := by
  have hp : (pullbackSpecIso (ULift.{u} ℤ) Γ(X, U) Γ(X, V)).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(X, V) →+* Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V))) = pullback.snd _ _ :=
    pullbackSpecIso_hom_snd _ _ _
  simp only [intersectionToTensorSpec, affineProductSpecIso, Iso.trans_hom, asIso_hom,
    Category.assoc, hp, pullback.mapDesc, pullback.map,
    pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, intersectionPullbackIso,
    IsPullback.isoPullback_hom_snd_assoc]

/-- The true tensor-to-intersection section ring map induced by this actual scheme comparison. -/
def tensorSectionMap (U V : X.affineOpens) :
    Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V) →+* Γ(X, U.1 ⊓ V.1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V)))).inv ≫
    (intersectionToTensorSpec U V).appTop ≫ (U.1 ⊓ V.1).topIso.hom).hom

/-- Genuine global section isomorphisms of open subschemes respect every actual restriction. -/
theorem topIso_naturality {U V : X.Opens} (h : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE h).appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE h).op := by
  have hn := X.restrictFunctorΓ.hom.naturality (homOfLE h).op
  change (X.homOfLE h).appTop ≫ U.topIso.hom = V.topIso.hom ≫ X.presheaf.map (homOfLE h).op at hn
  rw [hn, Iso.inv_hom_id_assoc]

/-- The actual tensor map on the left section-ring inclusion is the genuine section restriction. -/
theorem tensorSectionMap_comp_includeLeft (U V : X.affineOpens) :
    (tensorSectionMap U V).comp (Algebra.TensorProduct.includeLeftRingHom :
      Γ(X, U) →+* Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V)) =
        (X.presheaf.map (homOfLE (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left)).op).hom := by
  have h := congrArg (fun q => (Scheme.ΓSpecIso Γ(X, U)).inv ≫ q.appTop ≫ (U.1 ⊓ V.1).topIso.hom)
    (intersectionToTensorSpec_fst U V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  simp only [Category.assoc] at h
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, U.2.isoSpec_hom_appTop] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [topIso_naturality] at h
  exact congrArg CommRingCat.Hom.hom h

/-- The actual tensor map on the right section-ring inclusion is the genuine section restriction. -/
theorem tensorSectionMap_comp_includeRight (U V : X.affineOpens) :
    (tensorSectionMap U V).comp (Algebra.TensorProduct.includeRight.toRingHom :
      Γ(X, V) →+* Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V)) =
        (X.presheaf.map (homOfLE (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right)).op).hom := by
  have h := congrArg (fun q => (Scheme.ΓSpecIso Γ(X, V)).inv ≫ q.appTop ≫ (U.1 ⊓ V.1).topIso.hom)
    (intersectionToTensorSpec_snd U V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  simp only [Category.assoc] at h
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, V.2.isoSpec_hom_appTop] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [topIso_naturality] at h
  exact congrArg CommRingCat.Hom.hom h

/-- Every genuine tensor has the actual product of its two restricted section values. -/
theorem tensorSectionMap_tmul (U V : X.affineOpens) (a : Γ(X, U)) (b : Γ(X, V)) :
    tensorSectionMap U V (a ⊗ₜ[ULift.{u} ℤ] b) =
      X.presheaf.map (homOfLE (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left)).op a *
        X.presheaf.map (homOfLE (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right)).op b := by
  have ha := RingHom.congr_fun (tensorSectionMap_comp_includeLeft U V) a
  have hb := RingHom.congr_fun (tensorSectionMap_comp_includeRight U V) b
  have ht : a ⊗ₜ[ULift.{u} ℤ] b = (a ⊗ₜ[ULift.{u} ℤ] (1 : Γ(X, V))) *
      ((1 : Γ(X, U)) ⊗ₜ[ULift.{u} ℤ] b) := by simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [ht, map_mul]
  exact congrArg₂ (· * ·) ha hb

/-- Surjectivity is produced by the true separated diagonal, not assumed as a tensor presentation. -/
theorem tensorSectionMap_surjective [X.IsSeparated] (U V : X.affineOpens) :
    Function.Surjective (tensorSectionMap U V) := by
  let : IsClosedImmersion (intersectionToTensorSpec U V) := isClosedImmersion_intersectionToTensorSpec U V
  exact (ConcreteCategory.bijective_of_isIso (U.1 ⊓ V.1).topIso.hom).2.comp
    (((intersectionToTensorSpec U V).app_surjective ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
        (CommRingCat.of (Γ(X, U) ⊗[ULift.{u} ℤ] Γ(X, V)))).inv).2)

end SchemeSeparatedSections
end EnvelopeProperty
