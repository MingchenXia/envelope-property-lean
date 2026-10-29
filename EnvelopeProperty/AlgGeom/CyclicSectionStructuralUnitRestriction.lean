import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverStructuralUnit
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCover
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-! # The original cyclic structural splitting after actual open restriction -/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionStructuralUnitRestriction

/-- The SAME canonical structural unit commutes with the native open cartesian comparison. -/
theorem restrictPushforwardUnit_triangle
    {Y X U V : Scheme.{u}} (f : Y ⟶ X) (f' : U ⟶ V)
    (iU : U ⟶ Y) (iV : V ⟶ X) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (H : IsPullback f' iU iV f) :
    (restrictFunctor iV).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (restrictPushforwardIsoOfIsPullbackApp f f' iU iV H (unitObj Y)).hom ≫
      (pushforward f').map (restrictUnitIso iU).hom =
    (restrictUnitIso iV).hom ≫
      SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
  let eR : Γ(Y, f ⁻¹ᵁ iV ''ᵁ W.unop) ≅ Γ(U, f' ⁻¹ᵁ W.unop) :=
    Y.presheaf.mapIso (eqToIso h).op ≪≫ iU.appIso _
  have hring : (iV.appIso W.unop).inv ≫ f.app _ = f'.app W.unop ≫ eR.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom',
      Scheme.Hom.map_appLE, eR, Scheme.Hom.appLE_comp_appLE, H.w]
  have he := congrArg (fun k => (iV.appIso W.unop).hom ≫ k ≫ eR.hom) hring
  have he' : f.app (iV ''ᵁ W.unop) ≫ eR.hom =
      (iV.appIso W.unop).hom ≫ f'.app W.unop := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using he
  change (iU.appIso (f' ⁻¹ᵁ W.unop)).hom
      (Y.presheaf.map (eqToHom h).op (f.app (iV ''ᵁ W.unop) x)) =
    f'.app W.unop ((iV.appIso W.unop).hom x)
  exact ConcreteCategory.congr_hom he' x

private def restrictRetraction
    {Y X U V : Scheme.{u}} (f : Y ⟶ X) (f' : U ⟶ V)
    (iU : U ⟶ Y) (iV : V ⟶ X) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (H : IsPullback f' iU iV f)
    (r : (pushforward f).obj (unitObj Y) ⟶ unitObj X) :
    (pushforward f').obj (unitObj U) ⟶ unitObj V :=
  (pushforward f').map (restrictUnitIso iU).inv ≫
    (restrictPushforwardIsoOfIsPullbackApp f f' iU iV H (unitObj Y)).inv ≫
    (restrictFunctor iV).map r ≫ (restrictUnitIso iV).hom

private theorem unit_comp_restrictRetraction
    {Y X U V : Scheme.{u}} (f : Y ⟶ X) (f' : U ⟶ V)
    (iU : U ⟶ Y) (iV : V ⟶ X) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (H : IsPullback f' iU iV f)
    (r : (pushforward f).obj (unitObj Y) ⟶ unitObj X)
    (hr : SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ r =
      𝟙 (unitObj X)) :
    SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
      restrictRetraction f f' iU iV H r = 𝟙 (unitObj V) := by
  apply (cancel_epi (restrictUnitIso iV).hom).1
  change (restrictUnitIso iV).hom ≫
      SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
        (pushforward f').map (restrictUnitIso iU).inv ≫
        (restrictPushforwardIsoOfIsPullbackApp f f' iU iV H (unitObj Y)).inv ≫
        (restrictFunctor iV).map r ≫ (restrictUnitIso iV).hom = _
  rw [← Category.assoc, ← restrictPushforwardUnit_triangle f f' iU iV H]
  simp only [Category.assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, hr]
  change 𝟙 _ ≫ (restrictUnitIso iV).hom = (restrictUnitIso iV).hom ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

open CyclicSectionGlobalCover

private instance toRootSpec_open (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (a : Γ(X, ⊤)) : IsOpenImmersion (toRootSpec X n a) :=
  MorphismProperty.of_isPullback (equation_isPullback X n a) inferInstance

/-- The actual scalar cyclic structural-unit retraction over ANY original affine scheme. -/
def affineBaseRetraction (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (a : Γ(X, ⊤)) (hn : 0 < n) :
    (pushforward (projection X n a)).obj (unitObj (equation X n a)) ⟶ unitObj X :=
  restrictRetraction (CyclicSectionAffineCover.structureMap n a)
    (projection X n a) (toRootSpec X n a) X.toSpecΓ (equation_isPullback X n a)
    (CyclicSectionGlobalCoverStructuralUnit.constantRetraction n a hn)

/-- Its composite with the SAME original scalar structural unit is the WHOLE identity. -/
theorem unit_comp_affineBaseRetraction (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (a : Γ(X, ⊤)) (hn : 0 < n) :
    SheafOfModules.unitToPushforwardObjUnit (projection X n a).toRingCatSheafHom ≫
      affineBaseRetraction X n a hn = 𝟙 (unitObj X) :=
  unit_comp_restrictRetraction (CyclicSectionAffineCover.structureMap n a)
    (projection X n a) (toRootSpec X n a) X.toSpecΓ (equation_isPullback X n a)
    (CyclicSectionGlobalCoverStructuralUnit.constantRetraction n a hn)
    (CyclicSectionGlobalCoverStructuralUnit.unit_comp_constantRetraction n a hn)

end EnvelopeProperty.CyclicSectionStructuralUnitRestriction
