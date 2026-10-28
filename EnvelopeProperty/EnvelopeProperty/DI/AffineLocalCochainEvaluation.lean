import EnvelopeProperty.DI.AffineLocalMapRestriction
import EnvelopeProperty.DI.LocalRepresentativeRestriction
import EnvelopeProperty.DI.SingleFunctorHomology
import EnvelopeProperty.AlgGeom.SchemeSectionHomology

/-! # Native affine evaluation of the SAME original local sheaf cochain -/
noncomputable section
namespace EnvelopeProperty.DI.AffineLocalCochainEvaluation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
local notation "L" => Scheme.Modules.restrictFunctor W.ι
local notation "I" => Scheme.Modules.restrictFunctor hW.isoSpec.inv
local notation "J" => Scheme.Modules.restrictFunctor hW.fromSpec
private abbrev gammaFunctor : (Spec (Z.presheaf.obj (op W))).Modules ⥤
    ModuleCat (Z.presheaf.obj (op W)) := moduleSpecΓFunctor
local notation "G" => gammaFunctor (W := W)
private instance inverseChartZero : (I).PreservesZeroMorphisms := inferInstance
private instance gammaZero : (G).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private theorem specReadback_naturality {M N : Z.Modules} (φ : M ⟶ N) :
    (I).map ((L).map φ) ≫ (AffineLocalMapRestriction.specReadbackIso hW N).hom =
      (AffineLocalMapRestriction.specReadbackIso hW M).hom ≫ (J).map φ := by
  change (I).map ((L).map φ) ≫
      ((I).map (AffineLocalMapRestriction.chartRestrictionIso hW N).hom ≫
        (AffineLocalMapRestriction.specReturn hW).hom.app ((J).obj N)) =
    ((I).map (AffineLocalMapRestriction.chartRestrictionIso hW M).hom ≫
      (AffineLocalMapRestriction.specReturn hW).hom.app ((J).obj M)) ≫ (J).map φ
  rw [← Category.assoc, ← Functor.map_comp,
    AffineLocalMapRestriction.chartRestriction_naturality, Functor.map_comp, Category.assoc]
  exact (congrArg (fun t => (I).map (AffineLocalMapRestriction.chartRestrictionIso hW M).hom ≫ t)
    ((AffineLocalMapRestriction.specReturn hW).hom.naturality ((J).map φ))).trans
      (Category.assoc _ _ _).symm

/-- The entire original target complex survives inverse-chart restriction and original units. -/
def specComplexIso (K : CochainComplex Z.Modules ℕ) :
    ((I).mapHomologicalComplex (.up ℕ)).obj
        (SchemeOpenRestrictionHomology.restrictedComplex W.ι K) ≅
      SchemeOpenRestrictionHomology.restrictedComplex hW.fromSpec K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => AffineLocalMapRestriction.specReadbackIso hW (K.X q))
    (fun q r _ => (specReadback_naturality hW (K.d q r)).symm)

variable (q : ℕ) (M : Z.Modules) (K : CochainComplex Z.Modules ℕ)
  (φ : (HomologicalComplex.single W.toScheme.Modules (.up ℕ) q).obj (M.restrict W.ι) ⟶
    SchemeOpenRestrictionHomology.restrictedComplex W.ι K)

/-- The SAME original local sheaf cochain, transported to its original affine spectrum. -/
def specRepresentative :
    (HomologicalComplex.single (Spec Γ(Z,W)).Modules (.up ℕ) q).obj (M.restrict hW.fromSpec) ⟶
      SchemeOpenRestrictionHomology.restrictedComplex hW.fromSpec K :=
  (HomologicalComplex.single (Spec Γ(Z,W)).Modules (.up ℕ) q).map
      (AffineLocalMapRestriction.specReadbackIso hW M).inv ≫
    ((HomologicalComplex.singleMapHomologicalComplex (I) (.up ℕ) q).app (M.restrict W.ι)).inv ≫
    ((I).mapHomologicalComplex (.up ℕ)).map φ ≫ (specComplexIso hW K).hom

/-- Genuine spectrum sections and original source/target units evaluate this SAME whole cochain. -/
def evaluateCochain :
    (HomologicalComplex.single (ModuleCat Γ(Z,W)) (.up ℕ) q).obj (M.val.obj (op W)) ⟶
      SchemeSectionHomology.sectionComplex K W :=
  (HomologicalComplex.single (ModuleCat Γ(Z,W)) (.up ℕ) q).map
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).inv ≫
    ((HomologicalComplex.singleMapHomologicalComplex (G) (.up ℕ) q).app (M.restrict hW.fromSpec)).inv ≫
    ((G).mapHomologicalComplex (.up ℕ)).map (specRepresentative hW q M K φ) ≫
      (Cartier.GeometricAffineHomology.sectionComplexIso hW K).hom

/-- Supporting components retain precisely the ORIGINAL affine sheaf-map readback. -/
theorem evaluateCochain_f :
    (evaluateCochain hW q M K φ).f q =
      (HomologicalComplex.singleObjXSelf (.up ℕ) q (M.val.obj (op W))).hom ≫
        AffineLocalMapRestriction.sectionReadback hW M (K.X q)
          ((HomologicalComplex.singleObjXSelf (.up ℕ) q (M.restrict W.ι)).inv ≫ φ.f q) := by
  dsimp only [evaluateCochain, specRepresentative, HomologicalComplex.comp_f]
  change _ ≫ _ ≫ (G).map (_ ≫ _ ≫ (I).map (φ.f q) ≫
    (AffineLocalMapRestriction.specReadbackIso hW (K.X q)).hom) ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.X q)).hom = _
  simp only [Iso.app_inv, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  rfl

/-- The original readback is closed because the SAME evaluated map is a genuine cochain map. -/
theorem readback_closed : ∀ j, (ComplexShape.up ℕ).Rel q j →
    AffineLocalMapRestriction.sectionReadback hW M (K.X q)
      ((HomologicalComplex.singleObjXSelf (.up ℕ) q (M.restrict W.ι)).inv ≫ φ.f q) ≫
        (SchemeSectionHomology.sectionComplex K W).d q j = 0 := by
  intro j _
  apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℕ) q (M.val.obj (op W))).hom).mp
  rw [comp_zero, ← Category.assoc, ← evaluateCochain_f, (evaluateCochain hW q M K φ).comm,
    HomologicalComplex.single_obj_d, zero_comp]

/-- This WHOLE actual evaluated sheaf cochain is the native representative of its ORIGINAL readback. -/
theorem evaluateCochain_eq :
    evaluateCochain hW q M K φ =
      HomologicalComplex.mkHomFromSingle
        (AffineLocalMapRestriction.sectionReadback hW M (K.X q)
          ((HomologicalComplex.singleObjXSelf (.up ℕ) q (M.restrict W.ι)).inv ≫ φ.f q))
        (readback_closed hW q M K φ) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [evaluateCochain_f, HomologicalComplex.mkHomFromSingle_f]
end EnvelopeProperty.DI.AffineLocalCochainEvaluation
