import EnvelopeProperty.DI.AffineLocalCochainEvaluation
import EnvelopeProperty.Cartier.GeometricHomologyNaturality

/-! # Actual original sheaf H-map and canonical affine evaluation of the SAME local cochain -/
noncomputable section
namespace EnvelopeProperty.DI.AffineLocalCochainHomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
local notation "J" => Scheme.Modules.restrictFunctor hW.fromSpec
private abbrev gammaFunctor : (Spec (Z.presheaf.obj (op W))).Modules ⥤
    ModuleCat (Z.presheaf.obj (op W)) := moduleSpecΓFunctor
local notation "G" => gammaFunctor (W := W)
private abbrev evaluation : Z.Modules ⥤ ModuleCat (Z.presheaf.obj (op W)) :=
  SheafOfModules.evaluation Z.ringCatSheaf (op W)
local notation "EV" => evaluation (W := W)
private instance gammaZero : (G).PreservesZeroMorphisms where
  map_zero _ _ := rfl
private instance gammaLimits : PreservesFiniteLimits (G) := by
  let : (G).IsRightAdjoint := (tilde.adjunction (R := Γ(Z,W))).isRightAdjoint
  infer_instance
private instance restrictionLimits : PreservesFiniteLimits (J) := by
  let : PreservesLimits (J) := Scheme.Modules.restrictFunctor_preservesLimits hW.fromSpec
  infer_instance
private instance restrictionHomology : (J).PreservesHomology :=
  SchemeOpenRestrictionHomology.preservesHomology hW.fromSpec
private instance evaluationZero : (EV).PreservesZeroMorphisms where
  map_zero _ _ := rfl
private instance evaluationLimits : PreservesFiniteLimits (EV) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := Z.ringCatSheaf) (op W)
private instance chartGammaZero : ((J) ⋙ (G)).PreservesZeroMorphisms where
  map_zero M N := (congrArg (G).map ((J).map_zero M N)).trans ((G).map_zero _ _)
private instance chartGammaLimits : PreservesFiniteLimits ((J) ⋙ (G)) :=
  comp_preservesFiniteLimits _ _

private theorem chartComparison (K : CochainComplex Z.Modules ℕ) (q : ℕ) :
    HomologicalComplex.homologyMap (Cartier.GeometricAffineHomology.sectionComplexIso hW K).hom q ≫
        SchemeSectionHomology.comparison K W q =
      LeftExactHomologyComparison.map
          ((SchemeOpenRestrictionHomology.restrictedComplex hW.fromSpec K).sc q) (G) ≫
        (G).map (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom ≫
        (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom := by
  let S := K.sc q
  let α := AffineRestrictionSections.functorIso hW
  have hc : (AffineRestrictionSections.complexIso hW K).hom =
      (Cartier.GeometricAffineHomology.sectionComplexIso hW K).hom := by
    apply HomologicalComplex.Hom.ext
    funext r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hH : ShortComplex.homologyMap (S.mapNatTrans α.hom) =
      HomologicalComplex.homologyMap (Cartier.GeometricAffineHomology.sectionComplexIso hW K).hom q := by
    change HomologicalComplex.homologyMap (AffineRestrictionSections.complexIso hW K).hom q = _
    exact congrArg (fun t => HomologicalComplex.homologyMap t q) hc
  have hα : α.hom.app (K.homology q) =
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hn : HomologicalComplex.homologyMap
        (Cartier.GeometricAffineHomology.sectionComplexIso hW K).hom q ≫
        SchemeSectionHomology.comparison K W q =
      LeftExactHomologyComparison.map S ((J) ⋙ (G)) ≫
        (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom :=
    (congrArg (fun t => t ≫ LeftExactHomologyComparison.map S (EV)) hH.symm).trans
      ((LeftExactHomologyComparison.natTrans_naturality (S := S) (EV) α.hom).trans
        (congrArg (fun t => LeftExactHomologyComparison.map S ((J) ⋙ (G)) ≫ t) hα))
  have hn' := hn.trans (congrArg (fun t => t ≫
    (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom)
      (LeftExactHomologyCoherence.map_comp S (J) (G)))
  have hJ : (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom =
      LeftExactHomologyComparison.map S (J) :=
    (LeftExactHomologyCoherence.map_eq_mapHomologyIso S (J)).symm
  exact hn'.trans (congrArg (fun t =>
    LeftExactHomologyComparison.map (S.map (J)) (G) ≫ (G).map t ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom) hJ.symm)

variable (q : ℕ) (M : Z.Modules) (K : CochainComplex Z.Modules ℕ)
  (φ : (HomologicalComplex.single W.toScheme.Modules (.up ℕ) q).obj (M.restrict W.ι) ⟶
    SchemeOpenRestrictionHomology.restrictedComplex W.ι K)

/-- The ACTUAL induced sheaf homology map, with ORIGINAL source and target chart units. -/
def specHomologyReadback : M.val.obj (op W) ⟶ (K.homology q).val.obj (op W) :=
  (Cartier.GeometricAffineHomology.moduleSectionsIso hW M).inv ≫
    (G).map ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.restrict hW.fromSpec)).inv ≫
      HomologicalComplex.homologyMap
        (AffineLocalCochainEvaluation.specRepresentative hW q M K φ) q) ≫
    (G).map (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom ≫
    (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom

/-- The ENTIRE same actual sheaf H-map equals native evaluated H followed by canonical original comparison. -/
theorem canonical_class :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.val.obj (op W))).inv ≫
        HomologicalComplex.homologyMap (AffineLocalCochainEvaluation.evaluateCochain hW q M K φ) q ≫
        SchemeSectionHomology.comparison K W q = specHomologyReadback hW q M K φ := by
  let KC := SchemeOpenRestrictionHomology.restrictedComplex hW.fromSpec K
  let Ψ := AffineLocalCochainEvaluation.specRepresentative hW q M K φ
  let Ω := SingleFunctorHomology.sectionComponent (G) q (M.restrict hW.fromSpec) KC Ψ
  let hΩ := SingleFunctorHomology.sectionComponent_closed (G) q (M.restrict hW.fromSpec) KC Ψ
  let L := HomologicalComplex.mkHomFromSingle Ω hΩ
  let eM := Cartier.GeometricAffineHomology.moduleSectionsIso hW M
  let eΓ := Cartier.GeometricAffineHomology.sectionComplexIso hW K
  have hΨ : ((HomologicalComplex.singleMapHomologicalComplex (G) (.up ℕ) q).app
        (M.restrict hW.fromSpec)).inv ≫ ((G).mapHomologicalComplex (.up ℕ)).map Ψ = L := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    change _ ≫ (G).map (HomologicalComplex.singleObjXSelf (.up ℕ) q
      (M.restrict hW.fromSpec)).inv ≫ (G).map (Ψ.f q) =
      (HomologicalComplex.mkHomFromSingle Ω hΩ).f q
    exact (congrArg (fun t =>
      (HomologicalComplex.singleObjXSelf (.up ℕ) q ((G).obj (M.restrict hW.fromSpec))).hom ≫ t)
        ((G).map_comp (HomologicalComplex.singleObjXSelf (.up ℕ) q (M.restrict hW.fromSpec)).inv
          (Ψ.f q)).symm).trans (HomologicalComplex.mkHomFromSingle_f Ω hΩ).symm
  have heval : AffineLocalCochainEvaluation.evaluateCochain hW q M K φ =
      (HomologicalComplex.single (ModuleCat Γ(Z,W)) (.up ℕ) q).map eM.inv ≫ L ≫ eΓ.hom := by
    simpa only [AffineLocalCochainEvaluation.evaluateCochain, Category.assoc] using
      congrArg (fun t => (HomologicalComplex.single (ModuleCat Γ(Z,W)) (.up ℕ) q).map eM.inv ≫
        t ≫ eΓ.hom) hΨ
  have hclass :
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.val.obj (op W))).inv ≫
        HomologicalComplex.homologyMap (AffineLocalCochainEvaluation.evaluateCochain hW q M K φ) q =
      eM.inv ≫ LeadingCartierCycleTransport.singleClassMap q ((G).obj (M.restrict hW.fromSpec))
        (((G).mapHomologicalComplex (.up ℕ)).obj KC) Ω hΩ ≫
          HomologicalComplex.homologyMap eΓ.hom q := by
    have hu := HomologicalComplex.singleObjHomologySelfIso_inv_naturality (.up ℕ) q eM.inv
    rw [heval, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    change ((HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M.val.obj (op W))).inv ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex.single (ModuleCat Γ(Z,W)) (.up ℕ) q).map eM.inv) q) ≫
      (HomologicalComplex.homologyMap L q ≫ HomologicalComplex.homologyMap eΓ.hom q) = _
    exact (congrArg (fun t => t ≫
      (HomologicalComplex.homologyMap L q ≫ HomologicalComplex.homologyMap eΓ.hom q)) hu).trans
      (Category.assoc _ _ _)
  rw [← Category.assoc, hclass]
  simp only [Category.assoc]
  rw [chartComparison]
  have hs := SingleFunctorHomology.singleClassMap_evaluation (G) q (M.restrict hW.fromSpec) KC Ψ
  change LeadingCartierCycleTransport.singleClassMap q ((G).obj (M.restrict hW.fromSpec))
      (((G).mapHomologicalComplex (.up ℕ)).obj KC) Ω hΩ ≫
      LeftExactHomologyComparison.map (KC.sc q) (G) = _ at hs
  simpa only [specHomologyReadback, Category.assoc] using
    congrArg (fun t => eM.inv ≫ t ≫
      (G).map (SchemeOpenRestrictionHomology.homologyIso hW.fromSpec K q).hom ≫
      (Cartier.GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom) hs
end EnvelopeProperty.DI.AffineLocalCochainHomology
