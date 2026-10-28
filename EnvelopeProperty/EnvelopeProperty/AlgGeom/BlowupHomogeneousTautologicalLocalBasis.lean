import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalSpecFrames

/-! # Actual regular-generator bases for the original lifted form -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u v
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

private theorem nativeTensorBasis_inclusion {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (L I : C) (a : 𝟙_ C ≅ L) (b : I ⟶ 𝟙_ C) :
    (λ_ I).inv ≫ (a.hom ▷ I) ≫ (L ◁ b) ≫ (ρ_ L).hom = b ≫ a.hom := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality,
    ← leftUnitor_inv_naturality_assoc, ← unitors_equal]
  simp only [Iso.inv_hom_id_assoc]

private noncomputable instance localBasisMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

private def actualTensorBasis {X : Scheme.{u}} {L I : X.Modules}
    (e : L ≅ Scheme.Modules.unitObj X) (κ : Scheme.Modules.unitObj X ≅ I) :
    Scheme.Modules.unitObj X ≅ Scheme.Modules.tensorObj L I :=
  κ ≪≫ (λ_ I).symm ≪≫
    ((ModularCurves.monoidalUnitObjIso X ≪≫ e.symm) ⊗ᵢ Iso.refl I) ≪≫
    ModularCurves.monoidalTensorObjIso L I

private theorem actualTensorBasis_inclusion {X : Scheme.{u}} {L I : X.Modules}
    (e : L ≅ Scheme.Modules.unitObj X) (κ : Scheme.Modules.unitObj X ≅ I)
    (i : I ⟶ Scheme.Modules.unitObj X) :
    (actualTensorBasis e κ).hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap L I i ≫ e.hom =
      κ.hom ≫ i := by
  let c := ModularCurves.monoidalUnitObjIso X
  let a : 𝟙_ X.Modules ≅ L := c ≪≫ e.symm
  let s := ModularCurves.monoidalTensorObjIso L I
  let f := SchemeTensorObjMorphisms.tensorObjIdealMap L I i
  have hs : s.hom ≫ f = L ◁ (i ≫ c.inv) ≫ (ρ_ L).hom :=
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal L I i
  have hn := nativeTensorBasis_inclusion L I a (i ≫ c.inv)
  change (κ.hom ≫ (λ_ I).inv ≫ (a.hom ⊗ₘ 𝟙 I) ≫ s.hom) ≫ f ≫ e.hom = κ.hom ≫ i
  rw [tensorHom_id]
  calc
    _ = κ.hom ≫ ((λ_ I).inv ≫ (a.hom ▷ I) ≫ L ◁ (i ≫ c.inv) ≫ (ρ_ L).hom) ≫ e.hom := by
      simp only [Category.assoc]
      rw [← Category.assoc s.hom f e.hom, hs]
      simp only [Category.assoc]
    _ = κ.hom ≫ ((i ≫ c.inv) ≫ a.hom) ≫ e.hom :=
      congrArg (fun k => κ.hom ≫ k ≫ e.hom) hn
    _ = κ.hom ≫ i := by
      change κ.hom ≫ ((i ≫ c.inv) ≫ (c.hom ≫ e.inv)) ≫ e.hom = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem isIso_of_same_tensor_included_scalar {X : Scheme.{u}} {L I : X.Modules}
    (e : L ≅ Scheme.Modules.unitObj X) (κ : Scheme.Modules.unitObj X ≅ I)
    (i : I ⟶ Scheme.Modules.unitObj X)
    [Mono (SchemeTensorObjMorphisms.tensorObjIdealMap L I i)]
    (β : Scheme.Modules.unitObj X ⟶ Scheme.Modules.tensorObj L I)
    (h : β ≫ SchemeTensorObjMorphisms.tensorObjIdealMap L I i ≫ e.hom = κ.hom ≫ i) :
    IsIso β := by
  have hb := actualTensorBasis_inclusion e κ i
  have heq : β = (actualTensorBasis e κ).hom :=
    (cancel_mono (SchemeTensorObjMorphisms.tensorObjIdealMap L I i)).mp
      ((cancel_mono e.hom).mp
        (((Category.assoc _ _ _).trans h).trans
          ((Category.assoc _ _ _).trans hb).symm))
  rw [heq]
  infer_instance

private theorem pullbackSection_moduleComp {X Z : Scheme.{u}} (f : Z ⟶ X)
    {M N : X.Modules} (α : Scheme.Modules.unitObj X ⟶ M) (g : M ⟶ N) :
    SchemeLineSectionEvaluation.pullbackSectionHom f α ≫ (Scheme.Modules.pullback f).map g =
      SchemeLineSectionEvaluation.pullbackSectionHom f (α ≫ g) := by
  simp only [SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_comp, Category.assoc]

open DeJongAlterations.Geometry.ProjectiveIdeal MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private def nestedOriginalFormSpecFrame {R : Type u} [CommRing R] {n : ℕ}
    {X Z : Scheme.{u}} (μ : Z ⟶ X) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (U : Z.affineOpens) (i : Fin (n+1))
    (hi : U.1 ≤ (μ ≫ j) ⁻¹ᵁ nativeCoordinateOpen i) (d : ℕ) :
    (Scheme.Modules.pullback U.2.fromSpec).obj ((Scheme.Modules.pullback μ).obj
      ((Scheme.Modules.pullback j).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d))) ≅
      Scheme.Modules.unitObj (Spec Γ(Z, U)) :=
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  (Scheme.Modules.pullback U.2.fromSpec).mapIso ((Scheme.Modules.pullbackComp μ j).app M) ≪≫
    originalFormSpecFrame (μ ≫ j) U i hi d

private theorem nestedOriginalFormSpecFrame_scalar {R : Type u} [CommRing R] {n : ℕ}
    {X Z : Scheme.{u}} (μ : Z ⟶ X) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (U : Z.affineOpens) (i : Fin (n+1))
    (hi : U.1 ≤ (μ ≫ j) ⁻¹ᵁ nativeCoordinateOpen i) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec
        (SchemeLineSectionEvaluation.pullbackSectionHom μ
          (SchemeLineSectionEvaluation.pullbackSectionHom j
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF))) ≫
      (nestedOriginalFormSpecFrame μ j U i hi d).hom =
      ModularCurves.unitEndomorphismOfTopSection (originalFormSpecCoefficient (μ ≫ j) U i hi F) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let C := (Scheme.Modules.pullbackComp μ j).app M
  let α := ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF
  let a := SchemeLineSectionEvaluation.pullbackSectionHom μ
    (SchemeLineSectionEvaluation.pullbackSectionHom j α)
  let P := Scheme.Modules.pullback U.2.fromSpec
  let E := originalFormSpecFrame (μ ≫ j) U i hi d
  have hcomp : a ≫ C.hom = SchemeLineSectionEvaluation.pullbackSectionHom (μ ≫ j) α :=
    SchemeLineSectionEvaluation.pullbackSectionHom_comp μ j α
  have hp := pullbackSection_moduleComp U.2.fromSpec a C.hom
  have hs := hp.trans (congrArg
    (fun k : Scheme.Modules.unitObj Z ⟶ (Scheme.Modules.pullback (μ ≫ j)).obj M =>
      SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec k) hcomp)
  change SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec a ≫
    (P.map C.hom ≫ E.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ E.hom) hs).trans
      (originalFormSpecFrame_scalar (μ ≫ j) U i hi d F hF))

private theorem tensorIdealMap_mono {W : Scheme.{u}} (L I : W.Modules)
    (hL : Scheme.Modules.IsInvertible L) (i : I ⟶ Scheme.Modules.unitObj W) [Mono i] :
    Mono (SchemeTensorObjMorphisms.tensorObjIdealMap L I i) := by
  let : Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left L hL i
  change Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i ≫ (Scheme.Modules.tensorObjUnitIso L).hom)
  infer_instance

/-- On an actual original affine regular-generator chart, the SAME old form
lift is an actual native local basis. Its included scalar is derived internally
from the original homogeneous form; no section-matching identity is an input. -/
theorem liftedFormSection_isIso_of_regular_coefficient {R : Type u} [CommRing R] {n : ℕ}
    {X Z : Scheme.{u}} (μ : Z ⟶ X) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : Z.affineOpens) (i : Fin (n+1))
    (hi : U.1 ≤ (μ ≫ j) ⁻¹ᵁ nativeCoordinateOpen i)
    (hg : DeJongAlterations.Geometry.BlowupProjectiveEmbedding.pulledForm (μ ≫ j) U i hi F ∈
      nonZeroDivisors Γ(Z, U))
    (hK : (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ).ideal U =
      Ideal.span {DeJongAlterations.Geometry.BlowupProjectiveEmbedding.pulledForm (μ ≫ j) U i hi F}) :
    IsIso (SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec
      (liftedFormSection μ j J d F hF hFJ)) := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let L := (Scheme.Modules.pullback μ).obj ((Scheme.Modules.pullback j).obj M)
  let K := ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ
  let P := Scheme.Modules.pullback U.2.fromSpec
  let g := DeJongAlterations.Geometry.BlowupProjectiveEmbedding.pulledForm (μ ≫ j) U i hi F
  let e := nestedOriginalFormSpecFrame μ j U i hi d
  let κ := regularGeneratorPullbackBasis K U g hg hK
  let r : P.obj K.toModules ⟶ Scheme.Modules.unitObj (Spec Γ(Z, U)) :=
    P.map K.toModulesInclusion ≫ (Scheme.Modules.pullbackUnitIso U.2.fromSpec).hom
  let c := SchemeTensorIdealPullback.tensorObjPullbackIso U.2.fromSpec L K.toModules
  let β := liftedFormSection μ j J d F hF hFJ
  let b := SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec β
  let t := b ≫ c.hom
  let f := SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion
  let α := SchemeLineSectionEvaluation.pullbackSectionHom μ
    (SchemeLineSectionEvaluation.pullbackSectionHom j
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF))
  have hβ : β ≫ f = α := liftedFormSection_inclusion μ j J d F hF hFJ
  have hc : c.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (P.obj L) (P.obj K.toModules) r =
      P.map f := (SchemeTensorIdealPullback.tensorObjIdealMap_pullback U.2.fromSpec L
        K.toModules K.toModulesInclusion).symm
  have ht : t ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (P.obj L) (P.obj K.toModules) r =
      SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec α :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => b ≫ k) hc).trans
        ((pullbackSection_moduleComp U.2.fromSpec β f).trans
          (congrArg (fun k : Scheme.Modules.unitObj Z ⟶ L =>
            SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec k) hβ)))
  have hs : t ≫ SchemeTensorObjMorphisms.tensorObjIdealMap (P.obj L) (P.obj K.toModules) r ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (originalFormSpecCoefficient (μ ≫ j) U i hi F) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ e.hom) ht).trans
        (nestedOriginalFormSpecFrame_scalar μ j U i hi d F hF))
  have hκ : κ.hom ≫ r =
      ModularCurves.unitEndomorphismOfTopSection (originalFormSpecCoefficient (μ ≫ j) U i hi F) :=
    regularGeneratorPullbackBasis_inclusion K U g hg hK
  have hr : r = (K.openPullbackModuleIso U.2.fromSpec).hom ≫
      (K.comap U.2.fromSpec).toModulesInclusion :=
    (K.toModulesComapPullbackMap_inclusion U.2.fromSpec).symm
  let : Mono r := by
    let a := K.openPullbackModuleIso U.2.fromSpec
    let : IsIso a.hom := a.isIso_hom
    let : Mono (K.comap U.2.fromSpec).toModulesInclusion :=
      (K.comap U.2.fromSpec).toModulesInclusion_mono
    have hm : Mono (a.hom ≫ (K.comap U.2.fromSpec).toModulesInclusion) :=
      mono_comp a.hom (K.comap U.2.fromSpec).toModulesInclusion
    exact Eq.mpr (congrArg Mono hr) hm
  have hL : Scheme.Modules.IsInvertible (P.obj L) :=
    (((coordinateHyperplanePoleSheafPower_isInvertible (R := R) (0 : Fin (n+1)) d).pullback j).pullback μ).pullback U.2.fromSpec
  let : Mono (SchemeTensorObjMorphisms.tensorObjIdealMap (P.obj L) (P.obj K.toModules) r) :=
    tensorIdealMap_mono (P.obj L) (P.obj K.toModules) hL r
  have htIso : IsIso t := isIso_of_same_tensor_included_scalar e κ r t (hs.trans hκ.symm)
  let := htIso
  exact IsIso.of_isIso_comp_right b c.hom

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
