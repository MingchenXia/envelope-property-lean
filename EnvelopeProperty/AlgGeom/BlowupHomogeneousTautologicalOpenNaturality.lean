import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalFractionBases
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Canonical open pullback of the whole original ideal-tensor line -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u v
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

private theorem nativeIdealNaturality {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {L L' I J : C} (a : L ⟶ L') (b : I ⟶ J) (i : I ⟶ 𝟙_ C) (j : J ⟶ 𝟙_ C)
    (h : b ≫ j = i) :
    (a ⊗ₘ b) ≫ (L' ◁ j) ≫ (ρ_ L').hom = (L ◁ i) ≫ (ρ_ L).hom ≫ a := by
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, h, ← whisker_exchange_assoc, rightUnitor_naturality]

private noncomputable instance openNaturalityMonoidal (W : Scheme.{u}) :
    MonoidalCategory W.Modules := Scheme.Modules.monoidalCategory W

private theorem explicitIdealNaturality {W : Scheme.{u}} {L L' I J : W.Modules}
    (a : L ⟶ L') (b : I ⟶ J)
    (i : I ⟶ Scheme.Modules.unitObj W) (j : J ⟶ Scheme.Modules.unitObj W)
    (h : b ≫ j = i) :
    SchemeTensorObjMorphisms.tensorObjMap a b ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap L' J j =
      SchemeTensorObjMorphisms.tensorObjIdealMap L I i ≫ a := by
  let s := ModularCurves.monoidalTensorObjIso L I
  let t := ModularCurves.monoidalTensorObjIso L' J
  let c := ModularCurves.monoidalUnitObjIso W
  have hm : s.hom ≫ SchemeTensorObjMorphisms.tensorObjMap a b = (a ⊗ₘ b) ≫ t.hom := by
    apply (cancel_mono t.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [SchemeTensorObjMorphisms.tensorObjMap_monoidal, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have hi : b ≫ (j ≫ c.inv) = i ≫ c.inv :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ c.inv) h)
  apply (cancel_epi s.hom).mp
  calc
    s.hom ≫ (SchemeTensorObjMorphisms.tensorObjMap a b ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap L' J j) =
        (a ⊗ₘ b) ≫ (L' ◁ (j ≫ c.inv)) ≫ (ρ_ L').hom := by
      rw [← Category.assoc, hm, Category.assoc,
        SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
    _ = (L ◁ (i ≫ c.inv)) ≫ (ρ_ L).hom ≫ a := nativeIdealNaturality a b (i ≫ c.inv) (j ≫ c.inv) hi
    _ = s.hom ≫ (SchemeTensorObjMorphisms.tensorObjIdealMap L I i ≫ a) := by
      exact (congrArg (fun k => k ≫ a)
        (SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal L I i)).symm.trans
          (Category.assoc _ _ _)

private def idealModulesEqIso {W : Scheme.{u}} {I J : W.IdealSheafData} (h : I = J) :
    I.toModules ≅ J.toModules :=
  eqToIso (congrArg (fun K : W.IdealSheafData => K.toModules) h)

private def tensorChangeIdealIso {W : Scheme.{u}} {L L' : W.Modules}
    {I J : W.IdealSheafData} (e : L ≅ L') (h : I = J) :
    Scheme.Modules.tensorObj L I.toModules ≅ Scheme.Modules.tensorObj L' J.toModules :=
  Scheme.Modules.tensorObjCongr e (idealModulesEqIso h)

private theorem tensorChangeIdealIso_inclusion {W : Scheme.{u}} {L L' : W.Modules}
    {I J : W.IdealSheafData} (e : L ≅ L') (h : I = J) :
    (tensorChangeIdealIso e h).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap L' J.toModules J.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion ≫ e.hom := by
  cases h
  change SchemeTensorObjMorphisms.tensorObjMap e.hom (𝟙 I.toModules) ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap L' I.toModules I.toModulesInclusion = _
  exact explicitIdealNaturality e.hom (𝟙 I.toModules)
    I.toModulesInclusion I.toModulesInclusion (Category.id_comp _)

private def openTensorChangeIso {Z W : Scheme.{u}} (u : W ⟶ Z) [IsOpenImmersion u]
    (L : Z.Modules) (K : Z.IdealSheafData) {L' : W.Modules} {J : W.IdealSheafData}
    (e : (Scheme.Modules.pullback u).obj L ≅ L') (h : K.comap u = J) :
    (Scheme.Modules.pullback u).obj (Scheme.Modules.tensorObj L K.toModules) ≅
      Scheme.Modules.tensorObj L' J.toModules :=
  SchemeTensorIdealPullback.idealTensorOpenPullbackIso u L K ≪≫ tensorChangeIdealIso e h

private theorem openTensorChangeIso_inclusion {Z W : Scheme.{u}} (u : W ⟶ Z)
    [IsOpenImmersion u] (L : Z.Modules) (K : Z.IdealSheafData)
    {L' : W.Modules} {J : W.IdealSheafData}
    (e : (Scheme.Modules.pullback u).obj L ≅ L') (h : K.comap u = J) :
    (openTensorChangeIso u L K e h).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap L' J.toModules J.toModulesInclusion =
      (Scheme.Modules.pullback u).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion) ≫ e.hom := by
  rw [openTensorChangeIso, Iso.trans_hom, Category.assoc,
    tensorChangeIdealIso_inclusion, ← Category.assoc]
  exact congrArg (fun t => t ≫ e.hom)
    (SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion u L K)

private theorem idealComapComp {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z)
    (D : X.IdealSheafData) : (D.comap μ).comap u = D.comap (u ≫ μ) := by
  rw [Scheme.IdealSheafData.comap_comp]

/-- The canonical entire target comparison under an actual open immersion,
using the same original module, ideal and two morphisms. -/
def openIdealTensorCompIso {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z)
    [IsOpenImmersion u] (M : X.Modules) (D : X.IdealSheafData) :
    (Scheme.Modules.pullback u).obj
        (Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback (u ≫ μ)).obj M)
        (D.comap (u ≫ μ)).toModules :=
  openTensorChangeIso u ((Scheme.Modules.pullback μ).obj M) (D.comap μ)
    (L' := (Scheme.Modules.pullback (u ≫ μ)).obj M) (J := D.comap (u ≫ μ))
    ((Scheme.Modules.pullbackComp u μ).app M) (idealComapComp μ u D)

/-- The canonical comparison respects the entire original tensor-ideal
inclusion and the same original line-composition morphism. -/
theorem openIdealTensorCompIso_inclusion {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z)
    [IsOpenImmersion u] (M : X.Modules) (D : X.IdealSheafData) :
    (openIdealTensorCompIso μ u M D).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback (u ≫ μ)).obj M)
          (D.comap (u ≫ μ)).toModules (D.comap (u ≫ μ)).toModulesInclusion =
      (Scheme.Modules.pullback u).map
          (SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback μ).obj M)
            (D.comap μ).toModules (D.comap μ).toModulesInclusion) ≫
        ((Scheme.Modules.pullbackComp u μ).app M).hom :=
  openTensorChangeIso_inclusion u ((Scheme.Modules.pullback μ).obj M) (D.comap μ)
    (L' := (Scheme.Modules.pullback (u ≫ μ)).obj M) (J := D.comap (u ≫ μ))
    ((Scheme.Modules.pullbackComp u μ).app M) (idealComapComp μ u D)

private theorem pullbackSection_moduleComp {Z W : Scheme.{u}} (u : W ⟶ Z)
    {M N : Z.Modules} (α : Scheme.Modules.unitObj Z ⟶ M) (f : M ⟶ N) :
    SchemeLineSectionEvaluation.pullbackSectionHom u α ≫ (Scheme.Modules.pullback u).map f =
      SchemeLineSectionEvaluation.pullbackSectionHom u (α ≫ f) := by
  simp only [SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_comp, Category.assoc]

private theorem pullbackSection_compIso {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z)
    {M : X.Modules} (α : Scheme.Modules.unitObj X ⟶ M) :
    SchemeLineSectionEvaluation.pullbackSectionHom u
        (SchemeLineSectionEvaluation.pullbackSectionHom μ α) ≫
        ((Scheme.Modules.pullbackComp u μ).app M).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom (u ≫ μ) α := by
  have h := congrArg
    (fun t : (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback μ).obj M) ⟶
        (Scheme.Modules.pullback (u ≫ μ)).obj M =>
      SchemeLineSectionEvaluation.pullbackSectionHom u
        (SchemeLineSectionEvaluation.pullbackSectionHom μ α) ≫ t)
    (Iso.app_hom (Scheme.Modules.pullbackComp u μ) M)
  exact h.trans (SchemeLineSectionEvaluation.pullbackSectionHom_comp u μ α)

private theorem tensorIdealInclusion_mono {W : Scheme.{u}} (L : W.Modules)
    (hL : Scheme.Modules.IsInvertible L) (K : W.IdealSheafData) :
    Mono (SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion) := by
  let i : K.toModules ⟶ Scheme.Modules.unitObj W := K.toModulesInclusion
  let : Mono i := K.toModulesInclusion_mono
  let : Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left L hL i
  change Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i ≫
    (Scheme.Modules.tensorObjUnitIso L).hom)
  exact mono_comp _ _

private theorem openLift_eq {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z)
    [IsOpenImmersion u] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (D : X.IdealSheafData) (α : Scheme.Modules.unitObj X ⟶ M)
    (β : Scheme.Modules.unitObj Z ⟶
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules)
    (β' : Scheme.Modules.unitObj W ⟶
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback (u ≫ μ)).obj M)
        (D.comap (u ≫ μ)).toModules)
    (hβ : β ≫ SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules (D.comap μ).toModulesInclusion =
        SchemeLineSectionEvaluation.pullbackSectionHom μ α)
    (hβ' : β' ≫ SchemeTensorObjMorphisms.tensorObjIdealMap ((Scheme.Modules.pullback (u ≫ μ)).obj M)
      (D.comap (u ≫ μ)).toModules (D.comap (u ≫ μ)).toModulesInclusion =
        SchemeLineSectionEvaluation.pullbackSectionHom (u ≫ μ) α) :
    SchemeLineSectionEvaluation.pullbackSectionHom u β ≫ (openIdealTensorCompIso μ u M D).hom = β' := by
  let P := Scheme.Modules.pullback u
  let L := (Scheme.Modules.pullback μ).obj M
  let L' := (Scheme.Modules.pullback (u ≫ μ)).obj M
  let K := D.comap μ
  let K' := D.comap (u ≫ μ)
  let i := SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion
  let i' := SchemeTensorObjMorphisms.tensorObjIdealMap L' K'.toModules K'.toModulesInclusion
  let E := openIdealTensorCompIso μ u M D
  let C := (Scheme.Modules.pullbackComp u μ).app M
  let b := SchemeLineSectionEvaluation.pullbackSectionHom u β
  let : Mono i' := tensorIdealInclusion_mono L' (hM.pullback (u ≫ μ)) K'
  apply (cancel_mono i').mp
  have he : E.hom ≫ i' = P.map i ≫ C.hom := openIdealTensorCompIso_inclusion μ u M D
  calc
    (b ≫ E.hom) ≫ i' = b ≫ (E.hom ≫ i') := Category.assoc _ _ _
    _ = b ≫ (P.map i ≫ C.hom) := congrArg (fun q => b ≫ q) he
    _ = (b ≫ P.map i) ≫ C.hom := (Category.assoc _ _ _).symm
    _ = SchemeLineSectionEvaluation.pullbackSectionHom u (β ≫ i) ≫ C.hom :=
      congrArg (fun q => q ≫ C.hom) (pullbackSection_moduleComp u β i)
    _ = SchemeLineSectionEvaluation.pullbackSectionHom u
        (SchemeLineSectionEvaluation.pullbackSectionHom μ α) ≫ C.hom :=
      congrArg (fun q => SchemeLineSectionEvaluation.pullbackSectionHom u q ≫ C.hom) hβ
    _ = SchemeLineSectionEvaluation.pullbackSectionHom (u ≫ μ) α := pullbackSection_compIso μ u α
    _ = β' ≫ i' := hβ'.symm

open Alterations.Geometry.ProjectiveIdeal MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

/-- The canonical whole open target comparison carries the pullback of the
same original homogeneous-form lift to that very form lifted along the composite.
Its entire included section identity is derived, never assumed. -/
theorem liftedFormSection_openNaturality {R : Type u} [CommRing R] {n : ℕ}
    {X Z W : Scheme.{u}} (μ : Z ⟶ X) (u : W ⟶ Z) [IsOpenImmersion u]
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    @CategoryStruct.comp W.Modules _ (Scheme.Modules.unitObj W)
      ((Scheme.Modules.pullback u).obj
        (Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules))
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback (u ≫ μ)).obj M)
        (D.comap (u ≫ μ)).toModules)
      (SchemeLineSectionEvaluation.pullbackSectionHom u (liftedFormSection μ j J d F hF hFJ))
        (openIdealTensorCompIso μ u M D).hom =
      liftedFormSection (u ≫ μ) j J d F hF hFJ := by
  let M := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let α := SchemeLineSectionEvaluation.pullbackSectionHom j
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)
  have hM : Scheme.Modules.IsInvertible M :=
    (coordinateHyperplanePoleSheafPower_isInvertible (R := R) (0 : Fin (n+1)) d).pullback j
  exact openLift_eq μ u M hM D α (liftedFormSection μ j J d F hF hFJ)
    (liftedFormSection (u ≫ μ) j J d F hF hFJ)
    (liftedFormSection_inclusion μ j J d F hF hFJ)
    (liftedFormSection_inclusion (u ≫ μ) j J d F hF hFJ)

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
