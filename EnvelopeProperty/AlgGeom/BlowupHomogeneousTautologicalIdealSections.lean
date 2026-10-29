import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalIdealSectionCore

/-! # Specified original form lifts and their actual geometric comap -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory HomogeneousLocalization MvPolynomial
open Alterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

private theorem sectionHom_atOne {X : Scheme.{u}} (M : X.Modules)
    (α : Scheme.Modules.unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M (SchemeLineSectionEvaluation.sectionAtOne α) = α := by
  have hone : Scheme.Modules.topSectionHom (Scheme.Modules.unitObj X)
      (1 : Γ(X, ⊤)) = 𝟙 (Scheme.Modules.unitObj X) :=
    ModularCurves.unitEndomorphismOfTopSection_one
  have h := ModularCurves.topSectionHom_comp
    (M := Scheme.Modules.unitObj X) (N := M) (show Γ(X, ⊤) from 1) α
  have hleft : Scheme.Modules.topSectionHom (Scheme.Modules.unitObj X)
      (1 : Γ(X, ⊤)) ≫ α = α :=
    (congrArg (fun k : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X => k ≫ α) hone).trans
      (Category.id_comp α)
  exact h.symm.trans hleft

/-- An original homogeneous form in the original ideal gives an actual whole
section in its true original ideal tensor module. -/
def originalFormIdealSection {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    Scheme.Modules.unitObj X ⟶
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback j).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d))
        ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).toModules :=
  let L := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let I := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  SchemeModuleGlobalSections.sectionHom (Scheme.Modules.tensorObj L I.toModules)
    (exists_originalFormIdealSection j J d F hF hFJ).choose

/-- The entire original tensor-ideal inclusion recovers exactly the SAME
original homogeneous section, with its original scalar actions. -/
theorem originalFormIdealSection_inclusion {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    originalFormIdealSection j J d F hF hFJ ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap
          ((Scheme.Modules.pullback j).obj
            (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d))
          ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).toModules
          ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).toModulesInclusion =
      SchemeLineSectionEvaluation.pullbackSectionHom j
        (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF) := by
  let L := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let I := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let T := Scheme.Modules.tensorObj L I.toModules
  let r : Γ(T, ⊤) := (exists_originalFormIdealSection j J d F hF hFJ).choose
  let f : T ⟶ L := SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion
  let α : Scheme.Modules.unitObj X ⟶ L := SchemeLineSectionEvaluation.pullbackSectionHom j
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)
  have hr : f.val.app (.op ⊤) r = SchemeLineSectionEvaluation.sectionAtOne α :=
    (exists_originalFormIdealSection j J d F hF hFJ).choose_spec
  have hs := ModularCurves.topSectionHom_comp (M := T) (N := L) r f
  exact hs.trans ((congrArg (SchemeModuleGlobalSections.sectionHom L) hr).trans
    (sectionHom_atOne L α))

private noncomputable instance idealSectionsMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

private theorem tensorIdealMap_comp {W : Scheme.{u}}
    (B : W.Modules) {I J : W.Modules} (a : I ⟶ J) (j : J ⟶ Scheme.Modules.unitObj W) :
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B J j =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I (a ≫ j) := by
  let eI := ModularCurves.monoidalTensorObjIso B I
  let eJ := ModularCurves.monoidalTensorObjIso B J
  have hMap := SchemeTensorObjMorphisms.tensorObjMap_monoidal (𝟙 B) a
  have ht : eI.hom ≫ SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a =
      B ◁ a ≫ eJ.hom := by
    apply (cancel_mono eJ.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      MonoidalCategory.id_tensorHom]
  apply (cancel_epi eI.hom).mp
  rw [← Category.assoc, ht, Category.assoc,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B J j,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I (a ≫ j)]
  simp only [← whiskerLeft_comp_assoc, Category.assoc]

private theorem idealTensorComapMap_inclusion {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (L : X.Modules) (I : X.IdealSheafData) :
    (SchemeTensorIdealPullback.tensorObjPullbackIso μ L I.toModules).hom ≫
        SchemeTensorObjMorphisms.tensorObjMap (𝟙 ((Scheme.Modules.pullback μ).obj L))
          (I.toModulesComapPullbackMap μ) ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap _ _ (I.comap μ).toModulesInclusion =
      (Scheme.Modules.pullback μ).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion) := by
  let P := Scheme.Modules.pullback μ
  let N := P.obj L
  let c := SchemeTensorIdealPullback.tensorObjPullbackIso μ L I.toModules
  let a := I.toModulesComapPullbackMap μ
  let j : (I.comap μ).toModules ⟶ Scheme.Modules.unitObj Z := (I.comap μ).toModulesInclusion
  have hi : a ≫ j = P.map I.toModulesInclusion ≫ (Scheme.Modules.pullbackUnitIso μ).hom :=
    I.toModulesComapPullbackMap_inclusion μ
  have hc := tensorIdealMap_comp N a j
  have hn := congrArg (fun k : P.obj I.toModules ⟶ Scheme.Modules.unitObj Z =>
    SchemeTensorObjMorphisms.tensorObjIdealMap N (P.obj I.toModules) k) hi
  have hp := SchemeTensorIdealPullback.tensorObjIdealMap_pullback μ L I.toModules I.toModulesInclusion
  exact (congrArg (fun k => c.hom ≫ k) (hc.trans hn)).trans hp.symm

private theorem pullbackSectionHom_moduleComp {X Z : Scheme.{u}} (μ : Z ⟶ X)
    {M N : X.Modules} (α : Scheme.Modules.unitObj X ⟶ M) (f : M ⟶ N) :
    SchemeLineSectionEvaluation.pullbackSectionHom μ α ≫ (Scheme.Modules.pullback μ).map f =
      SchemeLineSectionEvaluation.pullbackSectionHom μ (α ≫ f) := by
  simp only [SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_comp, Category.assoc]

/-- The same actual form lifts into the geometric ideal comap along every
original morphism, using the true native tensor and canonical ideal map. -/
def liftedFormSection {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    Scheme.Modules.unitObj Z ⟶
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj ((Scheme.Modules.pullback j).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)))
        (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ).toModules :=
  let L := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let I := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  SchemeLineSectionEvaluation.pullbackSectionHom μ (originalFormIdealSection j J d F hF hFJ) ≫
    (SchemeTensorIdealPullback.tensorObjPullbackIso μ L I.toModules).hom ≫
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 ((Scheme.Modules.pullback μ).obj L))
      (I.toModulesComapPullbackMap μ)

/-- The whole included image is the original homogeneous form pulled by the
same two original maps. No flatness or matching certificate is assumed. -/
theorem liftedFormSection_inclusion {X Z : Scheme.{u}} (μ : Z ⟶ X)
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    liftedFormSection μ j J d F hF hFJ ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap
          ((Scheme.Modules.pullback μ).obj ((Scheme.Modules.pullback j).obj
            (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)))
          (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ).toModules
          (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ).toModulesInclusion =
      SchemeLineSectionEvaluation.pullbackSectionHom μ
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) := by
  let L := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let I := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let β := originalFormIdealSection j J d F hF hFJ
  let f := SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion
  have hi := idealTensorComapMap_inclusion μ L I
  have ht : ((SchemeTensorIdealPullback.tensorObjPullbackIso μ L I.toModules).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap (𝟙 _) (I.toModulesComapPullbackMap μ)) ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap _ _ (I.comap μ).toModulesInclusion =
      (Scheme.Modules.pullback μ).map f := (Category.assoc _ _ _).trans hi
  have hs := pullbackSectionHom_moduleComp μ β f
  have hp := congrArg (SchemeLineSectionEvaluation.pullbackSectionHom μ)
    (originalFormIdealSection_inclusion j J d F hF hFJ)
  change ((SchemeLineSectionEvaluation.pullbackSectionHom μ β ≫
      (SchemeTensorIdealPullback.tensorObjPullbackIso μ L I.toModules).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap (𝟙 _) (I.toModulesComapPullbackMap μ)) ≫ _) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => SchemeLineSectionEvaluation.pullbackSectionHom μ β ≫ k) ht).trans
      (hs.trans hp))

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
