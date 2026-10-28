import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import ModularCurves.Picard.PullbackTensorObj

/-! # Actual original section division on the genuine denominator basic open -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeSectionTensorDivision
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f
variable {X : Scheme.{u}} {M T : X.Modules}

private def rightUnit (M : X.Modules) : M ⊗ unitObj X ≅ M :=
  (Iso.refl M ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ M

/-- The actual right tensor of two whole section maps, through the native unit isomorphism. -/
def tensorRight (s : unitObj X ⟶ M) (β : unitObj X ⟶ T) : unitObj X ⟶ M ⊗ T :=
  s ≫ (rightUnit M).inv ≫ (𝟙 M ⊗ₘ β)

/-- Actual contraction with the inverse of the same whole denominator section. -/
def divide (α : unitObj X ⟶ M ⊗ T) (b : unitObj X ≅ T) : unitObj X ⟶ M :=
  α ≫ (𝟙 M ⊗ₘ b.inv) ≫ (rightUnit M).hom

/-- The entire actual ratio multiplied by its own denominator is the original numerator. -/
theorem tensorRight_divide (α : unitObj X ⟶ M ⊗ T) (b : unitObj X ≅ T) :
    tensorRight (divide α b) b.hom = α := by
  simp [tensorRight,divide,MonoidalCategory.tensorHom_def]

/-- Actual denominator contraction recovers the same whole original section. -/
theorem divide_tensorRight (s : unitObj X ⟶ M) (b : unitObj X ≅ T) :
    divide (tensorRight s b.hom) b = s := by
  simp [tensorRight,divide,MonoidalCategory.tensorHom_def,← whiskerLeft_comp_assoc]

/-- The actual original ratio, defined on the genuine basic open of the same denominator coefficient. -/
def basicRatio (eT : T ≅ unitObj X) (α : unitObj X ⟶ M ⊗ T)
    (β : unitObj X ⟶ T) :
    unitObj (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).toScheme ⟶
      (pullback (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).ι).obj M :=
  let i := (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).ι
  letI := SchemeLineSectionUnitFrames.basicOpenSection_isIso eT β
  divide (SchemeLineSectionEvaluation.pullbackSectionHom i α ≫
    (Functor.Monoidal.μIso (pullback i) M T).inv)
    (asIso (SchemeLineSectionEvaluation.pullbackSectionHom i β))

/-- Actual whole tensor identity on the original denominator basic open. -/
theorem basicRatio_tensor (eT : T ≅ unitObj X) (α : unitObj X ⟶ M ⊗ T)
    (β : unitObj X ⟶ T) :
    let i := (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).ι
    tensorRight (basicRatio eT α β) (SchemeLineSectionEvaluation.pullbackSectionHom i β) =
      SchemeLineSectionEvaluation.pullbackSectionHom i α ≫
        (Functor.Monoidal.μIso (pullback i) M T).inv := by
  let i := (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).ι
  let := SchemeLineSectionUnitFrames.basicOpenSection_isIso eT β
  exact tensorRight_divide _ (asIso (SchemeLineSectionEvaluation.pullbackSectionHom i β))

/-- The actual numerator is the tensor of the actual ratio and denominator through the true native tensorator. -/
theorem basicRatio_tensor_original (eT : T ≅ unitObj X) (α : unitObj X ⟶ M ⊗ T)
    (β : unitObj X ⟶ T) :
    let i := (X.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT β)).ι
    tensorRight (basicRatio eT α β) (SchemeLineSectionEvaluation.pullbackSectionHom i β) ≫
        (Functor.Monoidal.μIso (pullback i) M T).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom i α := by
  dsimp only
  rw [basicRatio_tensor,Category.assoc,Iso.inv_hom_id,Category.comp_id]

private theorem rightUnit_unit : rightUnit (unitObj X) = ModularCurves.unitObjTensorIso X := by
  apply Iso.ext
  simp only [rightUnit,ModularCurves.unitObjTensorIso,Iso.trans_hom,tensorIso_hom,
    Iso.refl_hom,Iso.symm_hom]
  simp [MonoidalCategory.tensorHom_def',Category.assoc,unitors_equal]

private theorem rightUnit_naturality {P Q : X.Modules} (s : P ⟶ Q) :
    (s ⊗ₘ 𝟙 (unitObj X)) ≫ (rightUnit Q).hom = (rightUnit P).hom ≫ s := by
  simp only [rightUnit,Iso.trans_hom,tensorIso_hom,Iso.refl_hom,Iso.symm_hom,
    MonoidalCategory.tensorHom_def,whiskerLeft_id,id_whiskerRight,Category.id_comp,Category.comp_id,Category.assoc]
  rw [← whisker_exchange_assoc,rightUnitor_naturality]

private theorem unit_hom_ext {P : X.Modules} {a b : unitObj X ⟶ P}
    (h : SchemeLineSectionEvaluation.sectionAtOne a = SchemeLineSectionEvaluation.sectionAtOne b) : a = b := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (1 : Γ(X,⊤))
  have hb := PresheafOfModules.naturality_apply b.val i (1 : Γ(X,⊤))
  change a.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i
    (SchemeLineSectionEvaluation.sectionAtOne a) at ha
  change b.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i
    (SchemeLineSectionEvaluation.sectionAtOne b) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun q => P.presheaf.map i q) h).trans hb.symm)

/-- The actual tensor section map evaluates to the actual native pure tensor, with no section matching premise. -/
theorem sectionAtOne_tensorRight (s : unitObj X ⟶ M) (β : unitObj X ⟶ T) :
    SchemeLineSectionEvaluation.sectionAtOne (tensorRight s β) =
      ModularCurves.tensorSection M T ⊤
        (SchemeLineSectionEvaluation.sectionAtOne s) (SchemeLineSectionEvaluation.sectionAtOne β) := by
  have hs : s ≫ (rightUnit M).inv =
      (rightUnit (unitObj X)).inv ≫ (s ⊗ₘ 𝟙 (unitObj X)) := by
    apply (cancel_mono (rightUnit M).hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [rightUnit_naturality, Iso.inv_hom_id_assoc]
  have ht : tensorRight s β = (ModularCurves.unitObjTensorIso X).inv ≫ (s ⊗ₘ β) := by
    rw [tensorRight,← Category.assoc,hs,rightUnit_unit,Category.assoc,tensorHom_comp_tensorHom]
    simp
  rw [ht]
  have h := ModularCurves.topSectionHom_tensorSection M T
    (SchemeLineSectionEvaluation.sectionAtOne s) (SchemeLineSectionEvaluation.sectionAtOne β)
  have hs' : Scheme.Modules.topSectionHom M (SchemeLineSectionEvaluation.sectionAtOne s) = s := by
    apply unit_hom_ext
    exact Scheme.Modules.topSectionHom_app_top_apply_one M _
  have hβ' : Scheme.Modules.topSectionHom T (SchemeLineSectionEvaluation.sectionAtOne β) = β := by
    apply unit_hom_ext
    exact Scheme.Modules.topSectionHom_app_top_apply_one T _
  rw [hs',hβ'] at h
  exact (congrArg SchemeLineSectionEvaluation.sectionAtOne h).symm.trans
    (Scheme.Modules.topSectionHom_app_top_apply_one (M ⊗ T) _)

end EnvelopeProperty.SchemeSectionTensorDivision
