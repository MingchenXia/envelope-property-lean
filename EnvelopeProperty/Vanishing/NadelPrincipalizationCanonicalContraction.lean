import EnvelopeProperty.Char0.CanonicalDifferentialSection
import EnvelopeProperty.AlgGeom.SchemeTensorIdealShuffle

/-! # Actual canonical tensor-dual contraction retaining whole original maps -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationCanonicalContraction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A) (B : X.Modules)

/-- Genuine evaluation/counit cancels the SAME original line's actual dual. -/
def contractionIso : Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B (dualObj A)) A ≅ B :=
  (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B (dualObj A)) A).symm ≪≫
    ((ModularCurves.monoidalTensorObjIso B (dualObj A)).symm ⊗ᵢ Iso.refl A) ≪≫
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).counitIso.app B

/-- The SAME actual structural-unit tensor comparison. -/
def unitTensorIso : Scheme.Modules.tensorObj (unitObj X) A ≅ A :=
  (ModularCurves.monoidalTensorObjIso (unitObj X) A).symm ≪≫
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl A) ≪≫ λ_ A

/-- Cancellation recovers the ENTIRE original map from its actual Hom section. -/
theorem contractionIso_section (φ : A ⟶ B) :
    SchemeTensorObjMorphisms.tensorObjMap (SchemeInvertibleHomSection.equiv A hA B φ) (𝟙 A) ≫
      (contractionIso A hA B).hom = (unitTensorIso A).hom ≫ φ := by
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA
  let s := E.toAdjunction.homEquiv (𝟙_ X.Modules) B ((λ_ A).hom ≫ φ)
  have hrec : (s ▷ A) ≫ E.counitIso.hom.app B = (λ_ A).hom ≫ φ := by
    have hr := (E.toAdjunction.homEquiv (𝟙_ X.Modules) B).symm_apply_apply ((λ_ A).hom ≫ φ)
    rw [Adjunction.homEquiv_counit] at hr
    exact hr
  dsimp only [contractionIso, unitTensorIso]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
    Category.assoc]
  rw [← Category.assoc (SchemeTensorObjMorphisms.tensorObjMap
    (SchemeInvertibleHomSection.equiv A hA B φ) (𝟙 A))
      (ModularCurves.monoidalTensorObjIso (Scheme.Modules.tensorObj B (dualObj A)) A).inv,
    SchemeTensorObjMorphisms.tensorObjMap_monoidal]
  simp only [tensorHom_id, Category.assoc]
  change (ModularCurves.monoidalTensorObjIso (unitObj X) A).inv ≫
      (SchemeInvertibleHomSection.equiv A hA B φ) ▷ A ≫
      (ModularCurves.monoidalTensorObjIso B (dualObj A)).inv ▷ A ≫
      E.counitIso.hom.app B = _
  rw [← comp_whiskerRight_assoc]
  have hs : SchemeInvertibleHomSection.equiv A hA B φ ≫
      (ModularCurves.monoidalTensorObjIso B (dualObj A)).inv =
      (ModularCurves.monoidalUnitObjIso X).inv ≫ s := by
    change ((ModularCurves.monoidalUnitObjIso X).inv ≫ s ≫
      (ModularCurves.monoidalTensorObjIso B (dualObj A)).hom) ≫ _ = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hs, comp_whiskerRight, Category.assoc, hrec]

private theorem tensorIdeal_left {X : Scheme.{u}} {B B' : X.Modules}
    (a : B ⟶ B') (I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) :
    SchemeTensorObjMorphisms.tensorObjMap a (𝟙 I) ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap B' I i =
    SchemeTensorObjMorphisms.tensorObjIdealMap B I i ≫ a := by
  let e := ModularCurves.monoidalTensorObjIso B I
  let e' := ModularCurves.monoidalTensorObjIso B' I
  have hm := SchemeTensorObjMorphisms.tensorObjMap_monoidal a (𝟙 I)
  have ht : e.hom ≫ SchemeTensorObjMorphisms.tensorObjMap a (𝟙 I) =
      (a ▷ I) ≫ e'.hom := by
    apply (cancel_mono e'.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hm]
    change e.hom ≫ e.inv ≫ (a ⊗ₘ 𝟙 I) = a ▷ I
    simp only [Iso.hom_inv_id_assoc, MonoidalCategory.tensorHom_id]
  apply (cancel_epi e.hom).mp
  have he := SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I i
  change e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I i = _ at he
  change e.hom ≫ _ = e.hom ≫ _ ≫ a
  rw [← Category.assoc, ht, Category.assoc,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← Category.assoc e.hom (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) a, he]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

/-- The actual rounded tensor uses the SAME native ideal shuffle and original evaluation. -/
def roundedContractionIso (I : X.Modules) :
    Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B (dualObj A)) I) A ≅ Scheme.Modules.tensorObj B I :=
  SchemeTensorObjMorphisms.tensorObjIdealShuffleIso (Scheme.Modules.tensorObj B (dualObj A)) I A ≪≫
    tensorObjCongr (contractionIso A hA B) (Iso.refl I)

/-- Contraction retains the ENTIRE original rounded ideal inclusion. -/
theorem roundedContractionIso_inclusion (I : X.Modules) (i : I ⟶ unitObj X) :
    (roundedContractionIso A hA B I).hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I i =
      SchemeTensorObjMorphisms.tensorObjMap
        (SchemeTensorObjMorphisms.tensorObjIdealMap (Scheme.Modules.tensorObj B (dualObj A)) I i) (𝟙 A) ≫
        (contractionIso A hA B).hom := by
  dsimp only [roundedContractionIso]
  simp only [Iso.trans_hom, Category.assoc]
  change (SchemeTensorObjMorphisms.tensorObjIdealShuffleIso (Scheme.Modules.tensorObj B (dualObj A)) I A).hom ≫
    SchemeTensorObjMorphisms.tensorObjMap (contractionIso A hA B).hom (𝟙 I) ≫ _ = _
  rw [tensorIdeal_left]
  rw [← Category.assoc, ← SchemeTensorObjMorphisms.tensorObjIdealShuffleIso_inclusion]

end EnvelopeProperty.Vanishing.NadelPrincipalizationCanonicalContraction
