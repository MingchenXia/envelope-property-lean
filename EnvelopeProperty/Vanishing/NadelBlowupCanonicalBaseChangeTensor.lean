import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleModel
import EnvelopeProperty.AlgGeom.CartierModuleFlatPullback

/-! # Whole Cartier tensor inclusion under the actual original flat base change -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem tensorIdeal_comp {X : Scheme.{u}} (B : X.Modules) {I J : X.Modules}
    (a : I ⟶ J) (j : J ⟶ unitObj X) :
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B J j =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I (a ≫ j) := by
  let eI := ModularCurves.monoidalTensorObjIso B I
  let eJ := ModularCurves.monoidalTensorObjIso B J
  have hMap := SchemeTensorObjMorphisms.tensorObjMap_monoidal (𝟙 B) a
  have ht : eI.hom ≫ SchemeTensorObjMorphisms.tensorObjMap (𝟙 B) a = B ◁ a ≫ eJ.hom := by
    apply (cancel_mono eJ.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      MonoidalCategory.id_tensorHom]
  apply (cancel_epi eI.hom).mp
  rw [← Category.assoc, ht, Category.assoc,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B J j,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I (a ≫ j)]
  simp only [← whiskerLeft_comp_assoc, Category.assoc]

/-- Actual flatness and actual Cartier invertibility produce the whole
native tensor/ideal-comap comparison, without a supplied module comparison. -/
def flatCartierTensorIso {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q]
    (B : X.Modules) (J : X.IdealSheafData) (hJ : J.IsInvertible) :
    (pullback q).obj (Scheme.Modules.tensorObj B J.toModules) ≅
      Scheme.Modules.tensorObj ((pullback q).obj B) (J.comap q).toModules :=
  SchemeTensorIdealPullback.tensorObjPullbackIso q B J.toModules ≪≫
    tensorObjCongr (Iso.refl _) (hJ.flatPullbackModuleIso q)

/-- The actual native flat Cartier tensor comparison retains the ENTIRE
same original tensor-ideal inclusion, not just its affine sections. -/
theorem flatCartierTensorIso_inclusion {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q]
    (B : X.Modules) (J : X.IdealSheafData) (hJ : J.IsInvertible) :
    (flatCartierTensorIso q B J hJ).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap _ _ (J.comap q).toModulesInclusion =
      (pullback q).map (SchemeTensorObjMorphisms.tensorObjIdealMap B _ J.toModulesInclusion) := by
  let F := pullback q
  let e := hJ.flatPullbackModuleIso q
  have h : e.hom ≫ (J.comap q).toModulesInclusion =
      F.map J.toModulesInclusion ≫ (pullbackUnitIso q).hom :=
    J.toModulesComapPullbackMap_inclusion q
  change (SchemeTensorIdealPullback.tensorObjPullbackIso q B J.toModules).hom ≫
    SchemeTensorObjMorphisms.tensorObjMap (𝟙 (F.obj B)) e.hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap (F.obj B) (J.comap q).toModules
        (J.comap q).toModulesInclusion = _
  rw [tensorIdeal_comp, h]
  exact (SchemeTensorIdealPullback.tensorObjIdealMap_pullback q B J.toModules J.toModulesInclusion).symm

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeTensor
