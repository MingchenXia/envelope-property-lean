/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierRatioSheaves

/-! # Whole explicit tensor and true sheaf-dual isomorphism functoriality -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- The actual sheafified tensor comparison preserves both identity isomorphisms. -/
theorem tensorObjCongr_refl (M N : X.Modules) :
    tensorObjCongr (Iso.refl M) (Iso.refl N) = Iso.refl (tensorObj M N) := by
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = 𝟙 _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

/-- The actual whole tensor comparison preserves simultaneous original composition. -/
theorem tensorObjCongr_trans {M N P M' N' P' : X.Modules}
    (e : M ≅ N) (f : N ≅ P) (e' : M' ≅ N') (f' : N' ≅ P') :
    tensorObjCongr (e ≪≫ f) (e' ≪≫ f') =
      tensorObjCongr e e' ≪≫ tensorObjCongr f f' := by
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      ((e.hom.val ≫ f.hom.val) ⊗ₘ (e'.hom.val ≫ f'.hom.val)) =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (e.hom.val ⊗ₘ e'.hom.val) ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (f.hom.val ⊗ₘ f'.hom.val)
  rw [← tensorHom_comp_tensorHom, Functor.map_comp]

/-- The actual original sheaf dual preserves the identity isomorphism. -/
theorem dualIsoObj_refl (M : X.Modules) : dualIsoObj (Iso.refl M) = Iso.refl (dualObj M) := by
  have : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b
  apply Iso.ext
  exact ModularCurves.SheafOfModules.dualMap_id X.ringCatSheaf M

/-- The genuine original sheaf dual reverses actual whole isomorphism composition. -/
theorem dualIsoObj_trans {M N P : X.Modules} (e : M ≅ N) (f : N ≅ P) :
    dualIsoObj (e ≪≫ f) = dualIsoObj f ≪≫ dualIsoObj e := by
  have : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b
  apply Iso.ext
  exact ModularCurves.SheafOfModules.dualMap_comp X.ringCatSheaf e.hom f.hom

end AlgebraicGeometry.Scheme.Modules
