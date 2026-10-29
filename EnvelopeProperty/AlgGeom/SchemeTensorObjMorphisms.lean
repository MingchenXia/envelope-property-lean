import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence

/-! # Actual tensor morphisms and original invertible tensor exactness -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeTensorObjMorphisms

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The SAME original explicit sheafified tensor morphism. -/
def tensorObjMap {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    Scheme.Modules.tensorObj M N ⟶ Scheme.Modules.tensorObj M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (a.val ⊗ₘ b.val)

/-- The genuine original tensor comparison is natural on ENTIRE original maps. -/
theorem tensorObjMap_monoidal {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorObjMap a b ≫ (ModularCurves.monoidalTensorObjIso M' N').inv =
      (ModularCurves.monoidalTensorObjIso M N).inv ≫ (a ⊗ₘ b) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := M.val ⊗ N.val) (F := (M' ⊗ N' : X.Modules))).injective
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    let η := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit
    have hn := congr($(η.naturality (a.val ⊗ₘ b.val)).app U |>.hom (x ⊗ₜ y))
    have ht := ModularCurves.tensorSection_map a b U.unop x y
    change (ModularCurves.monoidalTensorObjIso M' N').inv.val.app U
        ((tensorObjMap a b).val.app U ((η.app (M.val ⊗ N.val)).app U (x ⊗ₜ y))) =
      (a ⊗ₘ b).val.app U ((ModularCurves.monoidalTensorObjIso M N).inv.val.app U
        ((η.app (M.val ⊗ N.val)).app U (x ⊗ₜ y)))
    exact (congrArg ((ModularCurves.monoidalTensorObjIso M' N').inv.val.app U) hn.symm).trans
      ht.symm

/-- Tensoring an actual monomorphism by the SAME actual invertible module
retains monicity for the ORIGINAL explicit sheafified tensor map. -/
theorem mono_tensorObjMap_left (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    {M N : X.Modules} (a : M ⟶ N) [Mono a] :
    Mono (tensorObjMap (𝟙 L) a) := by
  let := Scheme.Modules.symmetricCategory X
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let : (tensorLeft L).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (BraidedCategory.tensorLeftIsoTensorRight L).symm
  have hm : Mono (𝟙 L ⊗ₘ a) := by
    rw [MonoidalCategory.id_tensorHom]
    change Mono ((tensorLeft L).map a)
    infer_instance
  have he := tensorObjMap_monoidal (𝟙 L) a
  have heq : tensorObjMap (𝟙 L) a =
      (ModularCurves.monoidalTensorObjIso L M).inv ≫ (𝟙 L ⊗ₘ a) ≫
        (ModularCurves.monoidalTensorObjIso L N).hom :=
    (Iso.comp_inv_eq (ModularCurves.monoidalTensorObjIso L N)).mp he
  rw [heq]
  infer_instance

end
end EnvelopeProperty.SchemeTensorObjMorphisms
