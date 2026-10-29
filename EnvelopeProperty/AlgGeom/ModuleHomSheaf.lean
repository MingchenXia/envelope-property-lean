/-
Copyright (c) 2026 The AINTLIB contributors and Envelope Property contributors.
Released under Apache 2.0 license as described in the file LICENSE.
The scalar-linearity descent argument adapts the selected native AINTLIB
Picard/Dual.lean proof to arbitrary original target module sheaves.
-/
import ModularCurves.Picard.Dual

/-! # The genuine sheaf of local morphisms between original module sheaves -/

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u
namespace EnvelopeProperty.ModuleHomSheaf
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})

/-- The existing additive sheaf Hom of the actual original underlying module sheaves. -/
def ambientHom (M N : _root_.SheafOfModules.{u} R) :=
  CategoryTheory.sheafHom ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj N)

/-- Forget scalar multiplication from the same original local module morphism. -/
def toAmbient (M N : _root_.SheafOfModules.{u} R) (U : C) :
    (M.over U ⟶ N.over U) → (ambientHom R M N).obj.obj (op U) :=
  fun α => (_root_.SheafOfModules.toSheaf (R.over U)).map α

/-- Forgetting scalar multiplication retains every original local module morphism injectively. -/
theorem toAmbient_injective (M N : _root_.SheafOfModules.{u} R) (U : C) :
    Function.Injective (toAmbient R M N U) :=
  fun _ _ h => (_root_.SheafOfModules.toSheaf (R.over U)).map_injective h

/-- The true original local module morphism restricts by the actual over-site functor. -/
def restrictHom (M N : _root_.SheafOfModules.{u} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ N.over U.unop) : M.over V.unop ⟶ N.over V.unop :=
  (_root_.SheafOfModules.overFunctorMap R f.unop).inv.app M ≫
    (_root_.SheafOfModules.overMap R f.unop).map α ≫
    (_root_.SheafOfModules.overFunctorMap R f.unop).hom.app N

/-- The actual original additive and module restrictions give the same whole local morphism. -/
theorem ambientHom_map_toAmbient (M N : _root_.SheafOfModules.{u} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (α : M.over U.unop ⟶ N.over U.unop) :
    (ambientHom R M N).obj.map f (toAmbient R M N U.unop α) =
      toAmbient R M N V.unop (restrictHom R M N f α) := rfl

/-- The genuine original module-linear morphisms inside the original additive sheaf Hom. -/
def homSubfunctor (M N : _root_.SheafOfModules.{u} R) :
    Subfunctor (ambientHom R M N).obj where
  obj U := Set.range (toAmbient R M N U.unop)
  map f _ := by
    rintro ⟨α, rfl⟩
    exact ⟨restrictHom R M N f α, ambientHom_map_toAmbient R M N f α⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem hom_app_smul (M N : _root_.SheafOfModules.{u} R) {U : Cᵒᵖ}
    (s : (ambientHom R M N).obj.obj U)
    (hs : (homSubfunctor R M N).sieveOfSection s ∈ J U.unop)
    (V : (Over U.unop)ᵒᵖ) (r : (R.over U.unop).obj.obj V)
    (m : (M.over U.unop).val.obj V) :
    s.hom.app V (r • m) =
      r • (show (N.over U.unop).val.obj V from
        s.hom.app V m) := by
  let T : Sieve V.unop :=
    (Sieve.overEquiv V.unop).symm
      (Sieve.pullback (V.unop.hom) ((homSubfunctor R M N).sieveOfSection s))
  have hT : T ∈ (J.over U.unop) V.unop :=
    J.overEquiv_symm_mem_over V.unop _ (J.pullback_stable (V.unop.hom) hs)
  apply (N.over U.unop).isSheaf.isSeparated
    V.unop T hT
  intro W i hi
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) (r • m)]
  change s.hom.app (op W)
      ((M.over U.unop).val.map i.op (r • m)) =
    (N.over U.unop).val.map i.op
      (r • (show (N.over U.unop).val.obj V from
        s.hom.app V m))
  rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul]
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) m]
  have hi' :
      (Sieve.pullback (V.unop.hom)
        ((homSubfunctor R M N).sieveOfSection s)) i.left :=
    (Sieve.overEquiv_symm_iff _ i).mp hi
  change (ambientHom R M N).obj.map (i.left ≫ V.unop.hom).op s ∈
    (homSubfunctor R M N).obj (op W.left) at hi'
  rcases hi' with ⟨β, hβ⟩
  change s.hom.app (op W)
      ((R.over U.unop).obj.map i.op r • (M.over U.unop).val.map i.op m) =
    (R.over U.unop).obj.map i.op r •
      (show (N.over U.unop).val.obj (op W) from
        s.hom.app (op W) ((M.over U.unop).val.map i.op m))
  rw [Over.w i] at hβ
  have hβ_app := congr_arg
    (fun q => q.hom.app (op (Over.mk (𝟙 W.left)))) hβ
  let r' : (R.over W.left).obj.obj (op (Over.mk (𝟙 W.left))) :=
    (R.over U.unop).obj.map i.op r
  let m' : (M.over W.left).val.obj (op (Over.mk (𝟙 W.left))) :=
    (M.over U.unop).val.map i.op m
  have hβ_smul := CategoryTheory.congr_fun hβ_app (r' • m')
  have hβ_m := CategoryTheory.congr_fun hβ_app m'
  have hleft_smul :
      (toAmbient R M N W.left β).hom.app (op (Over.mk (𝟙 W.left)))
          (r' • m') =
        β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') := rfl
  have hleft_m :
      (toAmbient R M N W.left β).hom.app (op (Over.mk (𝟙 W.left))) m' =
        β.val.app (op (Over.mk (𝟙 W.left))) m' := rfl
  have hright_smul :
      (((ambientHom R M N).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') := rfl
  have hright_m :
      (((ambientHom R M N).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' := rfl
  have hβ_canon_smul :
      β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') :=
    hleft_smul.symm.trans (hβ_smul.trans hright_smul)
  have hβ_canon_m :
      β.val.app (op (Over.mk (𝟙 W.left))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' :=
    hleft_m.symm.trans (hβ_m.trans hright_m)
  let e : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ≅ W :=
    Over.isoMk (Iso.refl _) (by rfl)
  have hs_canon_smul :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') = s.hom.app (op W) (r' • m') := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) (r' • m')
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op
          (r' • m')) =
      ((_root_.SheafOfModules.toSheaf R).obj
          N).obj.map (𝟙 W.left).op
        (s.hom.app (op W) (r' • m')) at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        N).obj.map_id] at h
    simpa only [AddCommGrpCat.id_apply] using h
  have hs_canon_m :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op W) m' := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) m'
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op m') =
      ((_root_.SheafOfModules.toSheaf R).obj
          N).obj.map (𝟙 W.left).op
        (s.hom.app (op W) m') at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        N).obj.map_id] at h
    simpa only [AddCommGrpCat.id_apply] using h
  change s.hom.app (op W) (r' • m') =
    r' • (show (N.over W.left).val.obj
      (op (Over.mk (𝟙 W.left))) from s.hom.app (op W) m')
  rw [← hs_canon_smul, ← hs_canon_m, ← hβ_canon_smul, ← hβ_canon_m]
  exact (β.val.app (op (Over.mk (𝟙 W.left)))).hom.map_smul r' m'

/-- Module-linearity of a local functional descends along covering sieves. -/
theorem homSubfunctor_isSheaf (M N : _root_.SheafOfModules.{u} R) :
    Presieve.IsSheaf J (homSubfunctor R M N).toFunctor := by
  apply ((homSubfunctor R M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J (ambientHom R M N).obj).mp
      (ambientHom R M N).property)).2
  intro U s hs
  let α : M.over U.unop ⟶ N.over U.unop :=
    { val := PresheafOfModules.homMk s.hom (hom_app_smul R M N s hs) }
  exact ⟨α, rfl⟩

/-- The actual original local-module-morphism sheaf, not a supplied gluing certificate. -/
def localHomSheaf (M N : _root_.SheafOfModules.{u} R) : Sheaf J (Type u) :=
  ⟨(homSubfunctor R M N).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).mpr (homSubfunctor_isSheaf R M N)⟩

/-- Every section of the derived local Hom sheaf is the same entire original module morphism. -/
def localHomEquiv (M N : _root_.SheafOfModules.{u} R) (U : C) :
    (M.over U ⟶ N.over U) ≃ (localHomSheaf R M N).obj.obj (op U) where
  toFun α := ⟨toAmbient R M N U α, ⟨α, rfl⟩⟩
  invFun x := x.2.choose
  left_inv α := by
    apply toAmbient_injective R M N U
    exact (Set.mem_range.mp (show toAmbient R M N U α ∈
      Set.range (toAmbient R M N U) from ⟨α, rfl⟩)).choose_spec
  right_inv x := Subtype.ext x.2.choose_spec

end EnvelopeProperty.ModuleHomSheaf
