/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import EnvelopeProperty.AlgGeom.CartierRatioPullback
import EnvelopeProperty.AlgGeom.CartierPullbackTensorCoherence

/-! # Composition of the actual canonical explicit tensor pullback -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace ModularCurves
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The actual coherent/explicit tensor comparison is natural. Its proof
reuses the exact native sheafification tensorator/counit argument. -/
private theorem cartierMonoidalTensorObjIso_inv_natural
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) ≫
        (monoidalTensorObjIso M' N').inv =
      (monoidalTensorObjIso M N).inv ≫ (f ⊗ₘ g) := by
  let : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  let : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let sh (A : X.PresheafOfModules) : X.Modules := L.obj A
  let δ (A B : X.PresheafOfModules) : sh (A ⊗ B) ⟶ sh A ⊗ sh B :=
    Functor.OplaxMonoidal.δ F A B
  let ε (A : X.Modules) : sh A.val ⟶ A :=
    (Scheme.Modules.sheafifyValIso A).hom
  have hIso (A B : X.Modules) :
      (monoidalTensorObjIso A B).inv =
        δ A.val B.val ≫ (ε A ⊗ₘ ε B) := by
    rfl
  have hδ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
        δ M.val N.val ≫ (L.map f.val ⊗ₘ L.map g.val) :=
    (Functor.OplaxMonoidal.δ_natural F f.val g.val).symm
  have hεf : L.map f.val ≫ ε M' = ε M ≫ f :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality f
  have hεg : L.map g.val ≫ ε N' = ε N ≫ g :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  let e' : (sh M'.val ⊗ sh N'.val) ⟶ (M' ⊗ N') :=
    ε M' ⊗ₘ ε N'
  let e₀ : (sh M.val ⊗ sh N.val) ⟶ (M ⊗ N) :=
    ε M ⊗ₘ ε N
  let lfg : (sh M.val ⊗ sh N.val) ⟶ (sh M'.val ⊗ sh N'.val) :=
    L.map f.val ⊗ₘ L.map g.val
  let fg : (M ⊗ N) ⟶ (M' ⊗ N') := f ⊗ₘ g
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
    δ M.val N.val ≫ lfg at hδ
  have hTensorComp : lfg ≫ e' = e₀ ≫ fg := by
    let c₁ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (L.map f.val ≫ ε M') ⊗ₘ (L.map g.val ≫ ε N')
    let c₀ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (ε M ≫ f) ⊗ₘ (ε N ≫ g)
    have hleft : lfg ≫ e' = c₁ := by
      dsimp only [lfg, e', c₁]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    have hmiddle : c₁ = c₀ := by
      dsimp only [c₁, c₀]
      exact congrArg₂
        (fun (a : sh M.val ⟶ M') (b : sh N.val ⟶ N') ↦ a ⊗ₘ b)
        hεf hεg
    have hright : e₀ ≫ fg = c₀ := by
      dsimp only [e₀, fg, c₀]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    exact hleft.trans (hmiddle.trans hright.symm)
  rw [hIso M' N', hIso M N]
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
    δ M.val N.val ≫ e₀ ≫ fg
  have h₁ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
        (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' =
        (δ M.val N.val ≫ lfg) ≫ e' :=
    congrArg (fun k ↦ k ≫ e') hδ
  have h₃ :
      (δ M.val N.val ≫ lfg) ≫ e' =
        δ M.val N.val ≫ (lfg ≫ e') :=
    Category.assoc _ _ _
  have h₄ :
      δ M.val N.val ≫ (lfg ≫ e') =
        δ M.val N.val ≫ (e₀ ≫ fg) :=
    congrArg (fun k ↦ δ M.val N.val ≫ k) hTensorComp
  have h₅ :
      δ M.val N.val ≫ (e₀ ≫ fg) =
        δ M.val N.val ≫ e₀ ≫ fg :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))


/-- The genuine canonical coherent/explicit tensor identification commutes
with the actual original isomorphisms in BOTH original module factors. -/
theorem cartierMonoidalTensorObjIso_hom_natural
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (e' : N ≅ N') :
    (monoidalTensorObjIso M N).hom ≫ (Scheme.Modules.tensorObjCongr e e').hom =
      (e.hom ⊗ₘ e'.hom) ≫ (monoidalTensorObjIso M' N').hom := by
  apply (cancel_epi (monoidalTensorObjIso M N).inv).mp
  apply (cancel_mono (monoidalTensorObjIso M' N').inv).mp
  have h := cartierMonoidalTensorObjIso_inv_natural e.hom e'.hom
  change (Scheme.Modules.tensorObjCongr e e').hom ≫ (monoidalTensorObjIso M' N').inv =
    (monoidalTensorObjIso M N).inv ≫ (e.hom ⊗ₘ e'.hom) at h
  simpa only [Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using h

end ModularCurves

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}}

/-- Canonical whole explicit sheafified tensor pullback commutes with the
TRUE native composition isomorphisms on both original module factors. -/
theorem canonicalTensorPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (pullback f).mapIso (canonicalTensorPullbackIso g M N) ≪≫
        canonicalTensorPullbackIso f ((pullback g).obj M) ((pullback g).obj N) ≪≫
        tensorObjCongr ((pullbackComp f g).app M) ((pullbackComp f g).app N) =
      (pullbackComp f g).app (tensorObj M N) ≪≫
        canonicalTensorPullbackIso (f ≫ g) M N := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  let : MonoidalCategory Y.Modules := monoidalCategory Y
  let : MonoidalCategory Z.Modules := monoidalCategory Z
  let : (pullback f).Monoidal := pullbackMonoidal f
  let : (pullback g).Monoidal := pullbackMonoidal g
  let : (pullback (f ≫ g)).Monoidal := pullbackMonoidal (f ≫ g)
  let kz := ModularCurves.monoidalTensorObjIso M N
  let kx := ModularCurves.monoidalTensorObjIso
    ((pullback f).obj ((pullback g).obj M)) ((pullback f).obj ((pullback g).obj N))
  let kfg := ModularCurves.monoidalTensorObjIso
    ((pullback (f ≫ g)).obj M) ((pullback (f ≫ g)).obj N)
  let dg := Functor.Monoidal.μIso (pullback g) M N
  let df := Functor.Monoidal.μIso (pullback f) ((pullback g).obj M) ((pullback g).obj N)
  let dfg := Functor.Monoidal.μIso (pullback (f ≫ g)) M N
  let cM := (pullbackComp f g).app M
  let cN := (pullbackComp f g).app N
  have hk : kx ≪≫ tensorObjCongr cM cN = (cM ⊗ᵢ cN) ≪≫ kfg := by
    apply Iso.ext
    exact ModularCurves.cartierMonoidalTensorObjIso_hom_natural cM cN
  have hd : (pullback f).mapIso dg.symm ≪≫ df.symm ≪≫ (cM ⊗ᵢ cN) =
      (pullbackComp f g).app (M ⊗ N) ≪≫ dfg.symm := by
    apply Iso.ext
    exact pullbackComp_inverse_tensorator f g M N
  have hc : (pullback f).mapIso ((pullback g).mapIso kz.symm) ≪≫
      (pullbackComp f g).app (M ⊗ N) =
      (pullbackComp f g).app (tensorObj M N) ≪≫
        (pullback (f ≫ g)).mapIso kz.symm := by
    apply Iso.ext
    exact (pullbackComp f g).hom.naturality kz.inv
  calc
    _ = (pullback f).mapIso ((pullback g).mapIso kz.symm) ≪≫
        (pullback f).mapIso dg.symm ≪≫ df.symm ≪≫ kx ≪≫ tensorObjCongr cM cN := by
      simp only [canonicalTensorPullbackIso, kz, kx, dg, df, cM, cN,
        Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
        Iso.self_symm_id_assoc]
    _ = (pullback f).mapIso ((pullback g).mapIso kz.symm) ≪≫
        ((pullback f).mapIso dg.symm ≪≫ df.symm ≪≫ (cM ⊗ᵢ cN)) ≪≫ kfg := by
      rw [hk]
      simp only [Iso.trans_assoc]
    _ = (pullback f).mapIso ((pullback g).mapIso kz.symm) ≪≫
        (pullbackComp f g).app (M ⊗ N) ≪≫ dfg.symm ≪≫ kfg := by
      rw [hd]
      simp only [Iso.trans_assoc]
    _ = (pullbackComp f g).app (tensorObj M N) ≪≫
        (pullback (f ≫ g)).mapIso kz.symm ≪≫ dfg.symm ≪≫ kfg := by
      rw [← Iso.trans_assoc, hc]
      simp only [Iso.trans_assoc]
    _ = _ := rfl

end AlgebraicGeometry.Scheme.Modules
