/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierCanonicalTensorPullback

/-! # Naturality of the actual whole explicit tensor pullback comparison -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
noncomputable local instance cartierTensorNaturalityMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  monoidalCategory X
noncomputable local instance cartierTensorNaturalityPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Modules.pullback f).Monoidal := pullbackMonoidal f
variable {X Y : Scheme.{u}}

/-- The genuine canonical whole explicit tensor pullback is natural in
both original module isomorphisms, using the actual native tensorator. -/
theorem canonicalTensorPullbackIso_natural (f : X ⟶ Y)
    {M M' N N' : Y.Modules} (e : M ≅ M') (e' : N ≅ N') :
    (Modules.pullback f).mapIso (tensorObjCongr e e') ≪≫
        canonicalTensorPullbackIso f M' N' =
      canonicalTensorPullbackIso f M N ≪≫
        tensorObjCongr ((Modules.pullback f).mapIso e) ((Modules.pullback f).mapIso e') := by
  let k := ModularCurves.monoidalTensorObjIso M N
  let k' := ModularCurves.monoidalTensorObjIso M' N'
  let kx := ModularCurves.monoidalTensorObjIso
    ((Modules.pullback f).obj M) ((Modules.pullback f).obj N)
  let kx' := ModularCurves.monoidalTensorObjIso
    ((Modules.pullback f).obj M') ((Modules.pullback f).obj N')
  let μ := Functor.Monoidal.μIso (Modules.pullback f) M N
  let μ' := Functor.Monoidal.μIso (Modules.pullback f) M' N'
  have hs : tensorObjCongr e e' ≪≫ k'.symm = k.symm ≪≫ (e ⊗ᵢ e') := by
    apply Iso.ext
    apply (cancel_epi k.hom).mp
    apply (cancel_mono k'.hom).mp
    have hk := ModularCurves.cartierMonoidalTensorObjIso_hom_natural e e'
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc, tensorIso_hom, k, k'] using hk
  have ht : (Modules.pullback f).mapIso (e ⊗ᵢ e') ≪≫ μ'.symm =
      μ.symm ≪≫ ((Modules.pullback f).mapIso e ⊗ᵢ (Modules.pullback f).mapIso e') := by
    apply Iso.ext
    exact (Functor.OplaxMonoidal.δ_natural (Modules.pullback f) e.hom e'.hom).symm
  have hx : ((Modules.pullback f).mapIso e ⊗ᵢ (Modules.pullback f).mapIso e') ≪≫ kx' =
      kx ≪≫ tensorObjCongr ((Modules.pullback f).mapIso e) ((Modules.pullback f).mapIso e') := by
    apply Iso.ext
    exact (ModularCurves.cartierMonoidalTensorObjIso_hom_natural
      ((Modules.pullback f).mapIso e) ((Modules.pullback f).mapIso e')).symm
  change (Modules.pullback f).mapIso (tensorObjCongr e e') ≪≫
      (Modules.pullback f).mapIso k'.symm ≪≫ μ'.symm ≪≫ kx' =
    ((Modules.pullback f).mapIso k.symm ≪≫ μ.symm ≪≫ kx) ≪≫
      tensorObjCongr ((Modules.pullback f).mapIso e) ((Modules.pullback f).mapIso e')
  rw [← Iso.trans_assoc, ← Functor.mapIso_trans, hs, Functor.mapIso_trans]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc ((Modules.pullback f).mapIso (e ⊗ᵢ e')), ht]
  simp only [Iso.trans_assoc]
  rw [hx]

end AlgebraicGeometry.Scheme.Modules
