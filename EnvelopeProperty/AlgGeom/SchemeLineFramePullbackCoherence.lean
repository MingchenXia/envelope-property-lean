import EnvelopeProperty.Berkovich.SchemeLineLocalFrames

/-! # Original whole local frame transport through genuine pullback composition -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual original frame transport commutes with the genuine native
pullback-composition comparison on the original module sheaf. -/
theorem frameViaFactor_pullbackComp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hi : i ≫ b = f)
    (g : C ⟶ D) {M : D.Modules}
    (e : (pullback (b ≫ g)).obj M ≅ unitObj B) :
    frameViaFactor i b f hi ((pullbackComp b g).app M ≪≫ e) =
      (pullbackComp f g).app M ≪≫
        frameViaFactor i (b ≫ g) (f ≫ g) (by rw [← Category.assoc,hi]) e := by
  subst f
  have hc : (pullbackComp i b).inv.app ((pullback g).obj M) ≫
      (pullback i).map ((pullbackComp b g).hom.app M) =
        (pullbackComp (i ≫ b) g).hom.app M ≫
          (pullbackComp i (b ≫ g)).inv.app M := by
    apply (cancel_epi ((pullbackComp i b).hom.app ((pullback g).obj M))).mp
    rw [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← pullbackComp_assoc_app]
    simp only [Category.assoc,Iso.hom_inv_id_app]
    erw [Category.comp_id]
  apply Iso.ext
  simp only [frameViaFactor,frameFactorIso,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,
    Functor.mapIso_hom,Functor.map_comp,Category.assoc]
  change (pullbackComp i b).inv.app ((pullback g).obj M) ≫
    (pullback i).map ((pullbackComp b g).hom.app M) ≫
      (pullback i).map e.hom ≫ (pullbackUnitIso i).hom =
    (pullbackComp (i ≫ b) g).hom.app M ≫
      (pullbackComp i (b ≫ g)).inv.app M ≫
        (pullback i).map e.hom ≫ (pullbackUnitIso i).hom
  rw [← Category.assoc ((pullbackComp i b).inv.app ((pullback g).obj M)),hc]
  simp only [Category.assoc]

/-- The genuine factor comparison followed by the transported whole frame
is the actual pullback of the original frame, for ANY comparison to the
same composite pullback object. -/
theorem frameFactorIso_pairing {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hg : g ≫ b = f)
    {M : C.Modules} {N : A.Modules} (p : N ≅ (pullback f).obj M)
    (e : (pullback b).obj M ≅ unitObj B) :
    (frameFactorIso g b f hg M ≪≫ p.symm) ≪≫
      (p ≪≫ frameViaFactor g b f hg e) =
        (pullback g).mapIso e ≪≫ pullbackUnitIso g := by
  unfold frameViaFactor
  simp only [Iso.trans_assoc,Iso.symm_self_id_assoc,Iso.self_symm_id_assoc]

end AlgebraicGeometry.Scheme.Modules
