/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModulePullbackSections

/-!
# Actual ideal module comparison under whole open restriction

The actual scheme section isomorphism of an open immersion identifies
whole original ideal membership with its genuine geometric ideal comap.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- The genuine original open-immersion section isomorphism identifies actual
ideal membership on whole original opens with its true geometric ideal comap. -/
theorem isLocallyMem_comap_iff_appIso_inv (I : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] (W : X.Opens) (s : Γ(X, W)) :
    (I.comap g).IsLocallyMem W s ↔
      I.IsLocallyMem (g ''ᵁ W) ((g.appIso W).inv.hom s) := by
  constructor
  · intro hs V hVW
    have hVr : V.1 ≤ g.opensRange := by
      intro y hy
      obtain ⟨x, _hx, rfl⟩ := hVW hy
      exact Scheme.Hom.mem_opensRange.mpr ⟨x, rfl⟩
    let U : X.affineOpens := ⟨g ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion g hVr⟩
    have hUW : U.1 ≤ W := by
      intro x hx
      exact (Scheme.Hom.apply_mem_image_iff g).mp (hVW hx)
    have him : g ''ᵁ U.1 = V.1 := by
      change g ''ᵁ g ⁻¹ᵁ V.1 = V.1
      rw [g.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hVr]
    have hVim : V.1 ≤ g ''ᵁ U.1 := him.symm.le
    have hmem := hs U hUW
    rw [ideal_comap_of_isOpenImmersion] at hmem
    have htarget := I.ideal_le_comap_ideal
      (U := V) (V := ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩) hVim hmem
    change Y.presheaf.map (homOfLE hVim).op
      ((g.appIso U.1).inv.hom (X.presheaf.map (homOfLE hUW).op s)) ∈ I.ideal V at htarget
    have hm : X.presheaf.map (homOfLE hUW).op ≫ (g.appIso U.1).inv ≫
        Y.presheaf.map (homOfLE hVim).op =
      (g.appIso W).inv ≫ Y.presheaf.map (homOfLE hVW).op := by
      rw [← Category.assoc, g.appIso_inv_naturality, Category.assoc, ← Functor.map_comp]
      congr 2
    have he := congrArg (fun q : Γ(X, W) ⟶ Γ(Y, V) => q.hom s) hm
    exact he ▸ htarget
  · intro hs U hUW
    rw [ideal_comap_of_isOpenImmersion]
    change (g.appIso U.1).inv.hom (X.presheaf.map (homOfLE hUW).op s) ∈
      I.ideal ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩
    rw [← ConcreteCategory.comp_apply, g.appIso_inv_naturality,
      ConcreteCategory.comp_apply]
    exact hs ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩ (g.image_mono hUW)

/-- The true source section isomorphism restricts to an actual linear
equivalence of the entire original ideal-module section spaces. -/
def openRestrictionSectionsEquiv (I : Y.IdealSheafData) (g : X ⟶ Y)
    [IsOpenImmersion g] (W : X.Opens) :
    Γ(I.toModules.restrict g, W) ≃ₗ[Γ(X, W)] Γ((I.comap g).toModules, W) where
  toFun s := ⟨(g.appIso W).hom.hom s.1,
    (I.isLocallyMem_comap_iff_appIso_inv g W _).mpr (by
      have h := ConcreteCategory.congr_hom (g.appIso W).hom_inv_id s.1
      change I.IsLocallyMem (g ''ᵁ W) ((g.appIso W).inv.hom ((g.appIso W).hom.hom s.1))
      rw [show (g.appIso W).inv.hom ((g.appIso W).hom.hom s.1) = s.1 from h]
      exact s.2)⟩
  invFun s := ⟨(g.appIso W).inv.hom s.1,
    (I.isLocallyMem_comap_iff_appIso_inv g W s.1).mp s.2⟩
  left_inv s := Subtype.ext (ConcreteCategory.congr_hom (g.appIso W).hom_inv_id s.1)
  right_inv s := Subtype.ext (ConcreteCategory.congr_hom (g.appIso W).inv_hom_id s.1)
  map_add' s t := Subtype.ext (map_add (g.appIso W).hom.hom s.1 t.1)
  map_smul' r s := by
    apply Subtype.ext
    change (g.appIso W).hom.hom ((g.appIso W).inv.hom r *
      (show Γ(Y, g ''ᵁ W) from s.1)) =
        r * (g.appIso W).hom.hom (show Γ(Y, g ''ᵁ W) from s.1)
    rw [map_mul]
    have h := ConcreteCategory.congr_hom (g.appIso W).inv_hom_id r
    exact congrArg (· * (g.appIso W).hom.hom (show Γ(Y, g ''ᵁ W) from s.1)) h

/-- The actual entire restricted original ideal module is the actual module
sheaf of the genuine geometric ideal comap along an arbitrary open immersion. -/
def openRestrictionModuleIso (I : Y.IdealSheafData) (g : X ⟶ Y) [IsOpenImmersion g] :
    I.toModules.restrict g ≅ (I.comap g).toModules :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun W => (I.openRestrictionSectionsEquiv g W.unop).toModuleIso)
      (by
        intro U V h
        ext s
        apply Subtype.ext
        change (g.appIso V.unop).hom.hom
          (Y.presheaf.map (g.opensFunctor.op.map h) s.1) =
            X.presheaf.map h ((g.appIso U.unop).hom.hom s.1)
        exact congrArg (fun q : Γ(Y, g ''ᵁ U.unop) ⟶ Γ(X, V.unop) => q.hom s.1)
          (g.appIso_hom_naturality h)))

/-- The actual whole restriction isomorphism sends every original ideal
section to its true image under the genuine original ring section isomorphism. -/
theorem openRestrictionModuleIso_app (I : Y.IdealSheafData) (g : X ⟶ Y)
    [IsOpenImmersion g] (W : X.Opens) (s : Γ(I.toModules.restrict g, W)) :
    (show (I.comap g).toSubmodule.obj (op W) from
      (I.openRestrictionModuleIso g).hom.app W s).1 =
        (g.appIso W).hom.hom (s : I.toSubmodule.obj (op (g ''ᵁ W))).1 := rfl


/-- Under the genuine restriction adjunction, the whole open comparison is
exactly the true original geometric ideal section map. -/
theorem openRestrictionModuleIso_restrictAdjunction (I : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] :
    (Scheme.Modules.restrictAdjunction g).homEquiv I.toModules (I.comap g).toModules
        (I.openRestrictionModuleIso g).hom =
      I.toModulesComapPushforwardMap g := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply Subtype.ext
  change (g.appIso (g ⁻¹ᵁ W)).hom.hom
    (Y.presheaf.map (homOfLE (g.image_preimage_le W)).op
      (s : I.toSubmodule.obj (op W)).1) =
    (g.app W).hom (s : I.toSubmodule.obj (op W)).1
  have he : Y.presheaf.map (homOfLE (g.image_preimage_le W)).op ≫
      (g.appIso (g ⁻¹ᵁ W)).hom = g.app W := by
    calc
      _ = (g.app W ≫ (g.appIso (g ⁻¹ᵁ W)).inv) ≫
          (g.appIso (g ⁻¹ᵁ W)).hom := by
        exact congrArg (fun q => q ≫ (g.appIso (g ⁻¹ᵁ W)).hom)
          (g.app_appIso_inv W).symm
      _ = g.app W := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun q : Γ(Y, W) ⟶ Γ(X, g ⁻¹ᵁ W) =>
    q.hom (s : I.toSubmodule.obj (op W)).1) he

/-- The canonical whole ideal pullback comparison is the actual open
restriction isomorphism under the genuine native restriction--pullback iso. -/
theorem openRestrictionModuleIso_comp_toModulesComapPullbackMap
    (I : Y.IdealSheafData) (g : X ⟶ Y) [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorIsoPullback g).hom.app I.toModules ≫
        I.toModulesComapPullbackMap g =
      (I.openRestrictionModuleIso g).hom := by
  apply ((Scheme.Modules.restrictAdjunction g).homEquiv I.toModules
    (I.comap g).toModules).injective
  rw [Adjunction.homEquiv_naturality_right,
    Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app,
    I.openRestrictionModuleIso_restrictAdjunction]
  exact I.toModulesComapPullbackMap_unit g

/-- The true canonical ideal-module pullback comparison is an isomorphism
along any actual open immersion, for every whole original ideal. -/
theorem toModulesComapPullbackMap_isIso_of_isOpenImmersion
    (I : Y.IdealSheafData) (g : X ⟶ Y) [IsOpenImmersion g] :
    IsIso (I.toModulesComapPullbackMap g) := by
  have h : IsIso ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app I.toModules ≫
      I.toModulesComapPullbackMap g) := by
    rw [I.openRestrictionModuleIso_comp_toModulesComapPullbackMap g]
    infer_instance
  exact (isIso_comp_left_iff
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app I.toModules)
    (I.toModulesComapPullbackMap g)).mp h

/-- The actual canonical ideal-module pullback isomorphism for an arbitrary
open immersion, constructed without Cartier or flatness assumptions. -/
def openPullbackModuleIso (I : Y.IdealSheafData) (g : X ⟶ Y) [IsOpenImmersion g] :
    (Scheme.Modules.pullback g).obj I.toModules ≅ (I.comap g).toModules := by
  let := I.toModulesComapPullbackMap_isIso_of_isOpenImmersion g
  exact asIso (I.toModulesComapPullbackMap g)

end AlgebraicGeometry.Scheme.IdealSheafData
