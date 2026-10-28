/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Actual global sections giving genuine local module frames

The elementary actual section-Hom restriction proof is adapted from the
private section-Hom arguments in the imported native PoleSheaf source.
-/
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules ModularCurves
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleGlobalSections

def sectionHom
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : Scheme.Modules.unitObj X ⟶ M :=
  M.unitHomEquiv.symm (moduleSectionsOfTop M x)

private theorem sectionHom_app_top_apply_one
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    (sectionHom M x).val.app (.op ⊤)
      (show X.presheaf.obj (.op ⊤) from 1) = x := by
  change (M.unitHomEquiv (sectionHom M x)).val (.op ⊤) = x
  let s := moduleSectionsOfTop M x
  have he : M.unitHomEquiv (sectionHom M x) = s :=
    Equiv.apply_symm_apply M.unitHomEquiv s
  have hv := congrArg (fun t ↦ t.val (.op (⊤ : X.Opens))) he
  rw [hv]
  change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
  simp
  rfl

private theorem sectionHom_app_apply
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (W : X.Opens) (a : Γ(X, W)) :
    (sectionHom M x).val.app (.op W) a =
      a • M.presheaf.map
        (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op x := by
  rfl

private theorem unit_hom_ext_top
    {X : Scheme.{u}} {M : X.Modules}
    {f g : Scheme.Modules.unitObj X ⟶ M}
    (h : f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1) =
      g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) :
    f = g := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have hf := PresheafOfModules.naturality_apply f.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  have hg := PresheafOfModules.naturality_apply g.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  change f.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hf
  change g.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hg
  rw [map_one] at hf hg
  exact hf.trans ((congrArg (fun q ↦ M.presheaf.map i q) h).trans hg.symm)

theorem sectionHom_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) :
    sectionHom ((Scheme.Modules.restrictFunctor U.1.ι).obj M)
        (localTrivializationRestriction M U x) =
      (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map
          (sectionHom M x) := by
  apply unit_hom_ext_top
  rw [sectionHom_app_top_apply_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [Scheme.Modules.restrictUnitIso_inv_app_applyP]
  rw [map_one]
  unfold localTrivializationRestriction
  let s : Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map
        (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x)
  have hrestrict :
      (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv s = s :=
    rfl
  have hmapApply :
      ((Scheme.Modules.restrictFunctor U.1.ι).map
          (sectionHom M x)).val.app (.op ⊤)
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) =
        (sectionHom M x).val.app
          (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) :=
    rfl
  have hs : s =
      (sectionHom M x).val.app
        (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
          (show X.presheaf.obj
            (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) := by
    dsimp only [s]
    rw [sectionHom_app_apply, one_smul]
    change M.presheaf.map (eqToHom U.1.ι_image_top).op
        (M.presheaf.map
          (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x) =
      M.presheaf.map
        (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
          (⊤ : X.Opens))).op x
    rw [← M.presheaf.map_comp_apply]
    rw [Subsingleton.elim
      ((homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op ≫
        (eqToHom U.1.ι_image_top).op)
      (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
        (⊤ : X.Opens))).op]
  exact hrestrict.trans (hs.trans hmapApply.symm)

/-- Composition of the SAME original section map takes the actual original
section to its actual image, with no choice of an auxiliary coefficient space. -/
theorem sectionHom_comp {X : Scheme.{u}} {M N : X.Modules}
    (s : Γ(M, (⊤ : X.Opens))) (f : M ⟶ N) :
    sectionHom M s ≫ f = sectionHom N (f.val.app (.op ⊤) s) := by
  apply unit_hom_ext_top
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (congrArg (fun z => f.val.app (.op ⊤) z)
    (sectionHom_app_top_apply_one M s)).trans
      (sectionHom_app_top_apply_one N (f.val.app (.op ⊤) s)).symm

private theorem sectionHom_one {X : Scheme.{u}} :
    sectionHom (unitObj X) (show Γ(X, (⊤ : X.Opens)) from 1) = 𝟙 (unitObj X) := by
  apply unit_hom_ext_top
  exact sectionHom_app_top_apply_one (unitObj X) (show Γ(X, (⊤ : X.Opens)) from 1)

/-- A genuine original global section whose coefficient in an actual original
local frame is one gives an isomorphism on that actual original open. -/
theorem isIso_restrict_sectionHom_of_coefficient_one {X : Scheme.{u}}
    (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ unitObj U.1.toScheme)
    (s : Γ(M, (⊤ : X.Opens)))
    (h : localTrivializationTopSection M U e s = 1) :
    IsIso ((restrictFunctor U.1.ι).map (sectionHom M s)) := by
  have hc := sectionHom_comp (localTrivializationRestriction M U s) e.hom
  change sectionHom (M.restrict U.1.ι) (localTrivializationRestriction M U s) ≫ e.hom =
    sectionHom (unitObj U.1.toScheme) (localTrivializationTopSection M U e s) at hc
  rw [h, sectionHom_one] at hc
  let q := (restrictFunctor U.1.ι).map (sectionHom M s)
  let r : (restrictFunctor U.1.ι).obj (unitObj X) ≅ unitObj U.1.toScheme :=
    restrictUnitIso U.1.ι
  have hr : sectionHom (M.restrict U.1.ι) (localTrivializationRestriction M U s) =
      r.inv ≫ q := sectionHom_restrict M U s
  have ht : (r.inv ≫ q) ≫ e.hom = 𝟙 (unitObj U.1.toScheme) :=
    (congrArg (fun f => f ≫ e.hom) hr).symm.trans hc
  have hi : r.inv ≫ q = e.inv := by
    apply (cancel_mono e.hom).mp
    exact ht.trans e.inv_hom_id.symm
  have heq : q = r.hom ≫ e.inv := by
    exact (r.hom_inv_id_assoc q).symm.trans (congrArg (fun f => r.hom ≫ f) hi)
  change IsIso q
  rw [heq]
  infer_instance

end EnvelopeProperty.SchemeModuleGlobalSections
