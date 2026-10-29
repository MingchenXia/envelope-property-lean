/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModuleOpenRestriction
import ModularCurves.Picard.DualPullback.UnitComp

/-! # Actual composition of canonical geometric ideal-module pullbacks -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y Z : Scheme.{u}}

/-- A literal equality of whole original geometric ideals induces the true
module isomorphism, without a separate comparison premise. -/
def toModulesEqualityIso (I J : X.IdealSheafData) (h : I = J) :
    I.toModules ≅ J.toModules := eqToIso (congrArg toModules h)

/-- Whole ideal equality preserves every actual included section. -/
theorem toModulesEqualityIso_hom_app_inclusion (I J : X.IdealSheafData) (h : I = J)
    (W : X.Opens) (s : Γ(I.toModules, W)) :
    (show J.toSubmodule.obj (op W) from (toModulesEqualityIso I J h).hom.app W s).1 =
      (s : I.toSubmodule.obj (op W)).1 := by
  subst J
  rfl

/-- Whole ideal equality preserves the true entire structure-module inclusion. -/
theorem toModulesEqualityIso_hom_inclusion (I J : X.IdealSheafData) (h : I = J) :
    (toModulesEqualityIso I J h).hom ≫ J.toModulesInclusion = I.toModulesInclusion := by
  subst J
  simp [toModulesEqualityIso]

/-- The true canonical comparison respects actual composition of geometric
pullbacks on whole module sheaves, with genuine native composition maps. -/
theorem toModulesComapPullbackMap_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
        I.toModulesComapPullbackMap (f ≫ g) ≫
        (toModulesEqualityIso _ _ (I.comap_comp f g)).hom =
      (Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g) ≫
        (I.comap g).toModulesComapPullbackMap f := by
  apply (cancel_mono ((I.comap g).comap f).toModulesInclusion).mp
  rw [Category.assoc, Category.assoc, toModulesEqualityIso_hom_inclusion,
    I.toModulesComapPullbackMap_inclusion,
    Category.assoc, (I.comap g).toModulesComapPullbackMap_inclusion]
  change (Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
      (Scheme.Modules.pullback (f ≫ g)).map I.toModulesInclusion ≫
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g) ≫
      (Scheme.Modules.pullback f).map (I.comap g).toModulesInclusion ≫
      (Scheme.Modules.pullbackUnitIso f).hom
  rw [← Category.assoc, ← (Scheme.Modules.pullbackComp f g).hom.naturality,
    Category.assoc]
  have hu : (Scheme.Modules.pullbackComp f g).hom.app
      (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.pullbackUnitIso f).hom :=
    ModularCurves.pullbackUnitIso_compLow f g
  rw [hu]
  have hi : (Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g) ≫
      (Scheme.Modules.pullback f).map (I.comap g).toModulesInclusion =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map I.toModulesInclusion) ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom := by
    exact ((Scheme.Modules.pullback f).map_comp _ _).symm.trans
      ((congrArg (fun q => (Scheme.Modules.pullback f).map q)
        (I.toModulesComapPullbackMap_inclusion g)).trans
          ((Scheme.Modules.pullback f).map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (Scheme.Modules.pullbackUnitIso f).hom) hi.symm).trans
      (Category.assoc _ _ _))


/-- Actual successive canonical isomorphisms give the genuine whole
comparison isomorphism for the original composite morphism. -/
theorem toModulesComapPullbackMap_isIso_comp (I : Z.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsIso (I.toModulesComapPullbackMap g))
    (hf : IsIso ((I.comap g).toModulesComapPullbackMap f)) :
    IsIso (I.toModulesComapPullbackMap (f ≫ g)) := by
  let := hg
  let := hf
  have h : IsIso ((Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
      I.toModulesComapPullbackMap (f ≫ g) ≫
      (toModulesEqualityIso _ _ (I.comap_comp f g)).hom) := by
    rw [I.toModulesComapPullbackMap_comp f g]
    infer_instance
  have h' : IsIso ((Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
      I.toModulesComapPullbackMap (f ≫ g)) := by
    have h'' : IsIso (((Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
        I.toModulesComapPullbackMap (f ≫ g)) ≫
        (toModulesEqualityIso _ _ (I.comap_comp f g)).hom) := by
      simpa only [Category.assoc] using h
    exact (isIso_comp_right_iff _ _).mp h''
  exact (isIso_comp_left_iff _ _).mp h'

/-- Cancelling the actual second canonical isomorphism in true composition
proves that the actual pullback of the first comparison is an isomorphism. -/
theorem toModulesComapPullbackMap_isIso_pullback_of_comp (I : Z.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsIso (I.toModulesComapPullbackMap (f ≫ g)))
    (hf : IsIso ((I.comap g).toModulesComapPullbackMap f)) :
    IsIso ((Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g)) := by
  let := hfg
  let := hf
  have h : IsIso ((Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g) ≫
      (I.comap g).toModulesComapPullbackMap f) := by
    rw [← I.toModulesComapPullbackMap_comp f g]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end AlgebraicGeometry.Scheme.IdealSheafData
