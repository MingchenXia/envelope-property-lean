/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierModuleFlatPullback

/-! # Canonical whole module comparisons for actual invariant Cartier ideals -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y Z : Scheme.{u}}

/-- The actual whole pullback of the original ideal inclusion into the
original structure module, followed by its genuine structure comparison. -/
def pullbackModuleInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj I.toModules ⟶ Scheme.Modules.unitObj X :=
  (Scheme.Modules.pullback f).map I.toModulesInclusion ≫
    (Scheme.Modules.pullbackUnitIso f).hom

/-- The original canonical comparison gives exactly the entire true
pullback ideal inclusion. -/
theorem pullbackModuleInclusion_eq (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.pullbackModuleInclusion f =
      I.toModulesComapPullbackMap f ≫ (I.comap f).toModulesInclusion :=
  (I.toModulesComapPullbackMap_inclusion f).symm

/-- Actual whole pullback inclusions respect genuine native composition. -/
theorem pullbackModuleInclusion_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
        I.pullbackModuleInclusion (f ≫ g) =
      (Scheme.Modules.pullback f).map (I.pullbackModuleInclusion g) ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by
  unfold pullbackModuleInclusion
  rw [← Category.assoc, ← (Scheme.Modules.pullbackComp f g).hom.naturality,
    Category.assoc]
  have hu : (Scheme.Modules.pullbackComp f g).hom.app
      (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.pullbackUnitIso f).hom :=
    ModularCurves.pullbackUnitIso_compLow f g
  rw [hu]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ (Scheme.Modules.pullbackUnitIso f).hom)
      ((Scheme.Modules.pullback f).map_comp _ _).symm)

/-- Under actual flat Cartier pullback, the true whole structure-module
inclusion is a monomorphism. -/
theorem IsInvertible.pullbackModuleInclusion_mono {I : Y.IdealSheafData}
    (hI : I.IsInvertible) (f : X ⟶ Y) [Flat f] : Mono (I.pullbackModuleInclusion f) := by
  let := hI.toModulesComapPullbackMap_isIso f
  rw [I.pullbackModuleInclusion_eq f]
  infer_instance

/-- The genuine canonical module comparison of two equal whole geometric
Cartier pullbacks along actual flat morphisms. -/
def IsInvertible.invariantModuleIso {I : Y.IdealSheafData} (hI : I.IsInvertible)
    (f g : X ⟶ Y) [Flat f] [Flat g] (h : I.comap f = I.comap g) :
    (Scheme.Modules.pullback f).obj I.toModules ≅
      (Scheme.Modules.pullback g).obj I.toModules :=
  hI.flatPullbackModuleIso f ≪≫ toModulesEqualityIso _ _ h ≪≫
    (hI.flatPullbackModuleIso g).symm

/-- The actual comparison is normalized by the two true canonical
geometric ideal pullback maps on the whole original source. -/
theorem IsInvertible.invariantModuleIso_hom_comp_canonical
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f g : X ⟶ Y)
    [Flat f] [Flat g] (h : I.comap f = I.comap g) :
    (hI.invariantModuleIso f g h).hom ≫ I.toModulesComapPullbackMap g =
      I.toModulesComapPullbackMap f ≫ (toModulesEqualityIso _ _ h).hom := by
  let := hI.toModulesComapPullbackMap_isIso f
  let := hI.toModulesComapPullbackMap_isIso g
  simp [invariantModuleIso, flatPullbackModuleIso, Category.assoc]

/-- The true comparison preserves the whole included structure-module map. -/
theorem IsInvertible.invariantModuleIso_hom_inclusion
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f g : X ⟶ Y)
    [Flat f] [Flat g] (h : I.comap f = I.comap g) :
    (hI.invariantModuleIso f g h).hom ≫ I.pullbackModuleInclusion g =
      I.pullbackModuleInclusion f := by
  rw [I.pullbackModuleInclusion_eq g, ← Category.assoc,
    hI.invariantModuleIso_hom_comp_canonical f g h, Category.assoc,
    toModulesEqualityIso_hom_inclusion, ← I.pullbackModuleInclusion_eq f]

/-- The whole inclusion identity uniquely determines the actual invariant
Cartier module comparison, without a separate linearization premise. -/
theorem IsInvertible.invariantModuleIso_hom_unique
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f g : X ⟶ Y)
    [Flat f] [Flat g] (h : I.comap f = I.comap g)
    (q : (Scheme.Modules.pullback f).obj I.toModules ⟶
      (Scheme.Modules.pullback g).obj I.toModules)
    (hq : q ≫ I.pullbackModuleInclusion g = I.pullbackModuleInclusion f) :
    q = (hI.invariantModuleIso f g h).hom := by
  let := hI.pullbackModuleInclusion_mono g
  exact (cancel_mono (I.pullbackModuleInclusion g)).mp
    (hq.trans (hI.invariantModuleIso_hom_inclusion f g h).symm)


/-- The canonical comparison for the same true morphism is the actual identity. -/
theorem IsInvertible.invariantModuleIso_refl {I : Y.IdealSheafData}
    (hI : I.IsInvertible) (f : X ⟶ Y) [Flat f] :
    hI.invariantModuleIso f f rfl = Iso.refl _ := by
  apply Iso.ext
  exact (hI.invariantModuleIso_hom_unique f f rfl (𝟙 _) (by simp)).symm

/-- Actual invariant Cartier module comparisons obey true transitivity. -/
theorem IsInvertible.invariantModuleIso_trans {I : Y.IdealSheafData}
    (hI : I.IsInvertible) (f g h : X ⟶ Y) [Flat f] [Flat g] [Flat h]
    (hfg : I.comap f = I.comap g) (hgh : I.comap g = I.comap h) :
    hI.invariantModuleIso f g hfg ≪≫ hI.invariantModuleIso g h hgh =
      hI.invariantModuleIso f h (hfg.trans hgh) := by
  apply Iso.ext
  apply hI.invariantModuleIso_hom_unique
  change ((hI.invariantModuleIso f g hfg).hom ≫
    (hI.invariantModuleIso g h hgh).hom) ≫ I.pullbackModuleInclusion h = _
  rw [Category.assoc, hI.invariantModuleIso_hom_inclusion g h hgh,
    hI.invariantModuleIso_hom_inclusion f g hfg]

/-- Pullback of the actual invariant comparison is the true canonical
comparison of composite maps under native whole pullback composition. -/
theorem IsInvertible.invariantModuleIso_pullback {I : Z.IdealSheafData}
    (hI : I.IsInvertible) (f : X ⟶ Y) (a b : Y ⟶ Z)
    [Flat a] [Flat b] [Flat (f ≫ a)] [Flat (f ≫ b)]
    (hab : I.comap a = I.comap b) :
    (Scheme.Modules.pullback f).map (hI.invariantModuleIso a b hab).hom ≫
        (Scheme.Modules.pullbackComp f b).hom.app I.toModules =
      (Scheme.Modules.pullbackComp f a).hom.app I.toModules ≫
        (hI.invariantModuleIso (f ≫ a) (f ≫ b)
          ((I.comap_comp f a).trans
            ((congrArg (fun K : Y.IdealSheafData => K.comap f) hab).trans
              (I.comap_comp f b).symm))).hom := by
  let := hI.pullbackModuleInclusion_mono (f ≫ b)
  apply (cancel_mono (I.pullbackModuleInclusion (f ≫ b))).mp
  rw [Category.assoc, I.pullbackModuleInclusion_comp f b,
    ← Category.assoc, ← Functor.map_comp,
    hI.invariantModuleIso_hom_inclusion a b hab,
    Category.assoc, hI.invariantModuleIso_hom_inclusion,
    I.pullbackModuleInclusion_comp f a]


/-- Equality of actual scheme maps gives the same true canonical invariant
module comparison as the genuine native pullback equality isomorphism. -/
theorem IsInvertible.invariantModuleIso_congr {I : Y.IdealSheafData}
    (hI : I.IsInvertible) (f g : X ⟶ Y) [Flat f] [Flat g] (h : f = g) :
    hI.invariantModuleIso f g (congrArg I.comap h) =
      (Scheme.Modules.pullbackCongr h).app I.toModules := by
  subst g
  change hI.invariantModuleIso f f rfl = Iso.refl _
  exact hI.invariantModuleIso_refl f

/-- Genuine pullback of an actual module isomorphism, expressed on the
whole composite scheme morphisms through native composition isomorphisms. -/
def pullbackComparisonIso (I : Z.IdealSheafData) (a b : Y ⟶ Z)
    (e : (Scheme.Modules.pullback a).obj I.toModules ≅
      (Scheme.Modules.pullback b).obj I.toModules) (f : X ⟶ Y) :
    (Scheme.Modules.pullback (f ≫ a)).obj I.toModules ≅
      (Scheme.Modules.pullback (f ≫ b)).obj I.toModules :=
  ((Scheme.Modules.pullbackComp f a).app I.toModules).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫
      (Scheme.Modules.pullbackComp f b).app I.toModules

/-- The actual pulled-back comparison is precisely the canonical invariant
Cartier comparison of the whole composite maps; the base map need not be flat. -/
theorem IsInvertible.invariantModuleIso_pullback_iso {I : Z.IdealSheafData}
    (hI : I.IsInvertible) (f : X ⟶ Y) (a b : Y ⟶ Z)
    [Flat a] [Flat b] [Flat (f ≫ a)] [Flat (f ≫ b)]
    (hab : I.comap a = I.comap b) :
    I.pullbackComparisonIso a b (hI.invariantModuleIso a b hab) f =
      hI.invariantModuleIso (f ≫ a) (f ≫ b)
        ((I.comap_comp f a).trans
          ((congrArg (fun K : Y.IdealSheafData => K.comap f) hab).trans
            (I.comap_comp f b).symm)) := by
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackComp f a).hom.app I.toModules)).mp
  change ((Scheme.Modules.pullbackComp f a).app I.toModules).hom ≫
      (((Scheme.Modules.pullbackComp f a).app I.toModules).inv ≫
        (Scheme.Modules.pullback f).map (hI.invariantModuleIso a b hab).hom ≫
        ((Scheme.Modules.pullbackComp f b).app I.toModules).hom) = _
  rw [Iso.hom_inv_id_assoc]
  exact hI.invariantModuleIso_pullback f a b hab

end AlgebraicGeometry.Scheme.IdealSheafData
