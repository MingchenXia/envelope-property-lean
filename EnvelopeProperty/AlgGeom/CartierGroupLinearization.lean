/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierInvariantLinearization
import EnvelopeProperty.AlgGeom.SchemeGroupActionFlat

/-! # Whole group unit and cocycle for actual invariant Cartier module sheaves -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty

/-- Whiskering an actual flat map of schemes over the original base is flat. -/
theorem flatOverWhiskerLeft {S : Scheme.{u}} (R : Over S) {A B : Over S}
    (f : A ⟶ B) [Flat f.left] : Flat (R ◁ f).left := by
  rw [Over.whiskerLeft_left]
  exact MorphismProperty.pullbackMap (P := @Flat) (by infer_instance) (by infer_instance)
    (by simp) f.w.symm

variable {k : Type u} [Field k]
variable (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G B]
attribute [local instance] flat_groupAction_over_field

/-- The actual whole action morphism on the original scheme product. -/
abbrev cartierActionMap : (G ⊗ B).left ⟶ B.left := (ModObj.smul (M := G) (X := B)).left

/-- The actual whole second projection of the original scheme product. -/
abbrev cartierProjectionMap : (G ⊗ B).left ⟶ B.left := pullback.snd G.hom B.hom

/-- The genuine whole original group unit section. -/
def cartierUnitMap : B.left ⟶ (G ⊗ B).left :=
  ((λ_ B).inv ≫ ((MonObj.one (X := G)) ▷ B)).left

/-- The actual multiplication map on the whole original triple scheme. -/
def cartierMultiplyMap : ((G ⊗ G) ⊗ B).left ⟶ (G ⊗ B).left :=
  ((MonObj.mul (X := G)) ▷ B).left

/-- The actual whole inner-action map on the original triple scheme. -/
def cartierInnerActionMap : ((G ⊗ G) ⊗ B).left ⟶ (G ⊗ B).left :=
  ((α_ G G B).hom ≫ (G ◁ (ModObj.smul (M := G) (X := B)))).left

/-- The genuine whole tail projection of the original triple scheme. -/
def cartierTailMap : ((G ⊗ G) ⊗ B).left ⟶ (G ⊗ B).left :=
  ((α_ G G B).hom ≫ snd G (G ⊗ B)).left

/-- The true unit followed by the whole action is the actual identity. -/
theorem cartierUnitMap_action :
    cartierUnitMap G B ≫ cartierActionMap G B = 𝟙 B.left := by
  have h : (λ_ B).inv ≫ ((MonObj.one (X := G)) ▷ B) ≫
      ModObj.smul (M := G) (X := B) = 𝟙 B := by simp
  exact congrArg (fun q : B ⟶ B => q.left) h

omit [ModObj G B] in
/-- The true unit followed by the whole projection is the actual identity. -/
theorem cartierUnitMap_projection :
    cartierUnitMap G B ≫ cartierProjectionMap G B = 𝟙 B.left := by
  change (λ_ B).inv.left ≫ ((MonObj.one (X := G)) ▷ B).left ≫
    pullback.snd G.hom B.hom = _
  rw [Over.whiskerRight_left_snd]
  exact Over.leftUnitor_inv_left_snd B

/-- The original multiplication/action triangle is the entire action law. -/
theorem cartierMultiplyMap_action :
    cartierMultiplyMap G B ≫ cartierActionMap G B =
      cartierInnerActionMap G B ≫ cartierActionMap G B := by
  exact congrArg (fun q : (G ⊗ G) ⊗ B ⟶ B => q.left) (ModObj.mul_smul_self G B)

/-- The whole inner-action projection equals the genuine tail action. -/
theorem cartierInnerActionMap_projection :
    cartierInnerActionMap G B ≫ cartierProjectionMap G B =
      cartierTailMap G B ≫ cartierActionMap G B := by
  change (α_ G G B).hom.left ≫ (G ◁ ModObj.smul (M := G) (X := B)).left ≫
    pullback.snd G.hom B.hom =
    (α_ G G B).hom.left ≫ pullback.snd G.hom (G ⊗ B).hom ≫
      (ModObj.smul (M := G) (X := B)).left
  rw [Over.whiskerLeft_left_snd]
  rfl

omit [ModObj G B] in
/-- Multiplication and tail preserve the same whole original last projection. -/
theorem cartierMultiplyMap_projection :
    cartierMultiplyMap G B ≫ cartierProjectionMap G B =
      cartierTailMap G B ≫ cartierProjectionMap G B := by
  change ((MonObj.mul (X := G)) ▷ B).left ≫ pullback.snd G.hom B.hom =
    (α_ G G B).hom.left ≫ pullback.snd G.hom (G ⊗ B).hom ≫ pullback.snd G.hom B.hom
  rw [Over.whiskerRight_left_snd]
  exact (Over.associator_hom_left_snd_snd G G B).symm

/-- The genuine whole inner-action map is flat. -/
theorem cartierInnerActionMap_flat : Flat (cartierInnerActionMap G B) := by
  have : Flat (G ◁ (ModObj.smul (M := G) (X := B))).left := flatOverWhiskerLeft G _
  have : IsIso (α_ G G B).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (α_ G G B).hom))
  change Flat ((α_ G G B).hom.left ≫ (G ◁ (ModObj.smul (M := G) (X := B))).left)
  infer_instance

omit [GrpObj G] [ModObj G B] in
/-- The actual whole tail is a flat projection after the genuine associator. -/
theorem cartierTailMap_flat : Flat (cartierTailMap G B) := by
  have : IsIso (α_ G G B).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (α_ G G B).hom))
  change Flat ((α_ G G B).hom.left ≫ pullback.snd G.hom (G ⊗ B).hom)
  infer_instance

variable (I : B.left.IdealSheafData) (hI : I.IsInvertible)
variable (hinv : I.comap (cartierActionMap G B) = I.comap (cartierProjectionMap G B))

/-- The actual canonical group action isomorphism of the true invariant
Cartier ideal module; both flatness statements are proved over the original field. -/
def cartierGroupLinearization :
    (Scheme.Modules.pullback (cartierActionMap G B)).obj I.toModules ≅
      (Scheme.Modules.pullback (cartierProjectionMap G B)).obj I.toModules :=
  hI.invariantModuleIso (cartierActionMap G B) (cartierProjectionMap G B) hinv

/-- The actual whole group module comparison preserves its true inclusion. -/
theorem cartierGroupLinearization_inclusion :
    (cartierGroupLinearization G B I hI hinv).hom ≫
        I.pullbackModuleInclusion (cartierProjectionMap G B) =
      I.pullbackModuleInclusion (cartierActionMap G B) :=
  hI.invariantModuleIso_hom_inclusion _ _ hinv

/-- Pullback to the actual whole group unit is the genuine native equality
isomorphism of its two true identity composite maps. -/
theorem cartierGroupLinearization_unit :
    I.pullbackComparisonIso (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierGroupLinearization G B I hI hinv) (cartierUnitMap G B) =
      (Scheme.Modules.pullbackCongr
        ((cartierUnitMap_action G B).trans (cartierUnitMap_projection G B).symm)).app I.toModules := by
  have : Flat (cartierUnitMap G B ≫ cartierActionMap G B) :=
    (congrArg Flat (cartierUnitMap_action G B)).mpr (by infer_instance)
  have : Flat (cartierUnitMap G B ≫ cartierProjectionMap G B) :=
    (congrArg Flat (cartierUnitMap_projection G B)).mpr (by infer_instance)
  rw [cartierGroupLinearization, hI.invariantModuleIso_pullback_iso]
  exact hI.invariantModuleIso_congr _ _ _


/-- The actual invariant Cartier module isomorphism satisfies the whole
original group cocycle on the entire genuine triple scheme product. -/
theorem cartierGroupLinearization_cocycle :
    (Scheme.Modules.pullbackCongr (cartierMultiplyMap_action G B)).app I.toModules ≪≫
      I.pullbackComparisonIso (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierGroupLinearization G B I hI hinv) (cartierInnerActionMap G B) ≪≫
      (Scheme.Modules.pullbackCongr (cartierInnerActionMap_projection G B)).app I.toModules ≪≫
      I.pullbackComparisonIso (cartierActionMap G B) (cartierProjectionMap G B)
        (cartierGroupLinearization G B I hI hinv) (cartierTailMap G B) ≪≫
      (Scheme.Modules.pullbackCongr (cartierMultiplyMap_projection G B).symm).app I.toModules =
    I.pullbackComparisonIso (cartierActionMap G B) (cartierProjectionMap G B)
      (cartierGroupLinearization G B I hI hinv) (cartierMultiplyMap G B) := by
  have : Flat (cartierInnerActionMap G B) := cartierInnerActionMap_flat G B
  have : Flat (cartierTailMap G B) := cartierTailMap_flat G B
  have : Flat (cartierMultiplyMap G B ≫ cartierActionMap G B) :=
    (congrArg Flat (cartierMultiplyMap_action G B)).mpr (by infer_instance)
  have : Flat (cartierMultiplyMap G B ≫ cartierProjectionMap G B) :=
    (congrArg Flat (cartierMultiplyMap_projection G B)).mpr (by infer_instance)
  rw [cartierGroupLinearization,
    hI.invariantModuleIso_pullback_iso (cartierInnerActionMap G B),
    hI.invariantModuleIso_pullback_iso (cartierTailMap G B),
    hI.invariantModuleIso_pullback_iso (cartierMultiplyMap G B)]
  rw [← hI.invariantModuleIso_congr _ _ (cartierMultiplyMap_action G B),
    ← hI.invariantModuleIso_congr _ _ (cartierInnerActionMap_projection G B),
    ← hI.invariantModuleIso_congr _ _ (cartierMultiplyMap_projection G B).symm]
  simp only [hI.invariantModuleIso_trans]

end EnvelopeProperty
