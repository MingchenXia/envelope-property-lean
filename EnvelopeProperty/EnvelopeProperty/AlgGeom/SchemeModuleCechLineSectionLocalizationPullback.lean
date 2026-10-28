import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationTensor
import ModularCurves.ForMathlib.PullbackUnitMonoidal

/-! # Whole native pullback laws for actual section division

These laws identify the actual tensor maps and frames under native
pullback, and verify that division by the original s^m cancels actual
multiplication by that SAME section power on its actual nonzero open.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance actualLineSectionPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

private def rightUnit {X : Scheme.{u}} (F : X.Modules) : F ⊗ unitObj X ≅ F :=
  (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F

private theorem rightUnit_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) :
    (pullback g).map (rightUnit F).hom =
      (Functor.Monoidal.μIso (pullback g) F (unitObj X)).inv ≫
        (𝟙 ((pullback g).obj F) ⊗ₘ (pullbackUnitIso g).hom) ≫
          (rightUnit ((pullback g).obj F)).hom := by
  let G := pullback g
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  let v := pullbackUnitIso g
  have hu : Functor.OplaxMonoidal.η G ≫ uY.hom = G.map uX.hom ≫ v.hom :=
    congrArg Iso.hom (pullback_monoidalUnitObjIso g)
  have hv : G.map uX.inv ≫ Functor.OplaxMonoidal.η G = v.hom ≫ uY.inv := by
    apply (cancel_mono uY.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hu, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
  change G.map ((𝟙 F ⊗ₘ uX.inv) ≫ (ρ_ F).hom) =
    (Functor.Monoidal.μIso G F (unitObj X)).inv ≫
      (𝟙 (G.obj F) ⊗ₘ v.hom) ≫ (𝟙 (G.obj F) ⊗ₘ uY.inv) ≫ (ρ_ (G.obj F)).hom
  rw [G.map_comp, Functor.Monoidal.map_tensor, Functor.Monoidal.map_rightUnitor,
    G.map_id]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  have ht : (𝟙 (G.obj F) ⊗ₘ G.map uX.inv) ≫
      (𝟙 (G.obj F) ⊗ₘ Functor.OplaxMonoidal.η G) =
    (𝟙 (G.obj F) ⊗ₘ v.hom) ≫ (𝟙 (G.obj F) ⊗ₘ uY.inv) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, hv]
  simpa only [Category.assoc, id_tensorHom, Functor.Monoidal.μIso_inv] using
    congrArg (fun a => (Functor.Monoidal.μIso G F (unitObj X)).inv ≫ a ≫
      (ρ_ (G.obj F)).hom) ht

/-- The WHOLE actual tensor-frame contraction has its native pullback
formula, retaining the original frame and actual structure-unit comparison. -/
theorem tensorFrameIso_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules)
    {T : X.Modules} (e : T ≅ unitObj X) :
    (pullback g).map (tensorFrameIso F e).hom =
      (Functor.Monoidal.μIso (pullback g) F T).inv ≫
        (tensorFrameIso ((pullback g).obj F)
          ((pullback g).mapIso e ≪≫ pullbackUnitIso g)).hom := by
  let G := pullback g
  change G.map ((𝟙 F ⊗ₘ e.hom) ≫ (rightUnit F).hom) = _
  rw [G.map_comp, Functor.Monoidal.map_tensor, G.map_id, rightUnit_pullback]
  change _ = (Functor.Monoidal.μIso G F T).inv ≫
    (𝟙 (G.obj F) ⊗ₘ (G.map e.hom ≫ (pullbackUnitIso g).hom)) ≫
      (rightUnit (G.obj F)).hom
  dsimp only [G]
  simp only [Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, id_tensorHom, ← whiskerLeft_comp_assoc]

/-- Multiplication by the SAME original section commutes with WHOLE native
pullback; no coefficient or tensor comparison is supplied. -/
theorem tensorSectionMap_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules)
    {T : X.Modules} (t : unitObj X ⟶ T) :
    (pullback g).map (tensorSectionMap F t) ≫
        (Functor.Monoidal.μIso (pullback g) F T).inv =
      tensorSectionMap ((pullback g).obj F) (pullbackSectionHom g t) := by
  let G := pullback g
  have he : G.mapIso (rightUnit F) =
      (Functor.Monoidal.μIso G F (unitObj X)).symm ≪≫
        (Iso.refl (G.obj F) ⊗ᵢ pullbackUnitIso g) ≪≫ rightUnit (G.obj F) :=
    Iso.ext (rightUnit_pullback g F)
  have hi := congrArg Iso.inv he
  change G.map (rightUnit F).inv =
    (rightUnit (G.obj F)).inv ≫
      (𝟙 (G.obj F) ⊗ₘ (pullbackUnitIso g).inv) ≫
        (Functor.Monoidal.μIso G F (unitObj X)).hom at hi
  change G.map ((rightUnit F).inv ≫ (𝟙 F ⊗ₘ t)) ≫ _ = _
  rw [G.map_comp, hi, Functor.Monoidal.map_tensor, G.map_id]
  change _ = (rightUnit (G.obj F)).inv ≫
    (𝟙 (G.obj F) ⊗ₘ ((pullbackUnitIso g).inv ≫ G.map t))
  dsimp only [G]
  simp only [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id,
    id_tensorHom, ← whiskerLeft_comp_assoc]

/-- Actual multiplication by the SAME original s^m is exactly cancelled by
the canonical normalization on its WHOLE actual nonzero open. -/
theorem powerSectionTensorMap_normalized {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules) (m : ℕ) :
    (pullback (sectionOpen L hL s).ι).map (powerSectionTensorMap F L s m) ≫
      (normalizedTwistIso L hL s F m).hom = 𝟙 _ := by
  let V := sectionOpen L hL s
  let G := pullback V.ι
  change G.map (tensorSectionMap F (powerSectionHom s m)) ≫
      (Functor.Monoidal.μIso G F (bundleTensorPower L m)).inv ≫
        (tensorFrameIso (G.obj F) (powerSectionFrame L hL s m)).hom = _
  rw [← Category.assoc, tensorSectionMap_pullback, tensorSectionMap_frame]
  have hc : SchemeLineSectionUnitFrames.frameScalar (powerSectionFrame L hL s m)
      (pullbackSectionHom V.ι (powerSectionHom s m)) = 1 := by
    unfold SchemeLineSectionUnitFrames.frameScalar
    rw [powerSectionFrame_section]
    rfl
  rw [hc, ModularCurves.unitEndomorphismOfTopSection_one]
  simp only [SchemeUnitScalarAction.unitAction, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id]
  rfl

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
