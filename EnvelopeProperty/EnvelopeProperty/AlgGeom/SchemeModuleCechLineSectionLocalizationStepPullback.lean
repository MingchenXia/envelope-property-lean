import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationSteps

/-! # Original twist transitions retain canonical section normalization

Native pullback-power frames read the actual original transition scalar.
On the literal nonzero open the same original section is one, so its actual
successor and every finite iterate preserve the actual normalization map.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance stepPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

private def rightUnit {X : Scheme.{u}} (F : X.Modules) : F ⊗ unitObj X ≅ F :=
  (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F

/-! The following routine tensor congruence is internal. Its matching
equation is discharged by the actual native line-step calculation below. -/

private theorem actualPulledTensorFrame_scalar {X : Scheme.{u}} (F : X.Modules)
    {P Q : X.Modules} (c : P ⟶ Q) (e : P ≅ unitObj X) (d : Q ≅ unitObj X)
    (r : Γ(X, ⊤))
    (hc : c ≫ d.hom = e.hom ≫ ModularCurves.unitEndomorphismOfTopSection r) :
    (F ◁ c) ≫ (tensorFrameIso F d).hom =
      (tensorFrameIso F e).hom ≫
        SchemeUnitScalarAction.unitAction F (ModularCurves.unitEndomorphismOfTopSection r) := by
  have hs : SchemeLineSectionUnitFrames.frameScalar (Iso.refl (unitObj X))
      (ModularCurves.unitEndomorphismOfTopSection r) = r := by
    change (1 : Γ(X, ⊤)) * X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
    simp
  have h := tensorSectionMap_frame F (ModularCurves.unitEndomorphismOfTopSection r)
    (Iso.refl (unitObj X))
  rw [hs] at h
  change (rightUnit F).inv ≫ (𝟙 F ⊗ₘ ModularCurves.unitEndomorphismOfTopSection r) ≫
    (𝟙 F ⊗ₘ 𝟙 (unitObj X)) ≫ (rightUnit F).hom = _ at h
  rw [id_tensorHom, id_tensorHom, whiskerLeft_id, Category.id_comp] at h
  simp only [tensorFrameIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
  change (F ◁ c) ≫ ((F ◁ d.hom) ≫ (rightUnit F).hom) =
    ((F ◁ e.hom) ≫ (rightUnit F).hom) ≫ _
  rw [← whiskerLeft_comp_assoc, hc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, whiskerLeft_comp]

/-- EVERY actual original morphism and original pulled frame read the SAME
original line-step coefficient, using native power-frame recursion. -/
theorem lineSectionStep_pullback_frame {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (s : unitObj X ⟶ L)
    (e : (pullback g).obj L ≅ unitObj Y) (m : ℕ) :
    (pullback g).map (lineSectionStep L s m) ≫
        (SchemePulledPowerFrames.pullbackPowerFrame g e (m + 1)).hom =
      (SchemePulledPowerFrames.pullbackPowerFrame g e m).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (SchemeLineSectionUnitFrames.frameScalar e (pullbackSectionHom g s)) := by
  let G := pullback g
  let A := ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L
  rw [lineSectionStep, G.map_comp, SchemePulledPowerFrames.pullbackPowerFrame_succ]
  change (G.map (tensorSectionMap (bundleTensorPower L m) s) ≫ G.map A.hom) ≫
    (G.map A.inv ≫ (Functor.Monoidal.μIso G (bundleTensorPower L m) L).inv ≫
      (SchemeTensorPowerFrames.tensorFrame
        (SchemePulledPowerFrames.pullbackPowerFrame g e m) e).hom) = _
  rw [Category.assoc, ← Category.assoc (G.map A.hom) (G.map A.inv),
    ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.id_comp]
  rw [← Category.assoc, tensorSectionMap_pullback, tensorSectionMap_tensorFrame]

/-- The WHOLE actual original module transition retains the original scalar
in EVERY actual native pullback-power frame; all compatibility is internal. -/
theorem twistStep_pullback_frame {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F L : X.Modules) (s : unitObj X ⟶ L)
    (e : (pullback g).obj L ≅ unitObj Y) (m : ℕ) :
    (pullback g).map (twistStep F L s m) ≫
        (Functor.Monoidal.μIso (pullback g) F (bundleTensorPower L (m + 1))).inv ≫
          (tensorFrameIso ((pullback g).obj F)
            (SchemePulledPowerFrames.pullbackPowerFrame g e (m + 1))).hom =
      ((Functor.Monoidal.μIso (pullback g) F (bundleTensorPower L m)).inv ≫
        (tensorFrameIso ((pullback g).obj F)
          (SchemePulledPowerFrames.pullbackPowerFrame g e m)).hom) ≫
            SchemeUnitScalarAction.unitAction ((pullback g).obj F)
              (ModularCurves.unitEndomorphismOfTopSection
                (SchemeLineSectionUnitFrames.frameScalar e (pullbackSectionHom g s))) := by
  rw [twistStep, Functor.Monoidal.map_whiskerLeft]
  simp only [Functor.Monoidal.μIso_inv, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [actualPulledTensorFrame_scalar _ _ _ _ _
    (lineSectionStep_pullback_frame g L s e m)]

/-- The actual successor preserves the SAME canonical normalization on the
literal original nonzero open: actual s has coefficient exactly one there. -/
theorem twistStep_normalized {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (F : X.Modules) (m : ℕ) :
    (pullback (sectionOpen L hL s).ι).map (twistStep F L s m) ≫
      (normalizedTwistIso L hL s F (m + 1)).hom =
        (normalizedTwistIso L hL s F m).hom := by
  have h := twistStep_pullback_frame (sectionOpen L hL s).ι F L s
    (sectionFrame L hL s) m
  have hc : SchemeLineSectionUnitFrames.frameScalar (sectionFrame L hL s)
      (pullbackSectionHom (sectionOpen L hL s).ι s) = 1 := by
    unfold SchemeLineSectionUnitFrames.frameScalar
    rw [sectionFrame_section]
    rfl
  rw [hc, ModularCurves.unitEndomorphismOfTopSection_one] at h
  simp only [SchemeUnitScalarAction.unitAction, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id] at h
  exact h

/-- EVERY finite actual original transition preserves the actual original
normalization, with literal original twists m and m+a. -/
theorem twistIterate_normalized {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (F : X.Modules) (m a : ℕ) :
    (pullback (sectionOpen L hL s).ι).map (twistIterate F L s m a) ≫
      (normalizedTwistIso L hL s F (m + a)).hom =
        (normalizedTwistIso L hL s F m).hom := by
  induction a with
  | zero =>
    rw [twistIterate, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  | succ a ih =>
    change (pullback (sectionOpen L hL s).ι).map
      (twistIterate F L s m a ≫ twistStep F L s (m + a)) ≫
        (normalizedTwistIso L hL s F ((m + a) + 1)).hom = _
    rw [Functor.map_comp, Category.assoc, twistStep_normalized, ih]

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
