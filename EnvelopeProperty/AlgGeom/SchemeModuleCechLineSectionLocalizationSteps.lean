import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationLocal

/-! # Actual original section transitions between the SAME tensor twists

The transition is literal multiplication by the original section in the
native tensor-power recursion. Finite iteration stays in F tensor L^(m+a),
and original frames read it back as exactly the original scalar power.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation SchemeTensorSectionHoms

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def rightUnit {X : Scheme.{u}} (F : X.Modules) : F ⊗ unitObj X ≅ F :=
  (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F

private theorem rightUnit_naturality {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) :
    (f ⊗ₘ 𝟙 (unitObj X)) ≫ (rightUnit Q).hom = (rightUnit P).hom ≫ f := by
  simp only [rightUnit, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
    MonoidalCategory.tensorHom_def, whiskerLeft_id, id_whiskerRight, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

private theorem rightUnit_unit {X : Scheme.{u}} :
    rightUnit (unitObj X) = ModularCurves.unitObjTensorIso X := by
  apply Iso.ext
  simp only [rightUnit, ModularCurves.unitObjTensorIso, Iso.trans_hom, tensorIso_hom,
    Iso.refl_hom, Iso.symm_hom]
  simp [MonoidalCategory.tensorHom_def', Category.assoc, unitors_equal]

private theorem tensorSectionMap_naturality {X : Scheme.{u}} {P Q T : X.Modules}
    (f : P ⟶ Q) (t : unitObj X ⟶ T) :
    f ≫ tensorSectionMap Q t = tensorSectionMap P t ≫ (f ⊗ₘ 𝟙 T) := by
  have hi : f ≫ (rightUnit Q).inv = (rightUnit P).inv ≫ (f ⊗ₘ 𝟙 (unitObj X)) := by
    apply (cancel_mono (rightUnit Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      rightUnit_naturality, Iso.inv_hom_id_assoc]
  change f ≫ (rightUnit Q).inv ≫ (𝟙 Q ⊗ₘ t) =
    ((rightUnit P).inv ≫ (𝟙 P ⊗ₘ t)) ≫ (f ⊗ₘ 𝟙 T)
  rw [← Category.assoc f, hi]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem tensorFrame_factor {X : Scheme.{u}} {P T : X.Modules}
    (e : P ≅ unitObj X) (d : T ≅ unitObj X) :
    (SchemeTensorPowerFrames.tensorFrame e d).hom =
      (e.hom ⊗ₘ 𝟙 T) ≫ (tensorFrameIso (unitObj X) d).hom := by
  change (e.hom ⊗ₘ d.hom) ≫ (ModularCurves.unitObjTensorIso X).hom =
    (e.hom ⊗ₘ 𝟙 T) ≫ ((𝟙 (unitObj X) ⊗ₘ d.hom) ≫ (rightUnit (unitObj X)).hom)
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    rightUnit_unit]

private theorem unitAction_unit {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    SchemeUnitScalarAction.unitAction (unitObj X)
      (ModularCurves.unitEndomorphismOfTopSection r) =
        ModularCurves.unitEndomorphismOfTopSection r := by
  have h := unitHom_eq_globalScalar (SchemeUnitScalarAction.unitAction (unitObj X)
    (ModularCurves.unitEndomorphismOfTopSection r))
  refine h.trans ?_
  congr 1
  change (SchemeUnitScalarAction.unitAction (unitObj X)
    (ModularCurves.unitEndomorphismOfTopSection r)).val.app (op ⊤) (1 : Γ(X, ⊤)) = r
  rw [SchemeUnitScalarAction.unitAction_apply,
    ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp

/-- Actual multiplication and two genuine original frames retain the
whole original section coefficient. This also applies to inherited native
pullback-power frames, without a supplied coefficient or matching premise. -/
theorem tensorSectionMap_tensorFrame {X : Scheme.{u}} {P T : X.Modules}
    (t : unitObj X ⟶ T) (e : P ≅ unitObj X) (d : T ≅ unitObj X) :
    tensorSectionMap P t ≫ (SchemeTensorPowerFrames.tensorFrame e d).hom =
      e.hom ≫ ModularCurves.unitEndomorphismOfTopSection
        (SchemeLineSectionUnitFrames.frameScalar d t) := by
  rw [tensorFrame_factor, ← Category.assoc, ← tensorSectionMap_naturality,
    Category.assoc, tensorSectionMap_frame, unitAction_unit]

/-- Literal multiplication by the SAME original section in the actual
native tensor-power successor, with no chosen frames. -/
def lineSectionStep {X : Scheme.{u}} (L : X.Modules) (s : unitObj X ⟶ L) (m : ℕ) :
    bundleTensorPower L m ⟶ bundleTensorPower L (m + 1) :=
  tensorSectionMap (bundleTensorPower L m) s ≫
    (ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).hom

private theorem lineSectionStep_frame {X : Scheme.{u}} (L : X.Modules)
    (s : unitObj X ⟶ L) (e : L ≅ unitObj X) (m : ℕ) :
    lineSectionStep L s m ≫ (SchemeTensorPowerFrames.powerFrame e (m + 1)).hom =
      (SchemeTensorPowerFrames.powerFrame e m).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (SchemeLineSectionUnitFrames.frameScalar e s) := by
  change (tensorSectionMap (bundleTensorPower L m) s ≫
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).hom) ≫
    ((ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).inv ≫
      (SchemeTensorPowerFrames.tensorFrame (SchemeTensorPowerFrames.powerFrame e m) e).hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [tensorSectionMap_tensorFrame]

private theorem tensorMap_frame_compare {X : Scheme.{u}} (F : X.Modules)
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

/-- The actual one-step original module-twist transition. -/
def twistStep {X : Scheme.{u}} (F L : X.Modules) (s : unitObj X ⟶ L) (m : ℕ) :
    F ⊗ bundleTensorPower L m ⟶ F ⊗ bundleTensorPower L (m + 1) :=
  F ◁ lineSectionStep L s m

/-- The actual native transition has exactly the original section scalar
in every original frame, as an ENTIRE original sheaf-map identity. -/
theorem twistStep_frame {X : Scheme.{u}} (F L : X.Modules) (s : unitObj X ⟶ L)
    (e : L ≅ unitObj X) (m : ℕ) :
    twistStep F L s m ≫
        (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e (m + 1))).hom =
      (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)).hom ≫
        SchemeUnitScalarAction.unitAction F
          (ModularCurves.unitEndomorphismOfTopSection
            (SchemeLineSectionUnitFrames.frameScalar e s)) :=
  tensorMap_frame_compare F (lineSectionStep L s m) _ _ _ (lineSectionStep_frame L s e m)

/-- Finite genuine multiplication by the SAME section stays in the SAME
literal original module twist F tensor L^(m+a). -/
def twistIterate {X : Scheme.{u}} (F L : X.Modules) (s : unitObj X ⟶ L) (m : ℕ) :
    (a : ℕ) → F ⊗ bundleTensorPower L m ⟶ F ⊗ bundleTensorPower L (m + a)
  | 0 => 𝟙 _
  | a + 1 => twistIterate F L s m a ≫ twistStep F L s (m + a)

/-- The SAME actual finite transition reads back to the SAME original
scalar raised to its actual number of steps, as a WHOLE original map. -/
theorem twistIterate_frame {X : Scheme.{u}} (F L : X.Modules) (s : unitObj X ⟶ L)
    (e : L ≅ unitObj X) (m a : ℕ) :
    twistIterate F L s m a ≫
        (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e (m + a))).hom =
      (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)).hom ≫
        SchemeUnitScalarAction.unitAction F
          (ModularCurves.unitEndomorphismOfTopSection
            (SchemeLineSectionUnitFrames.frameScalar e s ^ a)) := by
  induction a with
  | zero =>
    simp only [twistIterate, Nat.add_zero, Category.id_comp, pow_zero,
      ModularCurves.unitEndomorphismOfTopSection_one,
      SchemeUnitScalarAction.unitAction, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id]
  | succ a ih =>
    change (twistIterate F L s m a ≫ twistStep F L s (m + a)) ≫
      (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e ((m + a) + 1))).hom = _
    rw [Category.assoc, twistStep_frame, ← Category.assoc, ih, Category.assoc]
    have hc : SchemeUnitScalarAction.unitAction F
          (ModularCurves.unitEndomorphismOfTopSection
            (SchemeLineSectionUnitFrames.frameScalar e s ^ a)) ≫
        SchemeUnitScalarAction.unitAction F
          (ModularCurves.unitEndomorphismOfTopSection (SchemeLineSectionUnitFrames.frameScalar e s)) =
      SchemeUnitScalarAction.unitAction F
        (ModularCurves.unitEndomorphismOfTopSection (SchemeLineSectionUnitFrames.frameScalar e s ^ (a + 1))) := by
      simp only [SchemeUnitScalarAction.unitAction, Category.assoc,
        Iso.hom_inv_id_assoc]
      rw [← comp_whiskerRight_assoc, ModularCurves.unitEndomorphismOfTopSection_comp, pow_succ]
    rw [hc]

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
