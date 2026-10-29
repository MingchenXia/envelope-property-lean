import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationTensor

/-! # The actual section open in its original affine frames

The original zero ideal determines the open. Original section coefficients
internally identify its actual framed restrictions with scalar basic opens.
The canonical section-power frame is compared with the inherited original
frame as an equality of whole morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation
open SchemeGlobalSectionTensorPowerNorms CyclicSectionGlobalCoverRootSectionPowers

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L)

/-- The SAME zero-ideal open is the actual scalar basic open in any true
original frame; the open comparison is derived, never supplied. -/
theorem sectionOpen_eq_basicOpen_of_frame (e : L ≅ unitObj X) :
    sectionOpen L hL s = X.basicOpen (SchemeLineSectionUnitFrames.frameScalar e s) := by
  let E : L.over ⊤ ≅ SheafOfModules.unit (X.ringCatSheaf.over ⊤) :=
    (SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e
  ext x
  change (x ∉ (LineSectionZeroIdeal.zeroIdeal L hL s).support) ↔ _
  rw [SchemeLineZeroSupportPullback.mem_support_iff_coefficient_zero L hL s ⊤ x
    (by trivial) E]
  change (¬ X.evaluation ⊤ x (by trivial)
    (SchemeLineSectionUnitFrames.frameScalar e s) = 0) ↔ _
  rw [X.evaluation_eq_zero_iff_notMem_basicOpen x (by trivial), not_not]
  rfl

/-- The actual nonzero open retains the original line and section under
every genuine scheme pullback. -/
theorem sectionOpen_pullback (g : Y ⟶ X) :
    sectionOpen ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s) =
      g ⁻¹ᵁ sectionOpen L hL s := by
  ext y
  change (y ∉ (LineSectionZeroIdeal.zeroIdeal ((pullback g).obj L) (hL.pullback g)
    (pullbackSectionHom g s)).support) ↔ _
  rw [SchemeLineZeroSupportPullback.support_pullback g L hL s]
  rfl

private theorem original_power_coefficient (e : L ≅ unitObj X) (m : ℕ) :
    SchemeLineSectionUnitFrames.frameScalar (SchemeTensorPowerFrames.powerFrame e m)
        (powerSectionHom s m) = SchemeLineSectionUnitFrames.frameScalar e s ^ m := by
  have h := powerSectionHom_frame s e
    (SchemeLineSectionUnitFrames.frameScalar e s)
    (SchemeLineSectionUnitFrames.frameScalar_identity e s) m
  have hh := congrArg sectionAtOne h
  change SchemeLineSectionUnitFrames.frameScalar
      (SchemeTensorPowerFrames.powerFrame e m) (powerSectionHom s m) = _ at hh
  exact hh.trans (by
    change (1 : Γ(X, ⊤)) * X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
        (SchemeLineSectionUnitFrames.frameScalar e s ^ m) = _
    simp)

/-- The inherited original frame differs from the actual canonical s^m
frame by exactly the SAME original section coefficient to the mth power.
This is a whole native morphism equality on the literal section open. -/
theorem powerSectionFrame_compare (e : L ≅ unitObj X) (m : ℕ) :
    (((pullback (sectionOpen L hL s).ι).mapIso
      (SchemeTensorPowerFrames.powerFrame e m)) ≪≫
        pullbackUnitIso (sectionOpen L hL s).ι).hom =
      (powerSectionFrame L hL s m).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((sectionOpen L hL s).ι.appTop
            (SchemeLineSectionUnitFrames.frameScalar e s ^ m)) := by
  let V := sectionOpen L hL s
  let τ := pullbackSectionHom V.ι (powerSectionHom s m)
  have hτ : τ ≫ (powerSectionFrame L hL s m).hom = 𝟙 _ :=
    powerSectionFrame_section L hL s m
  have hi : IsIso (τ ≫ (powerSectionFrame L hL s m).hom) := by
    rw [hτ]
    infer_instance
  let := hi
  have hτiso : IsIso τ :=
    IsIso.of_isIso_comp_right τ (powerSectionFrame L hL s m).hom
  let := hτiso
  apply (cancel_epi τ).mp
  rw [← Category.assoc, hτ, Category.id_comp]
  have h := SchemeLineSectionUnitFrames.pullback_frameScalar V.ι
    (SchemeTensorPowerFrames.powerFrame e m) (powerSectionHom s m)
  rw [original_power_coefficient L s e m] at h
  exact h

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
