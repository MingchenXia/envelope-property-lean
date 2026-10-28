import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationAffine
import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationPullback
import EnvelopeProperty.AlgGeom.SchemeOpenPullbackWholeUnits
import EnvelopeProperty.AlgGeom.SchemeUnitScalarActionBaseChange
import EnvelopeProperty.AlgGeom.SchemeModulePrincipalLocalization

/-! # Actual normalized denominator lifting on an original affine frame

The original quasicoherent section localization is consumed for the actual
original module. Its denominators produce sections of the SAME original
tensor twists, with equality under the actual canonical normalization.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open CanonicalGeometry SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms
open SchemeOpenPullbackSectionEquiv SchemeOpenPullbackWholeUnits

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance localSectionPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

private def rightUnit {X : Scheme.{u}} (F : X.Modules) : F ⊗ unitObj X ≅ F :=
  (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F

private theorem frame_scalar_postcomp {X : Scheme.{u}} (F : X.Modules) {T : X.Modules}
    (e d : T ≅ unitObj X) (a : Γ(X, ⊤))
    (hd : d.hom = e.hom ≫ ModularCurves.unitEndomorphismOfTopSection a) :
    (tensorFrameIso F d).hom = (tensorFrameIso F e).hom ≫
      SchemeUnitScalarAction.unitAction F (ModularCurves.unitEndomorphismOfTopSection a) := by
  have hc : SchemeLineSectionUnitFrames.frameScalar (Iso.refl (unitObj X))
      (ModularCurves.unitEndomorphismOfTopSection a) = a := by
    change (1 : Γ(X, ⊤)) * X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op a = a
    simp
  have h := tensorSectionMap_frame F (ModularCurves.unitEndomorphismOfTopSection a)
    (Iso.refl (unitObj X))
  rw [hc] at h
  change (rightUnit F).inv ≫ (𝟙 F ⊗ₘ ModularCurves.unitEndomorphismOfTopSection a) ≫
    (𝟙 F ⊗ₘ 𝟙 (unitObj X)) ≫ (rightUnit F).hom = _ at h
  rw [id_tensorHom_id, Category.id_comp] at h
  dsimp only [tensorFrameIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  change (𝟙 F ⊗ₘ d.hom) ≫ (rightUnit F).hom =
    ((𝟙 F ⊗ₘ e.hom) ≫ (rightUnit F).hom) ≫ _
  rw [Category.assoc]
  rw [← h, hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, id_tensorHom,
    whiskerLeft_comp]

/-- The actual original normalized value of a WHOLE original twisted section. -/
def normalizedTopValue {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (F : X.Modules) (m : ℕ)
    (y : Γ(F ⊗ bundleTensorPower L m, ⊤)) :
    Γ((pullback (sectionOpen L hL s).ι).obj F, ⊤) :=
  (normalizedTwistIso L hL s F m).hom.app ⊤
    (affinePullbackUnitTop (sectionOpen L hL s).ι (F ⊗ bundleTensorPower L m) y)

private theorem normalized_frame_map {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules)
    (e : L ≅ unitObj X) (m : ℕ) :
    (pullback (sectionOpen L hL s).ι).map
        (tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)).hom =
      (normalizedTwistIso L hL s F m).hom ≫
        SchemeUnitScalarAction.unitAction ((pullback (sectionOpen L hL s).ι).obj F)
          (ModularCurves.unitEndomorphismOfTopSection
            ((sectionOpen L hL s).ι.appTop
              (SchemeLineSectionUnitFrames.frameScalar e s ^ m))) := by
  rw [tensorFrameIso_pullback]
  rw [frame_scalar_postcomp _ (powerSectionFrame L hL s m) _ _
    (powerSectionFrame_compare L hL s e m)]
  rfl

private theorem normalized_frame_value {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules)
    (e : L ≅ unitObj X) (m : ℕ) (y : Γ(F ⊗ bundleTensorPower L m, ⊤)) :
    (sectionOpen L hL s).ι.appTop (SchemeLineSectionUnitFrames.frameScalar e s ^ m) •
        normalizedTopValue L hL s F m y =
      affinePullbackUnitTop (sectionOpen L hL s).ι F
        ((tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)).hom.app ⊤ y) := by
  rw [Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_naturality]
  rw [normalized_frame_map]
  change _ = (SchemeUnitScalarAction.unitAction
    ((pullback (sectionOpen L hL s).ι).obj F)
    (ModularCurves.unitEndomorphismOfTopSection
      ((sectionOpen L hL s).ι.appTop
        (SchemeLineSectionUnitFrames.frameScalar e s ^ m)))).val.app (op ⊤)
          (normalizedTopValue L hL s F m y)
  rw [SchemeUnitScalarAction.unitAction_apply]
  change _ = ((1 : Γ((sectionOpen L hL s).toScheme, ⊤)) *
    (sectionOpen L hL s).toScheme.presheaf.map
      (homOfLE (le_top : (⊤ : (sectionOpen L hL s).toScheme.Opens) ≤ ⊤)).op
      ((sectionOpen L hL s).ι.appTop
        (SchemeLineSectionUnitFrames.frameScalar e s ^ m))) • _
  simp
  rfl

private theorem openSectionsEquiv_naturality {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (V : X.Opens) (x : Γ(M, V)) :
    openSectionsEquiv N V (φ.app V x) =
      ((pullback V.ι).map φ).app ⊤ (openSectionsEquiv M V x) := by
  rw [openSectionsEquiv_apply, openSectionsEquiv_apply]
  unfold SchemePullbackLocalSections.openPullbackSection
  let k := (eqToHom V.ι_preimage_self.symm).op
  have hu := congrArg (fun a => a.app V x)
    ((pullbackPushforwardAdjunction V.ι).unit.naturality φ)
  change ((pullbackPushforwardAdjunction V.ι).unit.app N).app V (φ.app V x) =
    ((pullback V.ι).map φ).app (V.ι ⁻¹ᵁ V)
      (((pullbackPushforwardAdjunction V.ι).unit.app M).app V x) at hu
  have hn := PresheafOfModules.naturality_apply ((pullback V.ι).map φ).val k
    (((pullbackPushforwardAdjunction V.ι).unit.app M).app V x)
  exact (congrArg (((pullback V.ι).obj N).presheaf.map k) hu).trans hn.symm

private theorem openSectionsEquiv_global_smul {X : Scheme.{u}} (F : X.Modules)
    (V : X.Opens) (a : Γ(X, ⊤)) (x : Γ(F, V)) :
    openSectionsEquiv F V
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a • x) =
      V.ι.appTop a • openSectionsEquiv F V x := by
  have h := openSectionsEquiv_naturality
    (SchemeUnitScalarAction.globalScalarAction F a) V x
  change openSectionsEquiv F V
    ((SchemeUnitScalarAction.globalScalarAction F a).val.app (op V) x) =
      ((pullback V.ι).map (SchemeUnitScalarAction.globalScalarAction F a)).val.app
        (op ⊤) (openSectionsEquiv F V x) at h
  rw [SchemeUnitScalarAction.globalScalarAction_apply,
    SchemeUnitScalarActionBaseChange.globalScalarAction_pullback,
    SchemeUnitScalarAction.globalScalarAction_apply] at h
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id] at h
  (convert h using 1; rfl)

/-- Actual quasicoherent localization produces an ACTUAL original tensor
twist lifting any section of the literal nonzero open in an original affine
frame. The resulting normalized value is equality, not supplied matching. -/
theorem affine_normalized_lift {X : Scheme.{u}} [IsAffine X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (e : L ≅ unitObj X)
    (x : Γ((pullback (sectionOpen L hL s).ι).obj F, ⊤)) :
    ∃ (m : ℕ) (y : Γ(F ⊗ bundleTensorPower L m, ⊤)),
      normalizedTopValue L hL s F m y = x := by
  classical
  let V := sectionOpen L hL s
  let r := SchemeLineSectionUnitFrames.frameScalar e s
  let P := baseModulePresheaf (𝟙 X) F
  let φ := (P.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  have hV : V = X.basicOpen r := sectionOpen_eq_basicOpen_of_frame L hL s e
  let : IsLocalizedModule.Away r φ := by
    have hl : ∀ W : X.Opens, W = X.basicOpen r →
        IsLocalizedModule.Away r
          (P.map (homOfLE (le_top : W ≤ ⊤)).op).hom := by
      rintro W rfl
      simpa only [Scheme.Hom.id_preimage] using
        (SchemeModulePrincipalLocalization.restriction_isLocalizedModule (𝟙 X) F r)
    exact hl V hV
  let x₀ := (openSectionsEquiv F V).symm x
  obtain ⟨⟨z, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers r) φ x₀
  obtain ⟨m, hm⟩ := a.property
  have hz : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (r ^ m) • x₀ =
      F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op z := by
    have hh := ha
    change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a : Γ(X, ⊤)) • x₀ =
      F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op z at hh
    simpa only [hm] using hh
  let E := tensorFrameIso F (SchemeTensorPowerFrames.powerFrame e m)
  let y := E.inv.app ⊤ z
  have hy : E.hom.app ⊤ y = z := iso_inv_hom_app_applyT E (op ⊤) z
  refine ⟨m, y, ?_⟩
  have hnorm := normalized_frame_value L hL s F e m y
  rw [hy, ← openSectionsEquiv_global F V z, ← hz,
    openSectionsEquiv_global_smul] at hnorm
  rw [(openSectionsEquiv F V).apply_symm_apply] at hnorm
  have hr : IsUnit (V.ι.appTop r) := by
    change IsUnit ((sectionOpen L hL s).ι.appTop r)
    rw [sectionOpen_eq_basicOpen_of_frame L hL s e]
    exact SchemeLineSectionUnitFrames.basicOpen_appTop_isUnit r
  have hrm : IsUnit (V.ι.appTop (r ^ m)) := by
    rw [map_pow]
    exact hr.pow m
  exact hrm.smul_left_cancel.mp hnorm

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
