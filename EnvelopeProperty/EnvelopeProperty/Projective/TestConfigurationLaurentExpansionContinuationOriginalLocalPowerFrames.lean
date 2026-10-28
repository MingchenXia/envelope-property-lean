import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativePowerTrivializationPullback

/-! # Actual source-derived original local and true-total-open degree-one model power frames -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Actual pullback composition DERIVES the entire original polarization-power restriction law. -/
theorem originalPolarizationPowerIso_pullback {A V Y Z : Scheme.{u}}
    (g : A ⟶ V) (j : V ⟶ Y) (p : V ⟶ Z) (M : Y.Modules) (L : Z.Modules)
    (σ : (pullback j).obj M ≅ (pullback p).obj L) (m : ℕ) :
    ((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
        (pullback g).mapIso (polarizationPowerIso j p M L σ m) ≪≫
          (pullbackComp g p).app (bundleTensorPower L m) =
      polarizationPowerIso (g ≫ j) (g ≫ p) M L
        (((pullbackComp g j).app M).symm ≪≫ (pullback g).mapIso σ ≪≫ (pullbackComp g p).app L) m := by
  let σg := ((pullbackComp g j).app M).symm ≪≫ (pullback g).mapIso σ ≪≫ (pullbackComp g p).app L
  have hj : ((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
      (pullback g).mapIso (tensorPowerPullbackIso j M m) ≪≫
        tensorPowerPullbackIso g ((pullback j).obj M) m =
      tensorPowerPullbackIso (g ≫ j) M m ≪≫ (tensorPowerIso ((pullbackComp g j).app M) m).symm := by
    have hh := congrArg (fun a => ((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
      a ≪≫ (tensorPowerIso ((pullbackComp g j).app M) m).symm)
      (originalTensorPowerPullbackIso_comp g j M m)
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.symm_self_id_assoc] using hh
  have hp : ((pullback g).mapIso (tensorPowerPullbackIso p L m)).symm ≪≫
      (pullbackComp g p).app (bundleTensorPower L m) ≪≫ tensorPowerPullbackIso (g ≫ p) L m =
      tensorPowerPullbackIso g ((pullback p).obj L) m ≪≫ tensorPowerIso ((pullbackComp g p).app L) m := by
    have hh := congrArg (fun a => ((pullback g).mapIso (tensorPowerPullbackIso p L m)).symm ≪≫ a)
      (originalTensorPowerPullbackIso_comp g p L m)
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using hh.symm
  have hn := originalTensorPowerPullbackIso_natural g σ m
  have hh : (((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
      (pullback g).mapIso (polarizationPowerIso j p M L σ m) ≪≫
        (pullbackComp g p).app (bundleTensorPower L m)) ≪≫ tensorPowerPullbackIso (g ≫ p) L m =
      tensorPowerPullbackIso (g ≫ j) M m ≪≫ tensorPowerIso σg m := by
    calc
      _ = ((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
          (pullback g).mapIso (tensorPowerPullbackIso j M m) ≪≫
            (pullback g).mapIso (tensorPowerIso σ m) ≪≫
              ((pullback g).mapIso (tensorPowerPullbackIso p L m)).symm ≪≫
                (pullbackComp g p).app (bundleTensorPower L m) ≪≫
                  tensorPowerPullbackIso (g ≫ p) L m := by
        simp only [polarizationPowerIso, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
      _ = ((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
          (pullback g).mapIso (tensorPowerPullbackIso j M m) ≪≫
            (pullback g).mapIso (tensorPowerIso σ m) ≪≫
              tensorPowerPullbackIso g ((pullback p).obj L) m ≪≫
                tensorPowerIso ((pullbackComp g p).app L) m := by rw [hp]
      _ = (((pullbackComp g j).app (bundleTensorPower M m)).symm ≪≫
          (pullback g).mapIso (tensorPowerPullbackIso j M m) ≪≫
            tensorPowerPullbackIso g ((pullback j).obj M) m) ≪≫
              tensorPowerIso ((pullback g).mapIso σ) m ≪≫
                tensorPowerIso ((pullbackComp g p).app L) m := by
        rw [← Iso.trans_assoc ((pullback g).mapIso (tensorPowerIso σ m))
          (tensorPowerPullbackIso g ((pullback p).obj L) m) (tensorPowerIso ((pullbackComp g p).app L) m), hn]
        simp only [Iso.trans_assoc]
      _ = (tensorPowerPullbackIso (g ≫ j) M m ≪≫
          (tensorPowerIso ((pullbackComp g j).app M) m).symm) ≪≫
            tensorPowerIso ((pullback g).mapIso σ) m ≪≫ tensorPowerIso ((pullbackComp g p).app L) m := by
        rw [hj]
      _ = _ := by
        simp only [σg, originalTensorPowerIso_trans, originalTensorPowerIso_symm, Iso.trans_assoc]
  have hf := congrArg (fun a => a ≪≫ (tensorPowerPullbackIso (g ≫ p) L m).symm) hh
  simpa only [polarizationPowerIso, σg, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hf

section OriginalFrames
open NativeTestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) (U : X.left.Opens)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
        (totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)

/-- TRUE original local degree-one polarization is INTERNALLY derived through actual native pullbackComp. -/
def originalTestConfigurationLocalPolarizationIso :
    (pullback (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)).obj M ≅
      (pullback (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ originalTestConfigurationUnitProjection C)).obj L :=
  ((pullbackComp ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι C.unitOpen.ι).app M).symm ≪≫
    (pullback ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι).mapIso
      (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) ≪≫
        (pullbackComp ((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι
          (originalTestConfigurationUnitProjection C)).app L

/-- An ACTUAL original degree-one local frame of M itself, not an identification of M-power one with M. -/
def originalTestConfigurationLocalDegreeOneModelFrame
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    (pullback (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)).obj M ≅
      unitObj (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).toScheme) :=
  originalTestConfigurationLocalPolarizationIso C U M L linearization fibreOneIdentification ≪≫
    frameViaFactor ((originalTestConfigurationUnitProjection C) ∣_ U) U.ι
      (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ originalTestConfigurationUnitProjection C)
      (morphismRestrict_ι (originalTestConfigurationUnitProjection C) U) δ

/-- SAME original sigma_m and delta_m local model-power frame is the TRUE degree-one M-frame power. -/
theorem originalTestConfigurationLocalModelPowerFrame_eq_degreeOne_power
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ) :
    originalTestConfigurationLocalModelPowerFrame C U M L linearization fibreOneIdentification δ m =
      tensorPowerPullbackIso (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι) M m ≪≫
        bundleTensorPowerTrivialization
          (originalTestConfigurationLocalDegreeOneModelFrame C U M L linearization fibreOneIdentification δ) m := by
  let p := originalTestConfigurationUnitProjection C
  let V := p ⁻¹ᵁ U
  let b := V.ι ≫ C.unitOpen.ι
  let q := V.ι ≫ p
  have hs : ((pullbackComp V.ι C.unitOpen.ι).app (bundleTensorPower M m)).symm ≪≫
      (pullback V.ι).mapIso (originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m) ≪≫
        (pullbackComp V.ι p).app (bundleTensorPower L m) =
      polarizationPowerIso b q M L
        (originalTestConfigurationLocalPolarizationIso C U M L linearization fibreOneIdentification) m :=
    originalPolarizationPowerIso_pullback V.ι C.unitOpen.ι p M L
      (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) m
  have hp : frameViaFactor (p ∣_ U) U.ι q (morphismRestrict_ι p U)
      (originalTestConfigurationLocalPowerFrame U L δ m) =
      tensorPowerPullbackIso q L m ≪≫
        bundleTensorPowerTrivialization (frameViaFactor (p ∣_ U) U.ι q (morphismRestrict_ι p U) δ) m :=
    originalFrameViaFactor_power (p ∣_ U) U.ι q (morphismRestrict_ι p U) δ m
  calc
    _ = (((pullbackComp V.ι C.unitOpen.ι).app (bundleTensorPower M m)).symm ≪≫
          (pullback V.ι).mapIso (originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m) ≪≫
            (pullbackComp V.ι p).app (bundleTensorPower L m)) ≪≫
              frameViaFactor (p ∣_ U) U.ι q (morphismRestrict_ι p U)
                (originalTestConfigurationLocalPowerFrame U L δ m) := by
      simp only [originalTestConfigurationLocalModelPowerFrame, p, V, q, Iso.trans_assoc]
    _ = polarizationPowerIso b q M L
        (originalTestConfigurationLocalPolarizationIso C U M L linearization fibreOneIdentification) m ≪≫
          (tensorPowerPullbackIso q L m ≪≫ bundleTensorPowerTrivialization
            (frameViaFactor (p ∣_ U) U.ι q (morphismRestrict_ι p U) δ) m) := by rw [hs, hp]
    _ = _ := originalPolarizationPowerIso_frame b q M L
      (originalTestConfigurationLocalPolarizationIso C U M L linearization fibreOneIdentification)
      (frameViaFactor (p ∣_ U) U.ι q (morphismRestrict_ι p U) δ) m

/-- Actual original open-image inverse constructs a TRUE degree-one frame of original M on the total open. -/
def originalTestConfigurationLocalDegreeOneTotalModelFrame
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    (pullback ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι).obj M ≅
      unitObj (((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).toScheme) :=
  frameViaFactor (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).isoOpensRange.inv
    (((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι)
    ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι
    (Scheme.Hom.isoOpensRange_inv_comp _)
    (originalTestConfigurationLocalDegreeOneModelFrame C U M L linearization fibreOneIdentification δ)

/-- SAME original true-total-open model-power frame is the genuine power of its actual degree-one M-frame. -/
theorem originalTestConfigurationLocalTotalModelPowerFrame_eq_degreeOne_power
    (δ : (pullback U.ι).obj L ≅ unitObj U.toScheme) (m : ℕ) :
    originalTestConfigurationLocalTotalModelPowerFrame C U M L linearization fibreOneIdentification δ m =
      tensorPowerPullbackIso
        ((((originalTestConfigurationUnitProjection C) ⁻¹ᵁ U).ι ≫ C.unitOpen.ι).opensRange).ι M m ≪≫
          bundleTensorPowerTrivialization
            (originalTestConfigurationLocalDegreeOneTotalModelFrame C U M L linearization fibreOneIdentification δ) m := by
  unfold originalTestConfigurationLocalTotalModelPowerFrame
  rw [originalTestConfigurationLocalModelPowerFrame_eq_degreeOne_power]
  exact originalFrameViaFactor_power _ _ _ _ _ m

end OriginalFrames
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
