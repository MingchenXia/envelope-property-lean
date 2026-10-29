import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativePowerFrameNaturality

/-! # Actual native tensor powers through true pullback composition and geometric factor squares -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- The SAME native pullbackComp respects the actual original power comparison in EVERY degree. -/
theorem originalTensorPowerPullbackIso_comp {A B D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (M : D.Modules) (m : ℕ) :
    (pullback f).mapIso (tensorPowerPullbackIso g M m) ≪≫
        tensorPowerPullbackIso f ((pullback g).obj M) m ≪≫
          tensorPowerIso ((pullbackComp f g).app M) m =
      (pullbackComp f g).app (bundleTensorPower M m) ≪≫ tensorPowerPullbackIso (f ≫ g) M m := by
  induction m with
  | zero =>
    simp only [tensorPowerPullbackIso, tensorPowerIso]
    apply Iso.ext
    exact (ModularCurves.pullbackUnitIso_compLow f g).symm
  | succ m ih =>
    change (pullback f).mapIso
        (canonicalTensorPullbackIso g (bundleTensorPower M m) M ≪≫
          tensorObjCongr (tensorPowerPullbackIso g M m) (Iso.refl _)) ≪≫
        (canonicalTensorPullbackIso f (bundleTensorPower ((pullback g).obj M) m) ((pullback g).obj M) ≪≫
          tensorObjCongr (tensorPowerPullbackIso f ((pullback g).obj M) m) (Iso.refl _)) ≪≫
            tensorObjCongr (tensorPowerIso ((pullbackComp f g).app M) m) ((pullbackComp f g).app M) =
      (pullbackComp f g).app (tensorObj (bundleTensorPower M m) M) ≪≫
        (canonicalTensorPullbackIso (f ≫ g) (bundleTensorPower M m) M ≪≫
          tensorObjCongr (tensorPowerPullbackIso (f ≫ g) M m) (Iso.refl _))
    have ht := tensorObjCongr_trans ((pullbackComp f g).app (bundleTensorPower M m))
      (tensorPowerPullbackIso (f ≫ g) M m) ((pullbackComp f g).app M)
      (Iso.refl ((pullback (f ≫ g)).obj M))
    calc
      _ = (pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M m) M) ≪≫
          canonicalTensorPullbackIso f ((pullback g).obj (bundleTensorPower M m)) ((pullback g).obj M) ≪≫
            tensorObjCongr ((pullbackComp f g).app (bundleTensorPower M m) ≪≫
              tensorPowerPullbackIso (f ≫ g) M m) ((pullbackComp f g).app M) := by
        rw [Functor.mapIso_trans]
        simp only [Iso.trans_assoc]
        rw [← Iso.trans_assoc ((pullback f).mapIso
          (tensorObjCongr (tensorPowerPullbackIso g M m) (Iso.refl _))),
          canonicalTensorPullbackIso_natural]
        simp only [Iso.trans_assoc, Functor.mapIso_refl, ← tensorObjCongr_trans,
          Iso.refl_trans]
        rw [ih]
      _ = ((pullback f).mapIso (canonicalTensorPullbackIso g (bundleTensorPower M m) M) ≪≫
          canonicalTensorPullbackIso f ((pullback g).obj (bundleTensorPower M m)) ((pullback g).obj M) ≪≫
            tensorObjCongr ((pullbackComp f g).app (bundleTensorPower M m)) ((pullbackComp f g).app M)) ≪≫
              tensorObjCongr (tensorPowerPullbackIso (f ≫ g) M m) (Iso.refl _) := by
        rw [show tensorObjCongr ((pullbackComp f g).app (bundleTensorPower M m) ≪≫
            tensorPowerPullbackIso (f ≫ g) M m) ((pullbackComp f g).app M) =
          tensorObjCongr ((pullbackComp f g).app (bundleTensorPower M m)) ((pullbackComp f g).app M) ≪≫
            tensorObjCongr (tensorPowerPullbackIso (f ≫ g) M m) (Iso.refl _) from
          by simpa only [Iso.trans_refl] using ht]
        simp only [Iso.trans_assoc]
      _ = _ := by
        rw [canonicalTensorPullbackIso_comp]
        exact Iso.trans_assoc _ _ _

/-- Actual equality of original scheme morphisms DERIVES whole native power congruence. -/
theorem originalTensorPowerPullbackIso_congr {A B : Scheme.{u}} {g h : A ⟶ B}
    (he : g = h) (M : B.Modules) (m : ℕ) :
    (pullbackCongr he).app (bundleTensorPower M m) ≪≫ tensorPowerPullbackIso h M m =
      tensorPowerPullbackIso g M m ≪≫ tensorPowerIso ((pullbackCongr he).app M) m := by
  subst h
  change Iso.refl _ ≪≫ tensorPowerPullbackIso g M m =
    tensorPowerPullbackIso g M m ≪≫ tensorPowerIso (Iso.refl _) m
  rw [Iso.refl_trans, originalTensorPowerIso_refl, Iso.trans_refl]

/-- The ACTUAL original factor-square comparison respects genuine native powers; no power certificate. -/
theorem originalFrameFactorIso_power {A B D : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ D) (f : A ⟶ D) (hg : g ≫ b = f)
    (M : D.Modules) (m : ℕ) :
    (pullback g).mapIso (tensorPowerPullbackIso b M m) ≪≫
        tensorPowerPullbackIso g ((pullback b).obj M) m ≪≫
          tensorPowerIso (frameFactorIso g b f hg M) m =
      frameFactorIso g b f hg (bundleTensorPower M m) ≪≫ tensorPowerPullbackIso f M m := by
  calc
    _ = ((pullback g).mapIso (tensorPowerPullbackIso b M m) ≪≫
        tensorPowerPullbackIso g ((pullback b).obj M) m ≪≫
          tensorPowerIso ((pullbackComp g b).app M) m) ≪≫
            tensorPowerIso ((pullbackCongr hg).app M) m := by
      rw [frameFactorIso, originalTensorPowerIso_trans]
      simp only [Iso.trans_assoc]
    _ = ((pullbackComp g b).app (bundleTensorPower M m) ≪≫
        tensorPowerPullbackIso (g ≫ b) M m) ≪≫
          tensorPowerIso ((pullbackCongr hg).app M) m := by
      rw [originalTensorPowerPullbackIso_comp]
    _ = (pullbackComp g b).app (bundleTensorPower M m) ≪≫
        (pullbackCongr hg).app (bundleTensorPower M m) ≪≫ tensorPowerPullbackIso f M m := by
      rw [Iso.trans_assoc, ← originalTensorPowerPullbackIso_congr]
    _ = _ := (Iso.trans_assoc _ _ _).symm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
