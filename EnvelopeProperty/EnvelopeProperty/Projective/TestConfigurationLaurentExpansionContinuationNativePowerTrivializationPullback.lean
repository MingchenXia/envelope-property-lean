import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativeUnitMultiplicationPullback

/-! # Genuine all-power pullback trivializations and actual original factored frames -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Actual native powers preserve the inverse of every genuine original module iso. -/
theorem originalTensorPowerIso_symm {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (m : ℕ) : tensorPowerIso e.symm m = (tensorPowerIso e m).symm := by
  have hh : tensorPowerIso e m ≪≫ tensorPowerIso e.symm m = Iso.refl _ := by
    rw [← originalTensorPowerIso_trans, Iso.self_symm_id, originalTensorPowerIso_refl]
  apply Iso.ext
  apply (cancel_epi (tensorPowerIso e m).hom).mp
  simpa only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.hom_inv_id] using congrArg Iso.hom hh

/-- Genuine native pullback preserves the ACTUAL original power-frame trivialization, including degree zero. -/
theorem originalBundleTensorPowerTrivialization_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M : Z.Modules} (e : M ≅ unitObj Z) (m : ℕ) :
    (pullback f).mapIso (bundleTensorPowerTrivialization e m) ≪≫ pullbackUnitIso f =
      tensorPowerPullbackIso f M m ≪≫
        bundleTensorPowerTrivialization ((pullback f).mapIso e ≪≫ pullbackUnitIso f) m := by
  induction m with
  | zero =>
    change (pullback f).mapIso (Iso.refl _) ≪≫ pullbackUnitIso f = pullbackUnitIso f ≪≫ Iso.refl _
    rw [Functor.mapIso_refl]
    exact (Iso.refl_trans _).trans (Iso.trans_refl _).symm
  | succ m ih =>
    let eF := (pullback f).mapIso e ≪≫ pullbackUnitIso f
    change (pullback f).mapIso
        (tensorObjCongr (bundleTensorPowerTrivialization e m) e ≪≫ bundleTensorLeftUnitIso (unitObj Z)) ≪≫
          pullbackUnitIso f =
      (canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
        tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl _)) ≪≫
          (tensorObjCongr (bundleTensorPowerTrivialization eF m) eF ≪≫ bundleTensorLeftUnitIso (unitObj Y))
    have ht := tensorObjCongr_trans (tensorPowerPullbackIso f M m)
      (bundleTensorPowerTrivialization eF m) (Iso.refl ((pullback f).obj M)) eF
    have hn : (pullback f).mapIso (tensorObjCongr (bundleTensorPowerTrivialization e m) e) ≪≫
        canonicalTensorPullbackIso f (unitObj Z) (unitObj Z) =
      canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
        tensorObjCongr ((pullback f).mapIso (bundleTensorPowerTrivialization e m))
          ((pullback f).mapIso e) :=
      canonicalTensorPullbackIso_natural f (bundleTensorPowerTrivialization e m) e
    calc
      _ = canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
          tensorObjCongr ((pullback f).mapIso (bundleTensorPowerTrivialization e m) ≪≫ pullbackUnitIso f)
            eF ≪≫ bundleTensorLeftUnitIso (unitObj Y) := by
        rw [Functor.mapIso_trans]
        simp only [Iso.trans_assoc]
        rw [originalBundleTensorUnitIso_pullback]
        rw [← Iso.trans_assoc ((pullback f).mapIso (tensorObjCongr (bundleTensorPowerTrivialization e m) e))]
        erw [hn]
        simp only [eF, tensorObjCongr_trans, Iso.trans_assoc]
      _ = canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
          tensorObjCongr (tensorPowerPullbackIso f M m ≪≫ bundleTensorPowerTrivialization eF m)
            eF ≪≫ bundleTensorLeftUnitIso (unitObj Y) := by rw [ih]
      _ = _ := by
        rw [show tensorObjCongr (tensorPowerPullbackIso f M m ≪≫ bundleTensorPowerTrivialization eF m) eF =
          tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl ((pullback f).obj M)) ≪≫
            tensorObjCongr (bundleTensorPowerTrivialization eF m) eF from
          by simpa only [Iso.refl_trans] using ht]
        simp only [Iso.trans_assoc]

/-- Actual original geometric factor frames preserve genuine native powers; no power comparison input. -/
theorem originalFrameViaFactor_power {A B D : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ D) (f : A ⟶ D) (hg : g ≫ b = f)
    {M : D.Modules} (e : (pullback b).obj M ≅ unitObj B) (m : ℕ) :
    frameViaFactor g b f hg (tensorPowerPullbackIso b M m ≪≫ bundleTensorPowerTrivialization e m) =
      tensorPowerPullbackIso f M m ≪≫ bundleTensorPowerTrivialization (frameViaFactor g b f hg e) m := by
  have hs := originalFrameFactorIso_power g b f hg M m
  have hc : (frameFactorIso g b f hg (bundleTensorPower M m)).symm ≪≫
      (pullback g).mapIso (tensorPowerPullbackIso b M m) ≪≫
        tensorPowerPullbackIso g ((pullback b).obj M) m =
      tensorPowerPullbackIso f M m ≪≫ (tensorPowerIso (frameFactorIso g b f hg M) m).symm := by
    have hh := congrArg (fun a => (frameFactorIso g b f hg (bundleTensorPower M m)).symm ≪≫
      a ≪≫ (tensorPowerIso (frameFactorIso g b f hg M) m).symm) hs
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.symm_self_id_assoc] using hh
  calc
    _ = (frameFactorIso g b f hg (bundleTensorPower M m)).symm ≪≫
        (pullback g).mapIso (tensorPowerPullbackIso b M m) ≪≫
          tensorPowerPullbackIso g ((pullback b).obj M) m ≪≫
            bundleTensorPowerTrivialization ((pullback g).mapIso e ≪≫ pullbackUnitIso g) m := by
      simp only [frameViaFactor, Functor.mapIso_trans, Iso.trans_assoc]
      rw [originalBundleTensorPowerTrivialization_pullback]
    _ = ((frameFactorIso g b f hg (bundleTensorPower M m)).symm ≪≫
        (pullback g).mapIso (tensorPowerPullbackIso b M m) ≪≫
          tensorPowerPullbackIso g ((pullback b).obj M) m) ≪≫
            bundleTensorPowerTrivialization ((pullback g).mapIso e ≪≫ pullbackUnitIso g) m := by
      simp only [Iso.trans_assoc]
    _ = (tensorPowerPullbackIso f M m ≪≫ (tensorPowerIso (frameFactorIso g b f hg M) m).symm) ≪≫
        bundleTensorPowerTrivialization ((pullback g).mapIso e ≪≫ pullbackUnitIso g) m := by rw [hc]
    _ = _ := by
      simp only [frameViaFactor, Iso.trans_assoc]
      rw [← originalTensorPowerIso_symm, originalTensorPowerTrivialization_transport]

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
