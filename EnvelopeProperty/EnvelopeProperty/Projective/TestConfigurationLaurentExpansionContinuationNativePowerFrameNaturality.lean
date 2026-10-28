import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussExtractedModelNorm
import EnvelopeProperty.AlgGeom.CartierTensorPullbackNaturality

/-! # Actual native tensor powers, pullback naturality and source-derived polarization frames -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Genuine native powers preserve the identity at EVERY degree including zero. -/
theorem originalTensorPowerIso_refl {Y : Scheme.{u}} (M : Y.Modules) (m : ℕ) :
    tensorPowerIso (Iso.refl M) m = Iso.refl (bundleTensorPower M m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change tensorObjCongr (tensorPowerIso (Iso.refl M) m) (Iso.refl M) = Iso.refl _
    rw [ih]
    exact tensorObjCongr_refl _ _

/-- Genuine native powers preserve actual original whole module-iso composition. -/
theorem originalTensorPowerIso_trans {Y : Scheme.{u}} {M N P : Y.Modules}
    (e : M ≅ N) (f : N ≅ P) (m : ℕ) :
    tensorPowerIso (e ≪≫ f) m = tensorPowerIso e m ≪≫ tensorPowerIso f m := by
  induction m with
  | zero => exact (Iso.refl_trans _).symm
  | succ m ih =>
    change tensorObjCongr (tensorPowerIso (e ≪≫ f) m) (e ≪≫ f) =
      tensorObjCongr (tensorPowerIso e m) e ≪≫ tensorObjCongr (tensorPowerIso f m) f
    rw [ih]
    exact tensorObjCongr_trans _ _ _ _

/-- Actual all-power pullback comparison is natural in the actual original whole module iso. -/
theorem originalTensorPowerPullbackIso_natural {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : Z.Modules} (e : M ≅ N) (m : ℕ) :
    (pullback f).mapIso (tensorPowerIso e m) ≪≫ tensorPowerPullbackIso f N m =
      tensorPowerPullbackIso f M m ≪≫ tensorPowerIso ((pullback f).mapIso e) m := by
  induction m with
  | zero => simp only [tensorPowerIso, tensorPowerPullbackIso, Functor.mapIso_refl,
      Iso.refl_trans, Iso.trans_refl]
  | succ m ih =>
    change (pullback f).mapIso (tensorObjCongr (tensorPowerIso e m) e) ≪≫
        (canonicalTensorPullbackIso f (bundleTensorPower N m) N ≪≫
          tensorObjCongr (tensorPowerPullbackIso f N m) (Iso.refl _)) =
      (canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
        tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl _)) ≪≫
          tensorObjCongr (tensorPowerIso ((pullback f).mapIso e) m) ((pullback f).mapIso e)
    have ht := tensorObjCongr_trans (tensorPowerPullbackIso f M m)
      (tensorPowerIso ((pullback f).mapIso e) m) (Iso.refl ((pullback f).obj M))
      ((pullback f).mapIso e)
    calc
      _ = canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
          tensorObjCongr ((pullback f).mapIso (tensorPowerIso e m) ≪≫ tensorPowerPullbackIso f N m)
            ((pullback f).mapIso e ≪≫ Iso.refl _) := by
        rw [← Iso.trans_assoc, canonicalTensorPullbackIso_natural]
        simp only [Iso.trans_assoc, tensorObjCongr_trans]
      _ = canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
          tensorObjCongr (tensorPowerPullbackIso f M m ≪≫ tensorPowerIso ((pullback f).mapIso e) m)
            ((pullback f).mapIso e) := by rw [ih, Iso.trans_refl]
      _ = _ := by
        rw [show tensorObjCongr
            (tensorPowerPullbackIso f M m ≪≫ tensorPowerIso ((pullback f).mapIso e) m)
            ((pullback f).mapIso e) =
          tensorObjCongr (tensorPowerPullbackIso f M m) (Iso.refl ((pullback f).obj M)) ≪≫
            tensorObjCongr (tensorPowerIso ((pullback f).mapIso e) m) ((pullback f).mapIso e) from
          by simpa only [Iso.refl_trans] using ht]
        exact (Iso.trans_assoc _ _ _).symm

/-- Actual power-frame trivializations transport through the genuine original module iso. -/
theorem originalTensorPowerTrivialization_transport {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (d : N ≅ unitObj Y) (m : ℕ) :
    tensorPowerIso e m ≪≫ bundleTensorPowerTrivialization d m =
      bundleTensorPowerTrivialization (e ≪≫ d) m := by
  induction m with
  | zero => exact Iso.refl_trans _
  | succ m ih =>
    change tensorObjCongr (tensorPowerIso e m) e ≪≫
        (tensorObjCongr (bundleTensorPowerTrivialization d m) d ≪≫ bundleTensorLeftUnitIso (unitObj Y)) =
      tensorObjCongr (bundleTensorPowerTrivialization (e ≪≫ d) m) (e ≪≫ d) ≪≫
        bundleTensorLeftUnitIso (unitObj Y)
    rw [← Iso.trans_assoc, ← tensorObjCongr_trans, ih]

/-- The TRUE polarization power iso takes actual frames to the powers of its actual degree-one frame. -/
theorem originalPolarizationPowerIso_frame {Y Z V : Scheme.{u}}
    (j : V ⟶ Y) (p : V ⟶ Z) (M : Y.Modules) (L : Z.Modules)
    (σ : (pullback j).obj M ≅ (pullback p).obj L)
    (e : (pullback p).obj L ≅ unitObj V) (m : ℕ) :
    polarizationPowerIso j p M L σ m ≪≫ tensorPowerPullbackIso p L m ≪≫
        bundleTensorPowerTrivialization e m =
      tensorPowerPullbackIso j M m ≪≫ bundleTensorPowerTrivialization (σ ≪≫ e) m := by
  simp only [polarizationPowerIso, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [originalTensorPowerTrivialization_transport]

/-- Original action/fibre-one data INTERNALLY derive sigma_m and its actual ALL-degree power-frame law. -/
theorem originalTestConfigurationModelPowerUnitIso_frame
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : NativeTestConfiguration.TestConfiguration k X) (M : C.total.Modules) (L : X.left.Modules)
    (linearization :
      (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (pullback (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
    (fibreOneIdentification :
      (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (e : (pullback (originalTestConfigurationUnitProjection C)).obj L ≅ unitObj C.unitOpen.toScheme)
    (m : ℕ) :
    originalTestConfigurationModelPowerUnitIso C M L linearization fibreOneIdentification m ≪≫
        tensorPowerPullbackIso (originalTestConfigurationUnitProjection C) L m ≪≫
          bundleTensorPowerTrivialization e m =
      tensorPowerPullbackIso C.unitOpen.ι M m ≪≫
        bundleTensorPowerTrivialization
          (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification ≪≫ e) m :=
  originalPolarizationPowerIso_frame C.unitOpen.ι (originalTestConfigurationUnitProjection C) M L
    (originalTestConfigurationPolarizationUnitIso C M L linearization fibreOneIdentification) e m

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
