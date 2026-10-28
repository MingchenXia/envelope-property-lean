import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationNatural

/-! # Actual finite original twist transitions under native affine-frame pullback

Both actual original transitions read back to the SAME original section
coefficient in the actual pulled frame. Cancelling that genuine frame
proves the WHOLE transition square, not a supplied compatibility premise.
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
private noncomputable instance transitionPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

private theorem pulledTwistFrame_factor {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F L : X.Modules) (e : (pullback g).obj L ≅ unitObj Y) (m : ℕ) :
    (Functor.Monoidal.μIso (pullback g) F (bundleTensorPower L m)).inv ≫
      (tensorFrameIso ((pullback g).obj F)
        (SchemePulledPowerFrames.pullbackPowerFrame g e m)).hom =
    (twistPullbackIso g F L m).hom ≫
      (tensorFrameIso ((pullback g).obj F) (SchemeTensorPowerFrames.powerFrame e m)).hom := by
  simp only [tensorFrameIso, SchemePulledPowerFrames.pullbackPowerFrame,
    twistPullbackIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    id_tensorHom, whiskerLeft_comp, Category.assoc]

private theorem twistStep_pullback_of_frame {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F L : X.Modules) (s : unitObj X ⟶ L)
    (e : (pullback g).obj L ≅ unitObj Y) (m : ℕ) :
    (pullback g).map (twistStep F L s m) ≫ (twistPullbackIso g F L (m + 1)).hom =
      (twistPullbackIso g F L m).hom ≫
        twistStep ((pullback g).obj F) ((pullback g).obj L) (pullbackSectionHom g s) m := by
  have h := twistStep_pullback_frame g F L s e m
  rw [pulledTwistFrame_factor, pulledTwistFrame_factor] at h
  apply (cancel_mono
    (tensorFrameIso ((pullback g).obj F) (SchemeTensorPowerFrames.powerFrame e (m + 1))).hom).mp
  simpa only [Category.assoc, twistStep_frame] using h

/-- Every finite SAME original section transition commutes with actual
native pullback and actual original power-twist comparison, in an ordinary
geometric pulled line frame. Every matching equation is derived internally. -/
theorem twistIterate_pullback_of_frame {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F L : X.Modules) (s : unitObj X ⟶ L)
    (e : (pullback g).obj L ≅ unitObj Y) (m a : ℕ) :
    (pullback g).map (twistIterate F L s m a) ≫ (twistPullbackIso g F L (m + a)).hom =
      (twistPullbackIso g F L m).hom ≫
        twistIterate ((pullback g).obj F) ((pullback g).obj L) (pullbackSectionHom g s) m a := by
  induction a with
  | zero =>
    rw [twistIterate, twistIterate, (pullback g).map_id, Category.id_comp, Category.comp_id]
    rfl
  | succ a ih =>
    change (pullback g).map (twistIterate F L s m a ≫ twistStep F L s (m + a)) ≫
      (twistPullbackIso g F L ((m + a) + 1)).hom =
      (twistPullbackIso g F L m).hom ≫
        (twistIterate ((pullback g).obj F) ((pullback g).obj L) (pullbackSectionHom g s) m a ≫
          twistStep ((pullback g).obj F) ((pullback g).obj L) (pullbackSectionHom g s) (m + a))
    rw [Functor.map_comp, Category.assoc, twistStep_pullback_of_frame g F L s e]
    rw [← Category.assoc, ih]
    simp only [Category.assoc]

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
