import EnvelopeProperty.Berkovich.SchemeInducedPowerFrames
import EnvelopeProperty.Berkovich.SchemeSupportLineFrames

/-! # Actual original support and local pullback frames have compatible whole powers -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeSupportPowerFrames
open CanonicalGeometry BundleTensorPowerPullback SchemePulledPowerFrames SchemeSupportLineFrames
open SchemeInducedPowerFrames SchemeLineSectionEvaluation

/-- The actual original support lift transports ALL actual original open power frames. -/
theorem supportGenericFrame_power {X : Scheme.{u}} (y : X) (U : X.Opens) (hy : y ∈ U)
    {M : X.Modules} (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) (n : ℕ) :
    supportGenericFrame y U hy (pullbackPowerFrame U.ι e n) =
      pullbackPowerFrame (X.fromSpecResidueField y) (supportGenericFrame y U hy e) n :=
  pullbackPowerFrame_factor (supportGenericFactor y U hy) U.ι (X.fromSpecResidueField y)
    (supportGenericFactor_comp y U hy) e n

/-- The actual original restriction square derives the WHOLE local pullback power frame. -/
theorem localPullbackFrame_power {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) (n : ℕ) :
    localPullbackFrame f U (pullbackPowerFrame U.ι e n) =
      (pullback (f ⁻¹ᵁ U).ι).mapIso (pullbackIso f M n) ≪≫
        pullbackPowerFrame (f ⁻¹ᵁ U).ι (localPullbackFrame f U e) n :=
  factorPowerFrame_comp (f ⁻¹ᵁ U).ι f (f ∣_ U) U.ι (morphismRestrict_ι f U) e n

/-- SAME original support/local frame in every degree, with the ACTUAL common native power comparison. -/
theorem supportGenericFrame_localPullbackPower {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (U : X.Opens) (hy : y ∈ f ⁻¹ᵁ U) {M : X.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) (n : ℕ) :
    supportGenericFrame y (f ⁻¹ᵁ U) hy (localPullbackFrame f U (pullbackPowerFrame U.ι e n)) =
      (pullback (Y.fromSpecResidueField y)).mapIso (pullbackIso f M n) ≪≫
        pullbackPowerFrame (Y.fromSpecResidueField y)
          (supportGenericFrame y (f ⁻¹ᵁ U) hy (localPullbackFrame f U e)) n := by
  have hl := congrArg (fun E => supportGenericFrame y (f ⁻¹ᵁ U) hy E)
    (localPullbackFrame_power f U e n)
  have hn := frameViaFactor_naturality (supportGenericFactor y (f ⁻¹ᵁ U) hy)
    (f ⁻¹ᵁ U).ι (Y.fromSpecResidueField y) (supportGenericFactor_comp y (f ⁻¹ᵁ U) hy)
    (pullbackIso f M n) (pullbackPowerFrame (f ⁻¹ᵁ U).ι (localPullbackFrame f U e) n)
  have hp := congrArg (fun E => (pullback (Y.fromSpecResidueField y)).mapIso (pullbackIso f M n) ≪≫ E)
    (supportGenericFrame_power y (f ⁻¹ᵁ U) hy (localPullbackFrame f U e) n)
  exact hl.trans (hn.trans hp)

end EnvelopeProperty.Berkovich.SchemeSupportPowerFrames
