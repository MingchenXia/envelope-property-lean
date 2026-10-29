import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationWholeReconstruction
import EnvelopeProperty.Projective.TestConfigurationSectionTransport
import EnvelopeProperty.Global.NativeTestConfigurationUnitFibre

/-! # Actual original test-configuration unit-open Laurent square and powers

The original native test configuration derives its actual Cartesian Laurent
square from the proved original whole trivialization and original parameter.
Every actual pullback of an original line-bundle power has unique finite
original Laurent coefficients. Identifying the original total-model
polarization with these pullbacks remains a genuine separate consumer.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- The first original coordinate of the internally proved SAME whole
unit-open trivialization, on the actual original noncentral scheme. -/
def originalTestConfigurationUnitProjection : C.unitOpen.toScheme ⟶ X.left :=
  (C.unitOpenIso.hom ≫ fst X (ProjBerk.nativeMultiplicativeGroup k)).left

/-- The SAME original Laurent parameter, through the proved native
group-pullback/unit-open identification. -/
def originalTestConfigurationUnitParameter :
    C.unitOpen.toScheme ⟶ Spec (CommRingCat.of k[T;T⁻¹]) :=
  (C.groupPullbackOpenIso.inv ≫ C.groupPullbackParameter).left

/-- The proved original trivialization retains exactly the SAME original
Laurent parameter on the entire original noncentral scheme. -/
theorem originalTestConfigurationUnitParameter_eq :
    (C.unitOpenIso.hom ≫ snd X (ProjBerk.nativeMultiplicativeGroup k)).left =
      originalTestConfigurationUnitParameter C :=
  congrArg (fun a : C.unitOpenOver ⟶ ProjBerk.nativeMultiplicativeGroup k => a.left)
    (NativeTestConfiguration.TestConfiguration.unitOpenIso_parameter C)

/-- The original test configuration DERIVES its actual original unit-open
Cartesian Laurent square; no square or scheme comparison is an input. -/
theorem originalTestConfigurationUnitCartesian :
    IsPullback (originalTestConfigurationUnitProjection C)
      (originalTestConfigurationUnitParameter C) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k k[T;T⁻¹]))) := by
  let G := ProjBerk.nativeMultiplicativeGroup k
  have hp : IsPullback (fst X G).left (snd X G).left X.hom G.hom := by
    exact Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct X G)
  let e := (Over.forget (Spec (CommRingCat.of k))).mapIso C.unitOpenIso
  refine hp.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rfl
  · change (C.unitOpenIso.hom ≫ snd X (ProjBerk.nativeMultiplicativeGroup k)).left =
      originalTestConfigurationUnitParameter C
    exact originalTestConfigurationUnitParameter_eq C
  · rfl
  · rfl

/-- Every SAME original tensor power has its genuine original whole-map
bijection on the actual original unit open, with no H0 comparison input. -/
theorem originalTestConfigurationPowerMap_bijective [IsProper X.hom]
    (L : X.left.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    Function.Bijective (originalBaseChangeMap X.hom
      (originalTestConfigurationUnitParameter C) (originalTestConfigurationUnitProjection C)
      (originalTestConfigurationUnitCartesian C).w (bundleTensorPower L m)) := by
  let : (bundleTensorPower L m).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).isQuasicoherent
  exact originalBaseChangeMap_bijective_of_isProper X.hom
    (originalTestConfigurationUnitParameter C) (originalTestConfigurationUnitProjection C)
    (originalTestConfigurationUnitCartesian C) (bundleTensorPower L m)

/-- EVERY section of EVERY original power's actual unit-open pullback has
UNIQUE finite ORIGINAL whole Laurent coefficients and literal reconstruction.
This does not identify the original total-model polarization with that pullback. -/
theorem exists_unique_original_testConfiguration_unit_power_laurent_expansion
    [IsProper X.hom] (L : X.left.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (s : originalBaseSections (originalTestConfigurationUnitParameter C)
      ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
        (bundleTensorPower L m))) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
              (bundleTensorPower L m)) from
          affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
            (bundleTensorPower L m) a)) = s := by
  let : (bundleTensorPower L m).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).isQuasicoherent
  exact exists_unique_original_whole_laurent_expansion_of_isProper X.hom
    (originalTestConfigurationUnitParameter C) (originalTestConfigurationUnitProjection C)
    (originalTestConfigurationUnitCartesian C) (bundleTensorPower L m) s

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
