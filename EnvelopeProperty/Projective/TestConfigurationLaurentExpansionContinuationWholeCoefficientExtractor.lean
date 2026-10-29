import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationModelOpenSections

/-! # Actual original unit-open H0 Laurent coefficient extraction -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry NativeTestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- The literal original scalar-adjunction reconstruction; no properness or decomposition input. -/
def originalTestConfigurationUnitPowerLaurentReconstruction (L : X.left.Modules) (m : ℕ) :
    (ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) →+
      originalBaseSections (originalTestConfigurationUnitParameter C)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) :=
  (originalBaseChangeMap X.hom (originalTestConfigurationUnitParameter C)
    (originalTestConfigurationUnitProjection C) (originalTestConfigurationUnitCartesian C).w
    (bundleTensorPower L m)).hom.toAddMonoidHom.comp
      (originalLaurentDomainCoefficients (originalBaseSections X.hom
        (bundleTensorPower L m))).symm.toAddMonoidHom

/-- Invert the proved SAME original whole H0 map and the true Laurent tensor basis. -/
def originalTestConfigurationUnitPowerLaurentCoefficients [IsProper X.hom]
    (L : X.left.Modules) (hL : IsInvertible L) (m : ℕ) :
    originalBaseSections (originalTestConfigurationUnitParameter C)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) ≃+
      (ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :=
  (LinearEquiv.ofBijective
    (originalBaseChangeMap X.hom (originalTestConfigurationUnitParameter C)
      (originalTestConfigurationUnitProjection C) (originalTestConfigurationUnitCartesian C).w
      (bundleTensorPower L m)).hom
    (originalTestConfigurationPowerMap_bijective C L hL m)).toAddEquiv.symm.trans
      (originalLaurentDomainCoefficients (originalBaseSections X.hom (bundleTensorPower L m)))

/-- The actual coefficient inverse IS the SAME original scalar-adjunction reconstruction. -/
theorem originalTestConfigurationUnitPowerLaurentCoefficients_symm [IsProper X.hom]
    (L : X.left.Modules) (hL : IsInvertible L) (m : ℕ)
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :
    (originalTestConfigurationUnitPowerLaurentCoefficients C L hL m).symm c =
      originalTestConfigurationUnitPowerLaurentReconstruction C L m c := rfl

/-- The named native reconstruction retains the literal monomials and original pullback sections. -/
theorem originalTestConfigurationUnitPowerLaurentReconstruction_apply
    (L : X.left.Modules) (m : ℕ)
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :
    originalTestConfigurationUnitPowerLaurentReconstruction C L m c =
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
          affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a)) :=
  originalBaseChangeMap_laurent_reconstruction X.hom (originalTestConfigurationUnitParameter C)
    (originalTestConfigurationUnitProjection C) (originalTestConfigurationUnitCartesian C).w
    (bundleTensorPower L m) c

/-- Every actual original unit-open whole section is reconstructed by its derived finite coefficients. -/
theorem originalTestConfigurationUnitPowerLaurentCoefficients_reconstruct [IsProper X.hom]
    (L : X.left.Modules) (hL : IsInvertible L) (m : ℕ)
    (s : originalBaseSections (originalTestConfigurationUnitParameter C)
      ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m))) :
    originalTestConfigurationUnitPowerLaurentReconstruction C L m
      (originalTestConfigurationUnitPowerLaurentCoefficients C L hL m s) = s :=
  (originalTestConfigurationUnitPowerLaurentCoefficients C L hL m).symm_apply_apply s

/-- Actual finite reconstruction is equivalent to equality with the actual extracted family. -/
theorem originalTestConfigurationUnitPowerLaurentReconstruction_eq_iff [IsProper X.hom]
    (L : X.left.Modules) (hL : IsInvertible L) (m : ℕ)
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m))
    (s : originalBaseSections (originalTestConfigurationUnitParameter C)
      ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m))) :
    originalTestConfigurationUnitPowerLaurentReconstruction C L m c = s ↔
      c = originalTestConfigurationUnitPowerLaurentCoefficients C L hL m s :=
  (originalTestConfigurationUnitPowerLaurentCoefficients C L hL m).symm_apply_eq

section OriginalWholeModel
variable (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)

/-- Actual original total section restriction followed by the source-derived polarization transport. -/
def originalTestConfigurationWholePowerUnitSection :
    Γ(bundleTensorPower M m, ⊤) →+
      originalBaseSections (originalTestConfigurationUnitParameter C)
        ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) :=
  (originalTestConfigurationModelPowerSectionsIso C M L linearization
    fibreOneIdentification m).hom.hom.toAddMonoidHom.comp
      (pullbackTopRestrictMap C.unitOpen.ι (bundleTensorPower M m)).hom.toAddMonoidHom

/-- The actual additive map has exactly the original adjunction-unit section value. -/
theorem originalTestConfigurationWholePowerUnitSection_apply
    (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationWholePowerUnitSection C M L linearization fibreOneIdentification m s =
      (originalTestConfigurationModelPowerSectionsIso C M L linearization fibreOneIdentification m).hom
        (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s) := by
  exact congrArg (fun z => (originalTestConfigurationModelPowerSectionsIso C M L linearization
    fibreOneIdentification m).hom z)
    (pullbackTopRestrictMap_apply C.unitOpen.ι (bundleTensorPower M m) s)

/-- An actual additive finite Laurent coefficient extractor for EVERY original whole model-power section. -/
def originalTestConfigurationWholePowerLaurentCoefficients [IsProper X.hom] (hL : IsInvertible L) :
    Γ(bundleTensorPower M m, ⊤) →+
      (ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :=
  (originalTestConfigurationUnitPowerLaurentCoefficients C L hL m).toAddMonoidHom.comp
    (originalTestConfigurationWholePowerUnitSection C M L linearization fibreOneIdentification m)

/-- The actual extracted original whole family reconstructs its SAME genuine unit-open section. -/
theorem originalTestConfigurationWholePowerLaurentCoefficients_reconstruct
    [IsProper X.hom] (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤)) :
    originalTestConfigurationUnitPowerLaurentReconstruction C L m
      (originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
        fibreOneIdentification m hL s) =
      originalTestConfigurationWholePowerUnitSection C M L linearization fibreOneIdentification m s :=
  originalTestConfigurationUnitPowerLaurentCoefficients_reconstruct C L hL m _

/-- Original reconstruction uniquely determines the actual extracted family; no total restriction injectivity. -/
theorem originalTestConfigurationWholePowerLaurentCoefficients_eq_iff
    [IsProper X.hom] (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤))
    (c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m)) :
    originalTestConfigurationUnitPowerLaurentReconstruction C L m c =
        originalTestConfigurationWholePowerUnitSection C M L linearization fibreOneIdentification m s ↔
      c = originalTestConfigurationWholePowerLaurentCoefficients C M L linearization
        fibreOneIdentification m hL s :=
  originalTestConfigurationUnitPowerLaurentReconstruction_eq_iff C L hL m c _

end OriginalWholeModel
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
