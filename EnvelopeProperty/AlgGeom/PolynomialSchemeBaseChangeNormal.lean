/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AffineGlobalSections
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # The actual polynomial-base-change rings and stalks of original affine schemes -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Polynomial TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.PolynomialSchemeBaseChangeNormal
open FlatGlobalSections
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsAffine X]

/-- The SAME original polynomial-base-change global ring is the polynomial
ring of the SAME original affine global ring, with no flatness premise. -/
def affinePolynomialSectionsEquiv :
    Γ(X, ⊤)[X] ≃+* Γ(baseChange (S := R[X]) p, ⊤) := by
  let _ : Algebra R Γ(X, ⊤) := sectionsAlgebra p
  let _ : Algebra R[X] Γ(baseChange (S := R[X]) p, ⊤) :=
    sectionsAlgebra (structureMap (S := R[X]) p)
  exact (polyEquivTensor R Γ(X, ⊤)).toRingEquiv.trans
    ((Algebra.TensorProduct.comm R Γ(X, ⊤) R[X]).toRingEquiv.trans
      (AffineGlobalSections.tensorEquiv (S := R[X]) p).toRingEquiv)

/-- The ACTUAL original polynomial-base-change affine global ring is a domain
if the original affine global ring is a domain. -/
theorem affinePolynomialSections_isDomain [IsDomain Γ(X, ⊤)] :
    IsDomain Γ(baseChange (S := R[X]) p, ⊤) :=
  Function.Injective.isDomain (affinePolynomialSectionsEquiv p).symm
    (affinePolynomialSectionsEquiv p).symm.injective

/-- Actual polynomial normality gives integral closedness of the SAME
original polynomial-base-change affine global ring. -/
theorem affinePolynomialSections_isIntegrallyClosed [IsDomain Γ(X, ⊤)]
    [IsIntegrallyClosed Γ(X, ⊤)] : IsIntegrallyClosed Γ(baseChange (S := R[X]) p, ⊤) :=
  IsIntegrallyClosed.of_equiv (affinePolynomialSectionsEquiv p)

-- The following actual affine-stalk localization comparison is the Mathlib-only
-- construction also used in ComplexSchemes.NativeAffineLineNormality.
private def affineStalkLocalizationEquiv (Y : Scheme.{u}) [IsAffine Y] (x : Y) :
    Localization.AtPrime ((Y.isoSpec.hom x).asIdeal) ≃+* Y.presheaf.stalk x :=
  ((Spec.stalkIso (.of Γ(Y, ⊤)) (Y.isoSpec.hom x)).symm ≪≫
    asIso (Y.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- EVERY actual original polynomial-base-change affine stalk is a domain,
using its genuine original global-ring prime localization. -/
theorem affinePolynomial_stalk_isDomain [IsDomain Γ(X, ⊤)]
    (x : baseChange (S := R[X]) p) : IsDomain ((baseChange (S := R[X]) p).presheaf.stalk x) := by
  let := affinePolynomialSections_isDomain p
  exact Function.Injective.isDomain (affineStalkLocalizationEquiv _ x).symm
    (affineStalkLocalizationEquiv _ x).symm.injective

/-- EVERY actual original polynomial-base-change affine stalk is integrally
closed under the original affine-ring normality premise. -/
theorem affinePolynomial_stalk_isIntegrallyClosed [IsDomain Γ(X, ⊤)]
    [IsIntegrallyClosed Γ(X, ⊤)] (x : baseChange (S := R[X]) p) :
    IsIntegrallyClosed ((baseChange (S := R[X]) p).presheaf.stalk x) := by
  let := affinePolynomialSections_isDomain p
  let := affinePolynomialSections_isIntegrallyClosed p
  let q := (baseChange (S := R[X]) p).isoSpec.hom x
  have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (affineStalkLocalizationEquiv _ x)

end EnvelopeProperty.PolynomialSchemeBaseChangeNormal
