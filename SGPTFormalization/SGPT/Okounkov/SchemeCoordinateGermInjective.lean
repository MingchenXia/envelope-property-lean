import SGPT.Okounkov.SchemeCoordinateEtale
import SGPT.Okounkov.SchemeCoordinateStalkGerm
import TranscendentalNakamaye.Pending.HolomorphicZeroSetThin
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The actual integral-scheme stalk embeds in the chosen analytic germs

The SAME etale polynomial coordinates and their proved germ faithfulness
manufacture a generic-coordinate base-change field. Its actual localization
map into the analytic fraction field is injective, forcing the actual
affine/local/stalk germ maps to be injective. The extra hypothesis is the
actual original scheme's integrality, not a comparison certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy RingHom
open TranscendentalNakamaye.Pending
open scoped TensorProduct

/-- A faithful composite over an etale domain forces the whole map to be faithful.
The proof uses the actual generic base-change localization and its manufactured
finite-dimensional field structure. -/
private theorem injective_of_etale_faithful_composite
    {B A R : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [CommRing R] [IsDomain R] [Algebra B A] [Algebra.Etale B A]
    (γ : A →+* R) (hγβ : Function.Injective (γ.comp (algebraMap B A))) :
    Function.Injective γ := by
  let K := FractionRing B
  let H := FractionRing R
  let S := K ⊗[B] A
  let : Algebra A S := Algebra.TensorProduct.rightAlgebra
  let M : Submonoid A := Algebra.algebraMapSubmonoid A (nonZeroDivisors B)
  let : IsLocalization M S := IsLocalization.tensorRight (R := B) (S := A) (A := K)
    (nonZeroDivisors B)
  have hβ : Function.Injective (algebraMap B A) := by
    intro a b hab
    exact hγβ (congrArg γ hab)
  have hM : M ≤ nonZeroDivisors A := by
    rintro a ⟨b, hb, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact hβ (by simpa only [map_zero] using hzero)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  have hA : Function.Injective (algebraMap A S) := IsLocalization.injective S hM
  let : Algebra.Etale K S := inferInstance
  let : Module.Finite K S := Algebra.FormallyUnramified.finite_of_free K S
  let : Field S := fieldOfFiniteDimensional K S
  let γH : A →+* H := (algebraMap R H).comp γ
  have hUnits : ∀ s : M, IsUnit (γH s) := by
    rintro ⟨a, b, hb, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    change algebraMap R H (γ (algebraMap B A b)) ≠ 0
    intro hzero
    have hGerm : γ (algebraMap B A b) = 0 :=
      IsFractionRing.injective R H (by simpa only [map_zero] using hzero)
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact hγβ (by simpa only [RingHom.comp_apply, map_zero] using hGerm)
  let g : S →+* H := IsLocalization.lift (S := S) (g := γH) hUnits
  have hRestriction : g.comp (algebraMap A S) = γH := IsLocalization.lift_comp hUnits
  have hγH : Function.Injective γH := by
    rw [← hRestriction]
    exact g.injective.comp hA
  intro a b hab
  apply hγH
  exact congrArg (algebraMap R H) hab

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) [IsIntegral X]

local instance injectiveCoordinateComplexAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual integral source and genuine nonempty affine open produce
the actual original affine coordinate domain. -/
theorem schemeCoordinateAffineRing_isDomain : IsDomain (SchemeCoordinateAffineRing f n p) := by
  let : Nonempty (Spec (SchemeCoordinateAffineRing f n p)) :=
    ⟨schemeCoordinateAlgebraicPoint f n p⟩
  let : IsIntegral (Spec (SchemeCoordinateAffineRing f n p)) :=
    isIntegral_of_isOpenImmersion (standardSmoothComplexAffineChart f n p).val.map
  exact (affine_isIntegral_iff (SchemeCoordinateAffineRing f n p)).mp inferInstance

/-- Actual integral geometry and SAME-coordinate etaleness manufacture full
affine regular-germ injectivity; polynomial faithfulness alone is not assumed
to imply this conclusion. -/
theorem schemeCoordinateRegularGerm_injective :
    Function.Injective (schemeCoordinateRegularGerm f n p) := by
  let : IsDomain (SchemeCoordinateAffineRing f n p) :=
    schemeCoordinateAffineRing_isDomain f n p
  let : Algebra (MvPolynomial (Fin n) ℂ) (SchemeCoordinateAffineRing f n p) :=
    (schemeCoordinatePolynomialMap f n p).toRingHom.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) ℂ) (SchemeCoordinateAffineRing f n p) :=
    etale_algebraMap.mp (schemeCoordinatePolynomialMap_etale f n p)
  exact injective_of_etale_faithful_composite (schemeCoordinateRegularGerm f n p)
    (schemeCoordinatePolynomialGerm_injective f n p)

/-- Genuine fraction representations and the actual affine injection force
the manufactured original affine-local map to be injective. -/
theorem schemeCoordinateLocalRegularGerm_injective :
    Function.Injective (schemeCoordinateLocalRegularGerm f n p) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := (schemeCoordinatePointIdeal f n p).primeCompl) (SchemeCoordinateLocalRing f n p)
    (schemeCoordinateLocalRegularGerm f n p)
  intro a ha
  rw [schemeCoordinateLocalRegularGerm_algebraMap] at ha
  have ha0 : a = 0 := schemeCoordinateRegularGerm_injective f n p
    (by simpa only [map_zero] using ha)
  rw [ha0, map_zero]

/-- The produced map from the actual ORIGINAL scheme stalk is injective. -/
theorem schemeCoordinateStalkRegularGerm_injective :
    Function.Injective (schemeCoordinateStalkRegularGerm f n p) :=
  (schemeCoordinateLocalRegularGerm_injective f n p).comp (schemeCoordinateStalkEquiv f n p).symm.injective

end SGPT.Okounkov
