import SGPT.Okounkov.SchemeCoordinateRegularGerm
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The actual affine local algebra in the same chosen coordinate germ

The original affine evaluation kernel is a genuine maximal ideal. Its
complement maps to actual units by the proved evaluation identity, so the
native localization universal property constructs the local germ map.
No injectivity or global function-field premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.Pending
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The ideal is the kernel of the SAME internally produced affine point. -/
def schemeCoordinatePointIdeal : Ideal (SchemeCoordinateAffineRing f n p) :=
  RingHom.ker (standardSmoothComplexAlgebraPoint f n p).toRingHom

theorem schemeCoordinatePointIdeal_mem (a : SchemeCoordinateAffineRing f n p) :
    a ∈ schemeCoordinatePointIdeal f n p ↔
      standardSmoothComplexAlgebraPoint f n p a = 0 := Iff.rfl

/-- Actual structural scalars make the actual affine point surjective. -/
theorem schemeCoordinatePointIdeal_isMaximal :
    (schemeCoordinatePointIdeal f n p).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap ℂ (SchemeCoordinateAffineRing f n p) c,
    (standardSmoothComplexAlgebraPoint f n p).commutes c⟩

instance schemeCoordinatePointIdeal_isPrime :
    (schemeCoordinatePointIdeal f n p).IsPrime :=
  (schemeCoordinatePointIdeal_isMaximal f n p).isPrime

/-- The actual prime localization of the SAME original affine coordinate ring. -/
abbrev SchemeCoordinateLocalRing := Localization.AtPrime (schemeCoordinatePointIdeal f n p)

private theorem schemeCoordinateRegularGerm_denominator_unit
    (s : (schemeCoordinatePointIdeal f n p).primeCompl) :
    IsUnit (schemeCoordinateRegularGerm f n p s) := by
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  rw [schemeCoordinateRegularGerm_eval]
  exact s.property

/-- The local ring map is manufactured by actual denominator units. -/
def schemeCoordinateLocalRegularGerm :
    SchemeCoordinateLocalRing f n p →+* HolGerm (Fin n → ℂ) :=
  IsLocalization.lift (S := SchemeCoordinateLocalRing f n p)
    (g := schemeCoordinateRegularGerm f n p)
    (schemeCoordinateRegularGerm_denominator_unit f n p)

/-- The entire produced local map restricts to the original regular germ map. -/
theorem schemeCoordinateLocalRegularGerm_algebraMap
    (a : SchemeCoordinateAffineRing f n p) :
    schemeCoordinateLocalRegularGerm f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p) a) =
        schemeCoordinateRegularGerm f n p a :=
  IsLocalization.lift_eq (schemeCoordinateRegularGerm_denominator_unit f n p) a

/-- Actual fractions have their literal original scalar residue evaluations. -/
theorem schemeCoordinateLocalRegularGerm_eval_mk'
    (a : SchemeCoordinateAffineRing f n p)
    (s : (schemeCoordinatePointIdeal f n p).primeCompl) :
    HolGerm.eval (schemeCoordinateLocalRegularGerm f n p
      (IsLocalization.mk' (SchemeCoordinateLocalRing f n p) a s)) =
        standardSmoothComplexAlgebraPoint f n p a /
          standardSmoothComplexAlgebraPoint f n p s := by
  have h := congrArg (schemeCoordinateLocalRegularGerm f n p)
    (IsLocalization.mk'_spec (SchemeCoordinateLocalRing f n p) a s)
  rw [map_mul, schemeCoordinateLocalRegularGerm_algebraMap,
    schemeCoordinateLocalRegularGerm_algebraMap] at h
  have hev := congrArg (HolGerm.eval : HolGerm (Fin n → ℂ) →+* ℂ) h
  rw [map_mul, schemeCoordinateRegularGerm_eval, schemeCoordinateRegularGerm_eval] at hev
  exact (eq_div_iff s.property).mpr hev

/-- The exact maximal-ideal readback is derived for EVERY actual local element. -/
theorem schemeCoordinateLocalRegularGerm_mem_maximal_iff
    (a : SchemeCoordinateLocalRing f n p) :
    schemeCoordinateLocalRegularGerm f n p a ∈
        IsLocalRing.maximalIdeal (HolGerm (Fin n → ℂ)) ↔
      a ∈ IsLocalRing.maximalIdeal (SchemeCoordinateLocalRing f n p) := by
  obtain ⟨r, s, rfl⟩ :=
    IsLocalization.exists_mk'_eq (schemeCoordinatePointIdeal f n p).primeCompl a
  rw [HolGerm.mem_maximalIdeal_iff, schemeCoordinateLocalRegularGerm_eval_mk',
    IsLocalization.AtPrime.mk'_mem_maximal_iff (SchemeCoordinateLocalRing f n p)
      (schemeCoordinatePointIdeal f n p) r s]
  have hs : standardSmoothComplexAlgebraPoint f n p s ≠ 0 := s.property
  simp only [div_eq_zero_iff, hs, or_false, schemeCoordinatePointIdeal_mem]

/-- The manufactured map is actually a local ring homomorphism. -/
instance schemeCoordinateLocalRegularGerm_isLocalHom :
    IsLocalHom (schemeCoordinateLocalRegularGerm f n p) where
  map_nonunit a ha := by
    by_contra hn
    have hm : a ∈ IsLocalRing.maximalIdeal (SchemeCoordinateLocalRing f n p) := hn
    exact ((schemeCoordinateLocalRegularGerm_mem_maximal_iff f n p a).mpr hm) ha

end SGPT.Okounkov
