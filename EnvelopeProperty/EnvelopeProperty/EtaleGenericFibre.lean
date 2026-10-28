/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

open scoped TensorProduct
noncomputable section
namespace EnvelopeProperty
variable {A R : Type*} [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]

/-- A genuine nonzero principal parameter gives its actual fraction-coefficient localization homomorphism. -/
def fractionAwayHom (a : A) (ha : a ≠ 0) : Localization.Away a →ₐ[A] FractionRing A :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId A (FractionRing A))
    (isUnit_iff_ne_zero.mpr (by
      change algebraMap A (FractionRing A) a ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective A (FractionRing A)).ne ha))

/-- The actual principal-open fraction map retains every original coefficient element. -/
theorem fractionAwayHom_algebraMap (a : A) (ha : a ≠ 0) (x : A) :
    fractionAwayHom a ha (algebraMap A (Localization.Away a) x) = algebraMap A (FractionRing A) x :=
  (fractionAwayHom a ha).commutes x

/-- Actual etaleness after an intermediate base change derives reducedness of the original generic fibre. -/
theorem generic_isReduced_of_etale_baseChange (S : Type*) [CommRing S] [Algebra A S]
    [Algebra S (FractionRing A)] [IsScalarTower A S (FractionRing A)]
    [Algebra.Etale S (S ⊗[A] R)] : IsReduced (FractionRing A ⊗[A] R) := by
  have : IsReduced (FractionRing A ⊗[S] (S ⊗[A] R)) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) _
  let e := Algebra.TensorProduct.cancelBaseChange A S (FractionRing A) (FractionRing A) R
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- A genuine nonzero principal etale open forces the entire original generic fibre to be reduced. -/
theorem generic_isReduced_of_principal_etale (a : A) (ha : a ≠ 0)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[A] R)] :
    IsReduced (FractionRing A ⊗[A] R) := by
  let : Algebra (Localization.Away a) (FractionRing A) := (fractionAwayHom a ha).toRingHom.toAlgebra
  have : IsScalarTower A (Localization.Away a) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => ((fractionAwayHom a ha).commutes x).symm
  exact generic_isReduced_of_etale_baseChange (R := R) (Localization.Away a)

end EnvelopeProperty
