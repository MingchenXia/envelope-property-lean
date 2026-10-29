/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.RegularNormal
import EnvelopeProperty.Char0.EtaleSourceInputs
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular

/-!
# Normality derived from the actual etale coordinate map

No normality, factoriality, equicharacteristic regularity or local
normality hypothesis is supplied for the coordinate domain.
-/

noncomputable section

namespace EnvelopeProperty.Char0

universe u

variable {k E : Type u} [Field k] [CommRing E] [Algebra k E] {n : ℕ}

/-- The actual etale coordinate map makes every prime localization regular local. -/
theorem isRegularRing_of_etale_coordinates (v : Fin n → E)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) : IsRegularRing E := by
  let _ := (MvPolynomial.aeval (R := k) v).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) E :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval v).commutes c).symm
  have : Algebra.Etale (MvPolynomial (Fin n) k) E := hv.toAlgebra
  have : Algebra.Smooth k (MvPolynomial (Fin n) k) := {}
  have : Algebra.Smooth k E := Algebra.Smooth.comp k (MvPolynomial (Fin n) k) E
  let := finiteType_of_etale_coordinates v hv
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  apply (isRegularRing_iff).mpr
  intro P hP
  exact Algebra.IsSmoothAt.isRegularLocalRing (k := k) P

/-- An actual domain equipped with actual etale coordinates is integrally closed;
normality is produced from that coordinate map in arbitrary dimension. -/
theorem isIntegrallyClosed_of_etale_coordinates [IsDomain E] (v : Fin n → E)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) : IsIntegrallyClosed E := by
  let := isRegularRing_of_etale_coordinates v hv
  exact EnvelopeProperty.isIntegrallyClosed_of_isRegularRing E

end EnvelopeProperty.Char0
