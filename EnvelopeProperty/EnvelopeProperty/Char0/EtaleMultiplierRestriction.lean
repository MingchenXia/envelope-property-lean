/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleNormal
import EnvelopeProperty.Char0.NormalLeafMultiplierRestriction

/-!
# Full multiplier membership restricts to every actual etale monomial leaf

All normality needed for the reverse principal-divisibility argument is
derived from the actual etale coordinate map.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- Full all-divisorial-DVR multiplier membership forces rounded monomial
membership on every actual etale leaf. Normality is derived internally. -/
theorem valuativeMultiplierIdeal_le_comap_monomial_of_etale_leaf
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) :
    valuativeMultiplierIdeal C I hI q ≤
      (span {∏ l, v (c l) ^ (⌊q * (d l : ℚ)⌋₊ - a l)}).comap
        (Subalgebra.inclusion hCE).toRingHom := by
  let := isIntegrallyClosed_of_etale_coordinates v hv
  exact valuativeMultiplierIdeal_le_comap_monomial_of_normal_leaf
    C E hCE v hv c hc d a I hI hIE hJ q

end EnvelopeProperty.Char0
