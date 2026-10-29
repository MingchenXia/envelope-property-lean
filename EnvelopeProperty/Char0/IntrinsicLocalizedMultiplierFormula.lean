/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRLocalizedMultiplierFormula
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal

/-!
# The exact intrinsic multiplier formula at actual leaf localizations

The actual original function field produces every finite DVR coordinate
and index identification internally.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- At an actual etale-leaf DVR localization, the full intrinsic original-source
contribution is precisely its rounded leaf monomial comap, with actual finite
DVR coordinates and matching indices produced internally. -/
theorem intrinsicDVRMultiplierContribution_eq_monomial_comap_of_localization
    (C E V : Subalgebra k K) [IsFractionRing C K]
    [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
    (hCE : C ≤ E) (hEV : E ≤ V) (M : Submonoid E)
    (hlocal : letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
      IsLocalization M V)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) :
    intrinsicDVRMultiplierContribution C V (hCE.trans hEV) I hI q =
      (span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^
        (⌊q * (d l : ℚ)⌋₊ - a l)}).comap (Subalgebra.inclusion (hCE.trans hEV)).toRingHom := by
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  obtain ⟨m, π, w, hπ, hw⟩ := exists_finite_dvr_coordinates (k := k) V
  let w' : ULift.{u} (Fin m) → V := fun j => w j.down
  have hw' : IsTranscendenceBasis k (residue V ∘ w') := hw.comp_equiv Equiv.ulift
  let e : Fin n ≃ Option (ULift.{u} (Fin m)) := dvrLeafCoordinateIndexEquiv E V v hv hπ hw'
  rw [intrinsicDVRMultiplierContribution_eq C V (hCE.trans hEV) hπ hw' e I hI q]
  exact dvrMultiplierContribution_eq_monomial_comap_of_localization
    C E V hCE hEV M hlocal hπ hw' e v hv c hc d a I hI hIE hJ q

end EnvelopeProperty.Char0
