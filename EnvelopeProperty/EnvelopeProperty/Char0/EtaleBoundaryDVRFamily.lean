/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.BoundaryPrimeDetection
import EnvelopeProperty.Char0.EtaleNormal
import EnvelopeProperty.Char0.DivisorialPrimeLocalizations
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal

/-!
# Fixed finite actual divisorial DVRs from an actual etale boundary

The original function field, actual principal prime localizations,
DVR properties, essential finite type and finiteness are all derived.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem etaleBoundaryFamily_prime {E : Type*} [CommRing E]
    {τ : Type*} [Fintype τ] (p : τ → E) (P : boundaryMinimalPrimes p) : P.val.IsPrime := by
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp P.property
  exact hl.1.1

/-- Each actual fixed boundary minimal prime gives an actual divisorial DVR
of the original source inside the original function field. -/
def etaleBoundaryDivisorialDVR
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n)
    (P : boundaryMinimalPrimes (fun l => v (c l))) : divisorialDVRs C := by
  let _ : P.val.IsPrime := etaleBoundaryFamily_prime (fun l => v (c l)) P
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  let := finiteType_of_etale_coordinates v hv
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  let := isIntegrallyClosed_of_etale_coordinates v hv
  let l := Classical.choose (Set.mem_iUnion.mp P.property)
  have hl : P.val ∈ (span {v (c l)}).minimalPrimes := Classical.choose_spec (Set.mem_iUnion.mp P.property)
  have hvne : v (c l) ≠ 0 := by
    intro hz
    apply (etaleDifferentialBasis v hv).ne_zero (c l)
    rw [etaleDifferentialBasis_apply v hv, hz, map_zero]
  let V := primeLocalizationSubalgebra E P.val
  let := isDiscreteValuationRing_primeLocalizationSubalgebra_of_minimalPrimes E P.val hvne hl
  let := isFractionRing_primeLocalizationSubalgebra E P.val
  let := essFiniteType_primeLocalizationSubalgebra E P.val
  exact ⟨V, hCE.trans (le_primeLocalizationSubalgebra E P.val), inferInstance, inferInstance, inferInstance⟩

/-- The constructed actual valuation subalgebra is precisely the literal
original-field prime-localization image, not an abstract DVR replacement. -/
theorem etaleBoundaryDivisorialDVR_val
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n)
    (P : boundaryMinimalPrimes (fun l => v (c l))) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    letI : P.val.IsPrime := etaleBoundaryFamily_prime (fun l => v (c l)) P
    (etaleBoundaryDivisorialDVR C E hCE v hv c P).val = primeLocalizationSubalgebra E P.val := rfl

/-- The actual family of divisorial DVRs from the fixed etale boundary is finite,
independently of every later ideal exponent or rational multiplier parameter. -/
theorem finite_range_etaleBoundaryDivisorialDVR
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) :
    (Set.range (etaleBoundaryDivisorialDVR C E hCE v hv c)).Finite := by
  let := finiteType_of_etale_coordinates v hv
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  let : Fintype (boundaryMinimalPrimes (fun l => v (c l))) :=
    (finite_boundaryMinimalPrimes (fun l => v (c l))).fintype
  exact Set.finite_range _

end EnvelopeProperty.Char0
