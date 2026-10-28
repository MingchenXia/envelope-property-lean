/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRLocalizedMultiplierFormula
import EnvelopeProperty.Char0.DivisorialPrimeLocalizations

/-!
# Full valuative multiplier membership restricts to rounded monomials on normal leaves

The original-source ideal is tested at actual literal DVR subalgebras obtained
from the accepted principal-ideal minimal-prime criterion on a normal leaf.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- Exact full valuative membership forces rounded monomial divisibility on every
actual normal etale leaf. Normality is a leaf property in this local theorem;
it is not accepted as a new assumption for the arbitrary smooth-source endpoint. -/
theorem valuativeMultiplierIdeal_le_comap_monomial_of_normal_leaf
    (C E : Subalgebra k K) [IsFractionRing C K] [IsIntegrallyClosed E] (hCE : C ≤ E)
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
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  let := finiteType_of_etale_coordinates v hv
  have : Algebra.EssFiniteType k E := inferInstance
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  let g : E := ∏ l, v (c l) ^ (⌊q * (d l : ℚ)⌋₊ - a l)
  have hvne (i : Fin n) : v i ≠ 0 := by
    intro h
    apply (etaleDifferentialBasis v hv).ne_zero i
    rw [etaleDifferentialBasis_apply v hv, h, map_zero]
  have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => pow_ne_zero _ (hvne (c l))
  intro f hf
  change Subalgebra.inclusion hCE f ∈ span {g}
  apply (mem_span_singleton_iff_forall_minimalPrimes_dvd hg (Subalgebra.inclusion hCE f)).mpr
  intro P hprime hP
  let V := primeLocalizationSubalgebra E P
  let hEV : E ≤ V := le_primeLocalizationSubalgebra E P
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := isDiscreteValuationRing_primeLocalizationSubalgebra_of_minimalPrimes E P hg hP
  let := isFractionRing_primeLocalizationSubalgebra E P
  let := essFiniteType_primeLocalizationSubalgebra E P
  let hlocal : IsLocalization P.primeCompl V := isLocalization_primeLocalizationSubalgebra E P
  obtain ⟨m, π, u, hπ, hu⟩ := exists_finite_dvr_coordinates (k := k) V
  let u' : ULift.{u} (Fin m) → V := fun j => u j.down
  have hu' : IsTranscendenceBasis k (residue V ∘ u') := hu.comp_equiv Equiv.ulift
  let e : Fin n ≃ Option (ULift.{u} (Fin m)) :=
    dvrLeafCoordinateIndexEquiv E V v hv hπ hu'
  have hmem := valuativeMultiplierIdeal_le_contribution C V (hCE.trans hEV) I hI q hf
  rw [intrinsicDVRMultiplierContribution_eq C V (hCE.trans hEV) hπ hu' e I hI q,
    dvrMultiplierContribution_eq_monomial_comap_of_localization C E V hCE hEV P.primeCompl
      hlocal hπ hu' e v hv c hc d a I hI hIE hJ q] at hmem
  have hgen : algebraMap E V g =
      ∏ l, Subalgebra.inclusion hEV (v (c l)) ^ (⌊q * (d l : ℚ)⌋₊ - a l) := by
    simp only [g, map_prod, map_pow]
    rfl
  have hcomp : algebraMap E V (Subalgebra.inclusion hCE f) =
      Subalgebra.inclusion (hCE.trans hEV) f := rfl
  have hdiv : algebraMap E V g ∣ algebraMap E V (Subalgebra.inclusion hCE f) := by
    rw [hgen, hcomp]
    exact Ideal.mem_span_singleton.mp hmem
  exact (dvd_in_primeLocalizationSubalgebra_iff E P g (Subalgebra.inclusion hCE f)).mp hdiv

end EnvelopeProperty.Char0
