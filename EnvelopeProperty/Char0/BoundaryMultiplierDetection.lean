/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.EtaleBoundaryDVRFamily
import EnvelopeProperty.Char0.IntrinsicLocalizedMultiplierFormula

/-!
# Fixed actual boundary DVRs detect all rounded leaf ideals

The same finite actual divisorial family detects the rounded original-source
leaf ideals at every rational exponent. No finite testing premise is given.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

private theorem boundaryMultiplier_prime {E : Type*} [CommRing E]
    {τ : Type*} [Fintype τ] (p : τ → E) (P : boundaryMinimalPrimes p) : P.val.IsPrime := by
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp P.property
  exact hl.1.1

/-- The actual intrinsic boundary-DVR contribution is exactly localized
rounded monomial divisibility in the original actual prime localization. -/
theorem mem_etaleBoundaryDVRContribution_iff_localized_monomial
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) (f : C) (P : boundaryMinimalPrimes (fun l => v (c l))) :
    letI : P.val.IsPrime := boundaryMultiplier_prime (fun l => v (c l)) P
    let D := etaleBoundaryDivisorialDVR C E hCE v hv c P
    letI := D.property.2.1
    letI := D.property.2.2.1
    letI := D.property.2.2.2
    f ∈ intrinsicDVRMultiplierContribution C D.val D.property.1 I hI q ↔
      algebraMap E (Localization.AtPrime P.val)
          (∏ l, v (c l) ^ (⌊q * (d l : ℚ)⌋₊ - a l)) ∣
        algebraMap E (Localization.AtPrime P.val) (Subalgebra.inclusion hCE f) := by
  let _ : P.val.IsPrime := boundaryMultiplier_prime (fun l => v (c l)) P
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  let D := etaleBoundaryDivisorialDVR C E hCE v hv c P
  let := D.property.2.1
  let := D.property.2.2.1
  let := D.property.2.2.2
  let V := primeLocalizationSubalgebra E P.val
  have hDV : D.val = V := etaleBoundaryDivisorialDVR_val C E hCE v hv c P
  have : IsDiscreteValuationRing V := hDV ▸ D.property.2.1
  have : IsFractionRing V K := hDV ▸ D.property.2.2.1
  have : Algebra.EssFiniteType k V := hDV ▸ D.property.2.2.2
  let hEV : E ≤ V := le_primeLocalizationSubalgebra E P.val
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  let hlocal : IsLocalization P.val.primeCompl V := isLocalization_primeLocalizationSubalgebra E P.val
  change f ∈ intrinsicDVRMultiplierContribution C V (hCE.trans hEV) I hI q ↔ _
  rw [intrinsicDVRMultiplierContribution_eq_monomial_comap_of_localization
    C E V hCE hEV P.val.primeCompl hlocal v hv c hc d a I hI hIE hJ q,
    Ideal.mem_comap, Ideal.mem_span_singleton]
  let g : E := ∏ l, v (c l) ^ (⌊q * (d l : ℚ)⌋₊ - a l)
  have hgen : algebraMap E V g =
      ∏ l, Subalgebra.inclusion hEV (v (c l)) ^ (⌊q * (d l : ℚ)⌋₊ - a l) := by
    simp only [g, map_prod, map_pow]
    rfl
  have hcomp : algebraMap E V (Subalgebra.inclusion hCE f) =
      (Subalgebra.inclusion (hCE.trans hEV)).toRingHom f := rfl
  rw [← hgen, ← hcomp]
  exact dvd_in_primeLocalizationSubalgebra_iff E P.val g (Subalgebra.inclusion hCE f)

/-- A fixed finite actual boundary divisorial family detects every rounded
leaf ideal, for every rational exponent, on the actual original source. -/
theorem mem_rounded_leaf_iff_all_boundaryDVRContributions
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E)
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (hIE : I.map (Subalgebra.inclusion hCE).toRingHom = span {∏ l, v (c l) ^ d l})
    (hJ : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) = span {∏ l, v (c l) ^ a l})
    (q : ℚ) (f : C) :
    Subalgebra.inclusion hCE f ∈ span {∏ l, v (c l) ^ (⌊q * (d l : ℚ)⌋₊ - a l)} ↔
      ∀ P : boundaryMinimalPrimes (fun l => v (c l)),
        let D := etaleBoundaryDivisorialDVR C E hCE v hv c P
        letI := D.property.2.1
        letI := D.property.2.2.1
        letI := D.property.2.2.2
        f ∈ intrinsicDVRMultiplierContribution C D.val D.property.1 I hI q := by
  let := isRegularRing_of_etale_coordinates v hv
  have hp (l : τ) : v (c l) ≠ 0 := by
    intro hz
    apply (etaleDifferentialBasis v hv).ne_zero (c l)
    rw [etaleDifferentialBasis_apply v hv, hz, map_zero]
  rw [mem_span_prod_pow_iff_boundary_localizations (fun l => v (c l)) hp
    (fun l => ⌊q * (d l : ℚ)⌋₊ - a l)]
  constructor
  · intro H P
    let _ : P.val.IsPrime := boundaryMultiplier_prime (fun l => v (c l)) P
    exact (mem_etaleBoundaryDVRContribution_iff_localized_monomial
      C E hCE v hv c hc d a I hI hIE hJ q f P).mpr (H P.val P.property)
  · intro H P _ hP
    exact (mem_etaleBoundaryDVRContribution_iff_localized_monomial
      C E hCE v hv c hc d a I hI hIE hJ q f ⟨P, hP⟩).mp (H ⟨P, hP⟩)

end EnvelopeProperty.Char0
