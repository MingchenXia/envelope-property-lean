import EnvelopeProperty.Char0.NormalLeafMultiplierRestriction
import EnvelopeProperty.Char0.EtaleNormal
import Mathlib.RingTheory.Ideal.Colon

/-! # The actual monomial colon in original etale coordinate domains -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u

private theorem monomialColonWeightedSub {τ : Type*} [Fintype τ]
    (r d a : τ → ℕ) (hr : ∑ l, r l ≤ 1) :
    (∑ l, d l * r l) - (∑ l, a l * r l) = ∑ l, (d l - a l) * r l := by
  simpa only [one_mul, Nat.floor_natCast] using weighted_multiplier_floor_eq_of_sum_le_one r d a 1 hr

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- On the SAME actual etale coordinate domain, the colon of the two
original monomial ideals is the SAME coordinatewise truncated-subtraction
monomial. Normality and every actual principal minimal-prime DVR are DERIVED. -/
theorem etale_monomial_colon_eq
    (E : Subalgebra k K) [IsFractionRing E K]
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) :
    (span {∏ l, v (c l) ^ d l}).colon (span {∏ l, v (c l) ^ a l} : Set E) =
      span {∏ l, v (c l) ^ (d l - a l)} := by
  let := isIntegrallyClosed_of_etale_coordinates v hv
  let := finiteType_of_etale_coordinates v hv
  have : Algebra.EssFiniteType k E := inferInstance
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  let g : E := ∏ l, v (c l) ^ (d l - a l)
  have hvne (i : Fin n) : v i ≠ 0 := by
    intro h
    apply (etaleDifferentialBasis v hv).ne_zero i
    rw [etaleDifferentialBasis_apply v hv, h, map_zero]
  have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => pow_ne_zero _ (hvne (c l))
  apply le_antisymm
  · intro f hf
    by_cases hf0 : f = 0
    · simpa only [hf0] using (span {g}).zero_mem
    change f ∈ span {g}
    apply (mem_span_singleton_iff_forall_minimalPrimes_dvd hg f).mpr
    intro P hprime hP
    let V := primeLocalizationSubalgebra E P
    let hEV : E ≤ V := le_primeLocalizationSubalgebra E P
    let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let := isDiscreteValuationRing_primeLocalizationSubalgebra_of_minimalPrimes E P hg hP
    let := isFractionRing_primeLocalizationSubalgebra E P
    let := essFiniteType_primeLocalizationSubalgebra E P
    let hlocal : IsLocalization P.primeCompl V := isLocalization_primeLocalizationSubalgebra E P
    obtain ⟨m, π, w, hπ, hw⟩ := exists_finite_dvr_coordinates (k := k) V
    let w' : ULift.{u} (Fin m) → V := fun j => w j.down
    have hw' : IsTranscendenceBasis k (residue V ∘ w') := hw.comp_equiv Equiv.ulift
    let e : Fin n ≃ Option (ULift.{u} (Fin m)) := dvrLeafCoordinateIndexEquiv E V v hv hπ hw'
    have hsum := sum_addVal_leaf_le_one_of_localization V E hEV P.primeCompl hlocal hπ hw' e v hv
    have hfinite (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
      exact (Finset.single_le_sum
        (f := fun j => addVal V (Subalgebra.inclusion hEV (v j)))
        (fun _ _ => bot_le) (Finset.mem_univ i)).trans hsum
    let r : Fin n → ℕ := fun i => (addVal V (Subalgebra.inclusion hEV (v i))).toNat
    have hcoord (i : Fin n) : addVal V (Subalgebra.inclusion hEV (v i)) = (r i : ℕ∞) :=
      (ENat.natCast_toNat (hfinite i)).symm
    have hsumNat : ∑ i, r i ≤ 1 := by
      simp_rw [hcoord] at hsum
      exact_mod_cast hsum
    have hselected : ∑ l, r (c l) ≤ 1 := by
      calc
        ∑ l, r (c l) = ∑ i ∈ Finset.univ.image c, r i :=
          (Finset.sum_image (fun _ _ _ _ h => hc h)).symm
        _ ≤ ∑ i ∈ Finset.univ, r i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ ≤ 1 := hsumNat
    have hmon (b : τ → ℕ) :
        addVal V (algebraMap E V (∏ l, v (c l) ^ b l)) =
          ((∑ l, b l * r (c l) : ℕ) : ℕ∞) := by
      simp only [map_prod, map_pow]
      exact addVal_prod_pow_toNat (fun l => Subalgebra.inclusion hEV (v (c l))) b
        (fun l => hfinite (c l))
    have hdiv : (∏ l, v (c l) ^ d l) ∣ f * (∏ l, v (c l) ^ a l) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_colon_span_singleton.mp hf)
    have hval := addVal_le_iff_dvd.mpr (map_dvd (algebraMap E V) hdiv)
    rw [map_mul, addVal_mul, hmon d, hmon a] at hval
    have hfv : addVal V (algebraMap E V f) ≠ ⊤ := by
      rw [ne_eq, addVal_eq_top_iff]
      exact (map_ne_zero_iff _ (Subalgebra.inclusion_injective hEV)).mpr hf0
    have hn : ∑ l, d l * r (c l) ≤
        (addVal V (algebraMap E V f)).toNat + ∑ l, a l * r (c l) := by
      rw [← ENat.natCast_toNat hfv] at hval
      exact_mod_cast hval
    have hcut : ∑ l, (d l - a l) * r (c l) ≤ (addVal V (algebraMap E V f)).toNat := by
      rw [← monomialColonWeightedSub (fun l => r (c l)) d a hselected]
      omega
    have htarget : addVal V (algebraMap E V g) ≤ addVal V (algebraMap E V f) := by
      rw [hmon (fun l => d l - a l), ← ENat.natCast_toNat hfv]
      exact_mod_cast hcut
    exact (dvd_in_primeLocalizationSubalgebra_iff E P g f).mp (addVal_le_iff_dvd.mp htarget)
  · intro f hf
    rw [Ideal.mem_colon_span_singleton]
    apply Ideal.mem_span_singleton.mpr
    have hprod : (∏ l, v (c l) ^ d l) ∣ g * (∏ l, v (c l) ^ a l) := by
      dsimp only [g]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_dvd_prod_of_dvd
      intro l _
      rw [← pow_add]
      apply pow_dvd_pow
      omega
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hf
    rw [ht]
    exact hprod.trans (by refine ⟨t, ?_⟩; ring)

/-- EVERY actual coefficient-ring isomorphism retains the ENTIRE original
etale monomial colon and all its original coordinate coefficients. -/
theorem etale_monomial_colon_eq_transport
    (E : Subalgebra k K) [IsFractionRing E K]
    {n : ℕ} (v : Fin n → E) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    {τ : Type u} [Fintype τ] (c : τ → Fin n) (hc : Function.Injective c)
    (d a : τ → ℕ) {B : Type u} [CommRing B] (e : E ≃+* B) :
    (span {∏ l, e (v (c l)) ^ d l}).colon (span {∏ l, e (v (c l)) ^ a l} : Set B) =
      span {∏ l, e (v (c l)) ^ (d l - a l)} := by
  ext b
  obtain ⟨f, rfl⟩ := e.surjective b
  have hsource : (∏ l, v (c l) ^ d l) ∣ f * (∏ l, v (c l) ^ a l) ↔
      (∏ l, v (c l) ^ (d l - a l)) ∣ f := by
    have h := Iff.of_eq (congrArg (fun I : Ideal E => f ∈ I)
      (etale_monomial_colon_eq E v hv c hc d a))
    simpa only [Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton] using h
  rw [Ideal.mem_colon_span_singleton, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have hmap (t : τ → ℕ) : ∏ l, e (v (c l)) ^ t l = e (∏ l, v (c l) ^ t l) := by
    simp only [map_prod, map_pow]
  rw [hmap d, hmap a, hmap (fun l => d l - a l), ← map_mul]
  have hiff (x y : E) : e x ∣ e y ↔ x ∣ y := by
    constructor
    · intro h
      simpa only [RingEquiv.symm_apply_apply] using map_dvd e.symm h
    · exact map_dvd e
  exact (hiff _ _).trans (hsource.trans (hiff _ _).symm)

end EnvelopeProperty.Char0
