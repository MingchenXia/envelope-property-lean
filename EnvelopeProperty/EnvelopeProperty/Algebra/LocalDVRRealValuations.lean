import EnvelopeProperty.Algebra.DiscreteValuationRealScale
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Genuine local original DVR centers classify the ENTIRE original real valuation -/
open IsDiscreteValuationRing
open scoped NNReal WithZero
noncomputable section
namespace EnvelopeProperty.LocalDVRRealValuations
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]

/-- A genuine local overring in the SAME actual fraction field is the WHOLE original valuation ring.
The proof uses the native local-overring theorem as in the bounded sibling
`DeJongAlterations.Algebra.DiscreteValuationOverring`, without importing its larger cone. -/
theorem localMap_bijective [ValuationRing R] (v : Valuation K ℝ≥0)
    (ρ : R →+* v.valuationSubring) [IsLocalHom ρ]
    (hρ : v.valuationSubring.toSubring.subtype.comp ρ = algebraMap R K) :
    Function.Bijective ρ := by
  let g := v.valuationSubring.toSubring.subtype
  have H := bijective_rangeRestrict_comp_of_valuationRing ρ g hρ
  refine ⟨Function.Injective.of_comp (f := g) ?_, ?_⟩
  · rw [← RingHom.coe_comp, hρ]
    exact IsFractionRing.injective R K
  · intro s
    obtain ⟨r, hr⟩ := H.2 (g.rangeRestrict s)
    have hK : (ρ r : K) = (s : K) :=
      congrArg (fun a : g.range => (a : K)) hr
    exact ⟨r, Subtype.ext hK⟩

/-- The ENTIRE original ring is the genuine real valuation's integer ring, derived from its actual local map. -/
theorem integers_of_localMap [ValuationRing R] (v : Valuation K ℝ≥0)
    (ρ : R →+* v.valuationSubring) [IsLocalHom ρ]
    (hρ : v.valuationSubring.toSubring.subtype.comp ρ = algebraMap R K) :
    v.Integers R := by
  have hsurj := (localMap_bijective v ρ hρ).surjective
  refine ⟨IsFractionRing.injective R K, fun r => ?_, fun {a} ha => ?_⟩
  · rw [← RingHom.congr_fun hρ r]
    exact (ρ r).2
  · obtain ⟨r, hr⟩ := hsurj ⟨a, ha⟩
    exact ⟨r, (RingHom.congr_fun hρ r).symm.trans (congrArg Subtype.val hr)⟩

variable [IsDiscreteValuationRing R]

private theorem native_uniformizer_value (π : R) (hπ : Irreducible π) :
    (maximalIdeal R).valuation K (algebraMap R K π) = WithZero.exp (-1) := by
  have ho : Ring.ordFrac R (algebraMap R K π) = WithZero.exp (1 : ℤ) :=
    Ring.ordFrac_irreducible hπ
  rw [Ring.ordFrac_eq_valuation_inv] at ho
  simpa only [inv_inv, ← WithZero.exp_neg] using congrArg Inv.inv ho

/-- Every actual local DVR coefficient map derives a TRUE positive scale on ALL original fractions. -/
theorem exists_positive_realScale (v : Valuation K ℝ≥0)
    (ρ : R →+* v.valuationSubring) [IsLocalHom ρ]
    (hρ : v.valuationSubring.toSubring.subtype.comp ρ = algebraMap R K) :
    ∃ s : ℝ≥0, 0 < s ∧
      v = DiscreteValuationRealScale.valuation ((maximalIdeal R).valuation K) s := by
  have hv := integers_of_localMap v ρ hρ
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  have hz0 : (0 : ℝ) < (v (algebraMap R K π) : ℝ) :=
    NNReal.coe_pos.mpr ((map_ne_zero v).mpr hπK).pos
  have hz1 : (v (algebraMap R K π) : ℝ) < 1 := hv.valuation_irreducible_lt_one hπ
  let s : ℝ≥0 := ⟨-Real.log (v (algebraMap R K π) : ℝ),
    (neg_pos.mpr (Real.log_neg hz0 hz1)).le⟩
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hz0 hz1)
  let w := DiscreteValuationRealScale.valuation ((maximalIdeal R).valuation K) s
  have hwπ : w (algebraMap R K π) = v (algebraMap R K π) := by
    apply NNReal.eq
    apply Real.log_injOn_pos
    · exact NNReal.coe_pos.mpr ((map_ne_zero w).mpr hπK).pos
    · exact hz0
    · change Real.log ((DiscreteValuationRealScale.scale s
        ((maximalIdeal R).valuation K (algebraMap R K π)) : ℝ≥0) : ℝ) = _
      rw [native_uniformizer_value π hπ, DiscreteValuationRealScale.log_scale_exp]
      change -Real.log (v (algebraMap R K π) : ℝ) * ((-1 : ℤ) : ℝ) = _
      norm_num
  have hwu (u : Rˣ) : w (algebraMap R K u) = 1 := by
    change DiscreteValuationRealScale.scale s
      ((maximalIdeal R).valuation K (algebraMap R K u)) = 1
    rw [Valuation.Integers.one_of_isUnit' u.isUnit ((maximalIdeal R).valuation_le_one), map_one]
  have hcoeff (r : R) : v (algebraMap R K r) = w (algebraMap R K r) := by
    by_cases hr : r = 0
    · subst r
      simp only [map_zero]
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hr hπ
    simp only [map_mul, map_pow, hv.one_of_isUnit u.isUnit, hwu u, one_mul, hwπ]
  refine ⟨s, hs, Valuation.ext fun a => ?_⟩
  change v a = w a
  obtain ⟨r, t, ht, rfl⟩ := IsFractionRing.div_surjective R a
  simp only [map_div₀, hcoeff]

/-- The TRUE original uniformizer value makes the whole native real scaling injective in its parameter. -/
theorem realScale_injective : Function.Injective
    (DiscreteValuationRealScale.valuation ((maximalIdeal R).valuation K)) := by
  intro s t hst
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have h := congrArg (fun w : Valuation K ℝ≥0 => Real.log (w (algebraMap R K π) : ℝ)) hst
  change Real.log ((DiscreteValuationRealScale.scale s
    ((maximalIdeal R).valuation K (algebraMap R K π)) : ℝ≥0) : ℝ) =
    Real.log ((DiscreteValuationRealScale.scale t
      ((maximalIdeal R).valuation K (algebraMap R K π)) : ℝ≥0) : ℝ) at h
  rw [native_uniformizer_value π hπ, DiscreteValuationRealScale.log_scale_exp,
    DiscreteValuationRealScale.log_scale_exp] at h
  apply NNReal.eq
  simp only [Int.cast_neg, Int.cast_one, mul_neg_one] at h
  exact neg_injective h

/-- The entire original valuation with an actual local DVR center determines one UNIQUE positive parameter. -/
theorem existsUnique_positive_realScale (v : Valuation K ℝ≥0)
    (ρ : R →+* v.valuationSubring) [IsLocalHom ρ]
    (hρ : v.valuationSubring.toSubring.subtype.comp ρ = algebraMap R K) :
    ∃! s : ℝ≥0, 0 < s ∧
      v = DiscreteValuationRealScale.valuation ((maximalIdeal R).valuation K) s := by
  obtain ⟨s, hs, hv⟩ := exists_positive_realScale v ρ hρ
  exact ⟨s, ⟨hs, hv⟩, fun t ht => realScale_injective (ht.2.symm.trans hv)⟩

end EnvelopeProperty.LocalDVRRealValuations
