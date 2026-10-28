import EnvelopeProperty.Algebra.RegularNormal

/-! # The ENTIRE original DVR intersection in ANY prescribed original fraction field

The actual principal-ideal detection argument from RegularNormal is retained in the
original specified field, so no replacement field/coefficient comparison is assumed.
-/

noncomputable section
namespace EnvelopeProperty
open Ideal
open scoped Classical
variable {R F : Type*} [CommRing R] [IsDomain R] [IsRegularRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Membership in EVERY actual original DVR prime localization forces membership
in the SAME original ring inside its SAME prescribed fraction field. -/
theorem exists_originalRing_of_mem_all_regularDVR_localizations (q : F)
    (hq : ∀ P : regularDVRPrimes R,
      q ∈ Localization.subalgebra F P.val.asIdeal.primeCompl
        P.val.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ a : R, algebraMap R F a = q := by
  obtain ⟨a, b, hb, hqeq⟩ := IsFractionRing.div_surjective R q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap R F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hb0
  have ha : a ∈ (span {b} : Ideal R) := by
    apply (mem_span_singleton_iff_forall_minimalPrimes_of_isRegularRing hb0 a).mpr
    intro P hP
    let := hP.1.1
    let := isDiscreteValuationRing_localization_of_mem_minimalPrimes_of_isRegularRing hb0 hP
    let p : regularDVRPrimes R := ⟨⟨P, inferInstance⟩, inferInstance⟩
    have hqp := hq p
    change ∃ (c s : R) (hs : s ∈ P.primeCompl),
      q = IsLocalization.mk' F c ⟨s, P.primeCompl_le_nonZeroDivisors hs⟩ at hqp
    obtain ⟨c, s, hs, heq⟩ := hqp
    rw [IsFractionRing.mk'_eq_div] at heq
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors hs)
    have hsF : algebraMap R F s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hs0
    have hcross := (div_eq_div_iff hbF hsF).mp (hqeq.trans heq)
    refine ⟨s, hs, Ideal.mem_span_singleton.mpr ⟨c, ?_⟩⟩
    apply IsFractionRing.injective R F
    simp only [map_mul]
    calc
      algebraMap R F s * algebraMap R F a = algebraMap R F a * algebraMap R F s := mul_comm _ _
      _ = algebraMap R F c * algebraMap R F b := hcross
      _ = algebraMap R F b * algebraMap R F c := mul_comm _ _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨c, ?_⟩
  rw [← hqeq, hc, map_mul]
  change algebraMap R F c = algebraMap R F b * algebraMap R F c / algebraMap R F b
  exact (mul_div_cancel_left₀ _ hbF).symm

/-- The ENTIRE actual original DVR-prime localization intersection equals
the literal original ring in ANY SAME prescribed original fraction field. -/
theorem iInf_regularDVR_localizations_eq_bot_in_fractionField :
    (⨅ P : regularDVRPrimes R,
      Localization.subalgebra F P.val.asIdeal.primeCompl
        P.val.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  apply le_antisymm _ bot_le
  intro q hq
  have hall (P : regularDVRPrimes R) :
      q ∈ Localization.subalgebra F P.val.asIdeal.primeCompl
        P.val.asIdeal.primeCompl_le_nonZeroDivisors := by
    have hle : (⨅ Q : regularDVRPrimes R,
        Localization.subalgebra F Q.val.asIdeal.primeCompl
          Q.val.asIdeal.primeCompl_le_nonZeroDivisors) ≤
        Localization.subalgebra F P.val.asIdeal.primeCompl
          P.val.asIdeal.primeCompl_le_nonZeroDivisors := iInf_le _ P
    exact hle hq
  obtain ⟨a, rfl⟩ := exists_originalRing_of_mem_all_regularDVR_localizations q hall
  exact (⊥ : Subalgebra R F).algebraMap_mem a

end EnvelopeProperty
