/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.RegularPrincipalDVR
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Actual regular domains are integrally closed in arbitrary dimension

The actual DVR prime localizations detect every original principal ideal.
Their intersection in the actual fraction field is the original ring, so
normality follows from actual intersection of integrally closed subrings.
-/

noncomputable section

namespace EnvelopeProperty

open IsLocalRing Ideal IsDiscreteValuationRing
open scoped Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]

/-- The actual prime localizations of a regular domain which are DVRs, with no
selected family or valuation-coverage premise supplied. -/
def regularDVRPrimes :=
  {P : PrimeSpectrum R // IsDiscreteValuationRing (Localization.AtPrime P.asIdeal)}

/-- The full actual DVR-localization intersection of a regular domain in its actual
fraction field is precisely the literal original domain subalgebra. -/
theorem iInf_dvrPrimeLocalizations_eq_bot :
    (⨅ P : regularDVRPrimes R,
      Localization.subalgebra (FractionRing R) P.val.asIdeal.primeCompl
        P.val.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  apply le_antisymm _ bot_le
  intro q hq
  let K := FractionRing R
  obtain ⟨a, b, hb, hqeq⟩ := IsFractionRing.div_surjective R q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  have ha : a ∈ (span {b} : Ideal R) := by
    apply (mem_span_singleton_iff_forall_minimalPrimes_of_isRegularRing hb0 a).mpr
    intro P hP
    let := hP.1.1
    let := isDiscreteValuationRing_localization_of_mem_minimalPrimes_of_isRegularRing hb0 hP
    let p : regularDVRPrimes R := ⟨⟨P, inferInstance⟩, inferInstance⟩
    have hle : (⨅ p : regularDVRPrimes R,
        Localization.subalgebra K p.val.asIdeal.primeCompl
          p.val.asIdeal.primeCompl_le_nonZeroDivisors) ≤
        Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors := iInf_le _ p
    have hqp : q ∈ Localization.subalgebra K P.primeCompl P.primeCompl_le_nonZeroDivisors := hle hq
    change ∃ (c s : R) (hs : s ∈ P.primeCompl),
      q = IsLocalization.mk' K c ⟨s, P.primeCompl_le_nonZeroDivisors hs⟩ at hqp
    obtain ⟨c, s, hs, heq⟩ := hqp
    rw [IsFractionRing.mk'_eq_div] at heq
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero (P.primeCompl_le_nonZeroDivisors hs)
    have hsK : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0
    have hcross := (div_eq_div_iff hbK hsK).mp (hqeq.trans heq)
    refine ⟨s, hs, Ideal.mem_span_singleton.mpr ⟨c, ?_⟩⟩
    apply IsFractionRing.injective R K
    simp only [map_mul]
    calc
      algebraMap R K s * algebraMap R K a = algebraMap R K a * algebraMap R K s := mul_comm _ _
      _ = algebraMap R K c * algebraMap R K b := hcross
      _ = algebraMap R K b * algebraMap R K c := mul_comm _ _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  have hqc : q = algebraMap R K c := by
    rw [← hqeq, hc, map_mul]
    change algebraMap R K b * algebraMap R K c / algebraMap R K b = algebraMap R K c
    exact mul_div_cancel_left₀ _ hbK
  rw [hqc]
  exact (⊥ : Subalgebra R K).algebraMap_mem c

/-- Every actual regular domain is integrally closed, without normality, factoriality,
characteristic, equicharacteristic or dimension assumptions. -/
theorem isIntegrallyClosed_of_isRegularRing : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_submonoid
    (fun P : regularDVRPrimes R => P.val.asIdeal.primeCompl)
    (fun P => P.val.asIdeal.primeCompl_le_nonZeroDivisors)
  · intro P
    let := P.property
    exact inferInstanceAs (IsIntegrallyClosed (Localization.AtPrime P.val.asIdeal))
  · exact iInf_dvrPrimeLocalizations_eq_bot R

end EnvelopeProperty
