/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.Rees

/-! # Exact actual center of the SAME original local maximal-primary Rees DVR -/
noncomputable section
namespace EnvelopeProperty
variable {B K ι : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
  [Field K] [Algebra B K] [IsFractionRing B K] (g : ι → B)

omit [IsDomain B] in
/-- The ACTUAL original Rees DVR of a maximal-primary original ideal is centered
EXACTLY at the original local maximal ideal, with all nonunit/containment inputs derived. -/
theorem reesValuationRing_maximalIdeal_comap_eq
    (x : ReesIndex K g) [IsNoetherianRing (reesNormalChart K g x.idx)]
    (hrad : (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal B) :
    (IsLocalRing.maximalIdeal (reesValuationRing K g x)).comap
      (algebraMap B (reesValuationRing K g x)) = IsLocalRing.maximalIdeal B := by
  let E := reesNormalChart K g x.idx
  let V := reesValuationRing K g x
  let : Algebra E V :=
    (Subalgebra.inclusion (reesNormalChart_le_reesValuationRing x)).toRingHom.toAlgebra
  let : IsLocalization.AtPrime V x.ideal := by
    change IsLocalization x.ideal.primeCompl
      (Localization.subalgebra.ofField K x.ideal.primeCompl x.ideal.primeCompl_le_nonZeroDivisors)
    infer_instance
  have hdP : algebraMap B E (g x.idx) ∈ x.ideal :=
    x.mem_minimalPrimes.1.2 (Ideal.subset_span (Set.mem_singleton _))
  have hd : algebraMap B V (g x.idx) ∈ IsLocalRing.maximalIdeal V := by
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    intro hu
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff V x.ideal _).mp hu) hdP
  let P := (IsLocalRing.maximalIdeal V).comap (algebraMap B V)
  have hI : Ideal.span (Set.range g) ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change algebraMap B V (g i) ∈ IsLocalRing.maximalIdeal V
    obtain ⟨c, hc⟩ := algebraMap_dvd_reesValuationRing x i
    rw [hc]
    exact (IsLocalRing.maximalIdeal V).mul_mem_right c hd
  have hradP : (Ideal.span (Set.range g)).radical ≤ P :=
    (Ideal.IsPrime.radical_le_iff (inferInstance : P.IsPrime)).mpr hI
  rw [hrad] at hradP
  exact ((inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal).eq_of_le
    (show P ≠ ⊤ from (inferInstance : P.IsPrime).ne_top) hradP).symm

end EnvelopeProperty
