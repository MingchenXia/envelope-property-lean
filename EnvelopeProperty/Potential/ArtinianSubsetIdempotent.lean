import EnvelopeProperty.ArtinianIdempotentEvaluation

/-! # Actual whole Artinian CRT idempotents for every genuine maximal subset -/

open scoped Classical
noncomputable section

namespace EnvelopeProperty.ArtinianFactors

variable (E : Type*) [CommRing E] [IsArtinianRing E]

/-- The actual inverse maximal-power CRT of the original subset characteristic function. -/
def subsetIdempotent (P : Set (MaximalSpectrum E)) : E :=
  (powerEquiv E).symm (fun m => if m ∈ P then 1 else 0)

theorem powerEquiv_subsetIdempotent (P : Set (MaximalSpectrum E)) :
    powerEquiv E (subsetIdempotent E P) = fun m => if m ∈ P then 1 else 0 :=
  (powerEquiv E).apply_symm_apply _

theorem subsetIdempotent_isIdempotent (P : Set (MaximalSpectrum E)) :
    IsIdempotentElem (subsetIdempotent E P) := by
  apply (powerEquiv E).injective
  rw [map_mul,powerEquiv_subsetIdempotent]
  funext m
  by_cases hm : m ∈ P
  · simp only [Pi.mul_apply,if_pos hm,mul_one]
  · simp only [Pi.mul_apply,if_neg hm,mul_zero]

/-- Every actual maximal-kernel original ring map has its EXACT prescribed zero/one value. -/
theorem subsetIdempotent_map {C : Type*} [CommRing C] (P : Set (MaximalSpectrum E))
    (m : MaximalSpectrum E) (f : E →+* C) (hf : RingHom.ker f = m.asIdeal) :
    f (subsetIdempotent E P) = if m ∈ P then 1 else 0 := by
  let t : E := if m ∈ P then 1 else 0
  have hclass : algebraMap E (PowerFactor E m) (subsetIdempotent E P) =
      algebraMap E (PowerFactor E m) t := by
    have h := congrFun (powerEquiv_subsetIdempotent E P) m
    change algebraMap E (PowerFactor E m) (subsetIdempotent E P) = _ at h
    by_cases hm : m ∈ P
    · simpa only [t,if_pos hm,map_one] using h
    · simpa only [t,if_neg hm,map_zero] using h
  have hmem : subsetIdempotent E P-t ∈ m.asIdeal^exponent E := Ideal.Quotient.eq.mp hclass
  have hz : f (subsetIdempotent E P-t) = 0 := by
    rw [← RingHom.mem_ker,hf]
    exact Ideal.pow_le_self (Nat.ne_of_gt (exponent_pos E)) hmem
  rw [map_sub,sub_eq_zero] at hz
  by_cases hm : m ∈ P
  · simpa only [t,if_pos hm,map_one] using hz
  · simpa only [t,if_neg hm,map_zero] using hz

theorem subsetIdempotent_empty : subsetIdempotent E ∅ = 0 := by
  apply (powerEquiv E).injective
  rw [powerEquiv_subsetIdempotent,map_zero]
  funext m
  simp only [Set.notMem_empty,if_false,Pi.zero_apply]

theorem subsetIdempotent_univ : subsetIdempotent E Set.univ = 1 := by
  apply (powerEquiv E).injective
  rw [powerEquiv_subsetIdempotent,map_one]
  funext m
  simp only [Set.mem_univ,if_true,Pi.one_apply]

end EnvelopeProperty.ArtinianFactors
