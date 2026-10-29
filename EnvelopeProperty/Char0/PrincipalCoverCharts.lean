/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.HironakaCharts

/-!
# Principal-open refinements as finite Rees charts

For a family generating the unit ideal, the Rees chart at a nonzero member is exactly the
principal localization at that member. Thus finite principal-open refinements can be appended
to a `ReesChartTree` without changing the kind of its nodes.
-/

noncomputable section

namespace EnvelopeProperty.Char0

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- A unit-ideal chart contains the inverse of its denominator. -/
theorem inv_mem_reesTreeChart_of_span_eq_top (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    (g i : K)⁻¹ ∈ reesTreeChart C g i := by
  have hone : (1 : C) ∈ Ideal.span (Set.range g) := by rw [hg]; trivial
  simpa using div_mem_reesTreeChart_of_mem_span C g i hi hone

/-- Ratios of a unit-ideal family generate precisely the principal-localization algebra. -/
theorem reesTreeChart_eq_adjoin_inv_of_span_eq_top (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    reesTreeChart C g i = C ⊔ Algebra.adjoin B {(g i : K)⁻¹} := by
  apply le_antisymm
  · apply (reesTreeChart_le_iff C _ g i).mpr
    refine ⟨le_sup_left, fun j => ?_⟩
    rw [div_eq_mul_inv]
    exact (C ⊔ Algebra.adjoin B {(g i : K)⁻¹}).mul_mem
      ((show C ≤ C ⊔ Algebra.adjoin B {(g i : K)⁻¹} from le_sup_left) (g j).property)
      ((show Algebra.adjoin B {(g i : K)⁻¹} ≤ C ⊔ Algebra.adjoin B {(g i : K)⁻¹}
        from le_sup_right) (Algebra.subset_adjoin (Set.mem_singleton _)))
  · apply sup_le (le_reesTreeChart C g i)
    apply Algebra.adjoin_le
    rintro _ (rfl : _ = _)
    exact inv_mem_reesTreeChart_of_span_eq_top C g hg i hi

/-- Every actual localized element belongs to a unit-ideal Rees chart. -/
theorem reesChartLocalizationMap_mem_of_span_eq_top (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0)
    (z : Localization.Away (g i)) :
    reesChartLocalizationMap C g i hi z ∈ reesTreeChart C g i := by
  obtain ⟨N, c, hc⟩ := IsLocalization.Away.surj (g i) z
  have heq : reesChartLocalizationMap C g i hi z = (c : K) * ((g i : K)⁻¹) ^ N := by
    have h := congrArg (reesChartLocalizationMap C g i hi) hc
    rw [map_mul, map_pow, reesChartLocalizationMap_algebraMap,
      reesChartLocalizationMap_algebraMap] at h
    have hiK : (g i : K) ≠ 0 := fun e => hi (Subtype.ext e)
    rw [inv_pow, ← div_eq_mul_inv]
    exact (eq_div_iff (pow_ne_zero N hiK)).mpr h
  rw [heq]
  exact (reesTreeChart C g i).mul_mem (le_reesTreeChart C g i c.property)
    ((reesTreeChart C g i).pow_mem (inv_mem_reesTreeChart_of_span_eq_top C g hg i hi) N)

/-- The canonical localization map with codomain restricted to the principal-cover chart. -/
def principalCoverLocalizationToReesChart (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    Localization.Away (g i) →+* reesTreeChart C g i :=
  (reesChartLocalizationMap C g i hi).codRestrict (reesTreeChart C g i).toSubring
    (reesChartLocalizationMap_mem_of_span_eq_top C g hg i hi)

/-- The finite unit-ideal Rees chart is the actual principal localization. -/
def principalCoverLocalizationEquiv (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0) :
    Localization.Away (g i) ≃+* reesTreeChart C g i :=
  RingEquiv.ofBijective (principalCoverLocalizationToReesChart C g hg i hi) ⟨by
    intro x y h
    exact reesChartLocalizationMap_injective C g i hi (congrArg Subtype.val h), by
    intro z
    obtain ⟨w, hw⟩ := affineBlowUpToReesChart_surjective C g i hi z
    exact ⟨w.val, hw⟩⟩

/-- The principal-cover equivalence preserves the structure map from the original chart. -/
theorem principalCoverLocalizationEquiv_algebraMap (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤) (i : Fin n) (hi : g i ≠ 0)
    (c : C) : principalCoverLocalizationEquiv C g hg i hi
      (algebraMap C (Localization.Away (g i)) c) = reesTreeChartIncl C g i c := by
  apply Subtype.ext
  exact reesChartLocalizationMap_algebraMap C g i hi c

end EnvelopeProperty.Char0
