import EnvelopeProperty.Algebra.Rees
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Actual Rees indices exist for every original nonzero proper finite ideal -/
noncomputable section
namespace EnvelopeProperty.ReesIndexExistence
variable {B K : Type*} [CommRing B] [Field K] [Algebra B K] [IsFractionRing B K]
variable {ι : Type*} [Finite ι] (g : ι → B)

/-- A genuine original normalized Rees chart has a nonunit original denominator.
The valuation subring and chart are derived from the original proper ideal. -/
theorem exists_normalChart_nonunit
    (hI : Ideal.span (Set.range g) ≠ ⊤) (hne : ∃ i, g i ≠ 0) :
    ∃ j, g j ≠ 0 ∧ ¬IsUnit (algebraMap B (reesNormalChart K g j) (g j)) := by
  classical
  let I : Ideal B := Ideal.span (Set.range g)
  let A : Subring K := (algebraMap B K).range
  let f : B →+* A := (algebraMap B K).rangeRestrict
  have hf : Function.Bijective f :=
    ⟨fun a b hab => IsFractionRing.injective B K (congrArg Subtype.val hab),
      (algebraMap B K).rangeRestrict_surjective⟩
  have hJ : I.map f ≠ ⊤ := by
    intro h
    have hh := congrArg (Ideal.comap f) h
    rw [Ideal.comap_map_of_bijective f hf, Ideal.comap_top] at hh
    exact hI hh
  obtain ⟨V,hVA,hVI⟩ := Ideal.image_subset_nonunits_valuationSubring (I.map f) hJ
  let VA : Subalgebra B K :=
    { V.toSubring with algebraMap_mem' := fun b => hVA ⟨b,rfl⟩ }
  have hval (i : ι) : V.valuation (algebraMap B K (g i)) < 1 := by
    apply V.mem_nonunits_iff.mp
    exact hVI ⟨f (g i), Ideal.mem_map_of_mem f (Ideal.subset_span ⟨i,rfl⟩), rfl⟩
  obtain ⟨i,hi⟩ := hne
  let : Fintype ι := Fintype.ofFinite ι
  let : Nonempty ι := ⟨i⟩
  obtain ⟨j,-,hj⟩ := Finset.exists_max_image Finset.univ
    (fun q => V.valuation (algebraMap B K (g q))) Finset.univ_nonempty
  have hjne : g j ≠ 0 := by
    intro hz
    have h := hj i (Finset.mem_univ i)
    rw [hz,map_zero,map_zero] at h
    have hi' : V.valuation (algebraMap B K (g i)) ≠ 0 := by
      exact (V.valuation.map_eq_zero_iff).not.mpr (by
        simpa only [map_zero] using (IsFractionRing.injective B K).ne hi)
    exact hi' (le_antisymm h zero_le)
  have hjK : algebraMap B K (g j) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne hjne
  have hchart : reesChart K g j ≤ VA := by
    apply Algebra.adjoin_le
    rintro _ ⟨q,rfl⟩
    change algebraMap B K (g q) / algebraMap B K (g j) ∈ V
    obtain ⟨a,ha⟩ := (V.valuation_le_iff _ _).mp (hj q (Finset.mem_univ q))
    rw [← ha,mul_div_cancel_right₀ _ hjK]
    exact a.2
  let : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  have hnormal : (integralClosure (reesChart K g j) K).toSubring ≤ V.toSubring := by
    apply Subring.integralClosure_le_iff.mpr
    intro a
    exact hchart a.2
  refine ⟨j,hjne,?_⟩
  let q : reesNormalChart K g j →+* V :=
    (Subring.inclusion hnormal)
  intro hu
  have hunit : IsUnit (q (algebraMap B (reesNormalChart K g j) (g j))) := hu.map q
  have heq := (V.valuation_eq_one_iff _).mp hunit
  exact (ne_of_lt (hval j)) heq

/-- The original Rees index type is nonempty, without a supplied DVR,
normality, excellence or Noetherianity premise. -/
theorem exists_reesIndex_of_proper_span
    (hI : Ideal.span (Set.range g) ≠ ⊤) (hne : ∃ i, g i ≠ 0) :
    Nonempty (ReesIndex K g) := by
  obtain ⟨j,hj,hunit⟩ := exists_normalChart_nonunit (K := K) g hI hne
  have hp : Ideal.span {algebraMap B (reesNormalChart K g j) (g j)} ≠ ⊤ := by
    exact fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨P,hP⟩ := Ideal.nonempty_minimalPrimes hp
  exact ⟨⟨j,P,hj,hP⟩⟩

end EnvelopeProperty.ReesIndexExistence
