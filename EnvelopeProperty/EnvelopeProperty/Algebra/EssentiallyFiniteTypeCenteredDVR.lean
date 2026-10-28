import EnvelopeProperty.Algebra.EssentiallyFiniteTypeNormalization
import EnvelopeProperty.Algebra.ReesIndexExistence
import EnvelopeProperty.Algebra.ReesLocalCenter

/-! # Genuine centered DVR existence for original local models -/
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.EssentiallyFiniteTypeCenteredDVR
variable (k B K : Type u) [Field k] [CommRing B] [Algebra k B]
  [Algebra.EssFiniteType k B] [Field K] [Algebra B K] [IsFractionRing B K]
include k

/-- Noetherianity of the SAME original normalized Rees chart is derived from
actual essentially finite type geometry, without a chart-normalization premise. -/
theorem isNoetherianRing_reesNormalChart {ι : Type u} [Finite ι] (g : ι → B) (j : ι) :
    IsNoetherianRing (reesNormalChart K g j) := by
  let : Algebra k K := ((algebraMap B K).comp (algebraMap k B)).toAlgebra
  let : IsScalarTower k B K := .of_algebraMap_eq fun _ => rfl
  let : Algebra.FiniteType B (reesChart K g j) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  let : Algebra.EssFiniteType k (reesChart K g j) :=
    Algebra.EssFiniteType.comp k B (reesChart K g j)
  exact EssentiallyFiniteTypeNormalization.isNoetherianRing_integralClosure k (reesChart K g j) K

/-- Every ACTUAL original nonfield local essentially finite type domain admits
an ACTUAL DVR of its SAME fraction field centered EXACTLY at its original maximal ideal. -/
theorem exists_centeredDVR [IsLocalRing B] (hB : ¬IsField B) :
    ∃ (V : Subalgebra B K) (hV : IsDiscreteValuationRing V),
      letI := hV
      (IsLocalRing.maximalIdeal V).comap (algebraMap B V) = IsLocalRing.maximalIdeal B := by
  classical
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing k B
  obtain ⟨s,hs⟩ := IsNoetherian.noetherian (IsLocalRing.maximalIdeal B)
  let g : s → B := fun i => i.val
  have hspan : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal B := by
    have hrange : Set.range g = (s : Set B) := by
      ext b
      simp only [Set.mem_range,Finset.mem_coe]
      exact ⟨fun ⟨a,ha⟩ => ha ▸ a.2, fun hb => ⟨⟨b,hb⟩,rfl⟩⟩
    rw [hrange]
    exact hs
  have hI : Ideal.span (Set.range g) ≠ ⊤ := by
    rw [hspan]
    exact (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal).ne_top
  have hne : ∃ i, g i ≠ 0 := by
    by_contra h
    have hg : ∀ i, g i = 0 := by simpa only [not_exists,not_not] using h
    have hm : IsLocalRing.maximalIdeal B = ⊥ := by
      rw [← hspan]
      apply le_antisymm _ bot_le
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hg i
    exact hB (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  obtain ⟨x⟩ := ReesIndexExistence.exists_reesIndex_of_proper_span (K := K) g hI hne
  let : IsNoetherianRing (reesNormalChart K g x.idx) := isNoetherianRing_reesNormalChart k B K g x.idx
  refine ⟨reesValuationRing K g x,inferInstance,?_⟩
  apply reesValuationRing_maximalIdeal_comap_eq g x
  rw [hspan]
  exact (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime).radical

end EnvelopeProperty.EssentiallyFiniteTypeCenteredDVR
