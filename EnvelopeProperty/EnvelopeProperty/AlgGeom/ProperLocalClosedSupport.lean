import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Fiber

/-! # Closed supports and closed points over the closed fibre of a local base -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section
universe u

namespace EnvelopeProperty.ProperLocalSectionDetection

variable {S : Type u} [CommRing S] [IsLocalRing S] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of S)) [UniversallyClosed q]

/-- Every nonempty actual closed support meets the original closed fibre. -/
theorem closedSubset_meets_closedFiber (Z : Set Y) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ y ∈ Z, q y = IsLocalRing.closedPoint S := by
  obtain ⟨z, hz⟩ := hne
  have hc : IsClosed (q '' Z) := q.isClosedMap Z hZ
  exact (IsLocalRing.specializes_closedPoint (q z)).mem_closed hc ⟨z, hz, rfl⟩

/-- Actual closed supports disjoint from the whole closed fibre are empty. -/
theorem closedSubset_eq_empty_of_closedFiber (Z : Set Y) (hZ : IsClosed Z)
    (h : ∀ y, q y = IsLocalRing.closedPoint S → y ∉ Z) : Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨y, hyZ, hy⟩ := closedSubset_meets_closedFiber q Z hZ ⟨z, hz⟩
  exact h y hy hyZ

/-- The whole original ideal sheaf is the unit ideal if its closed support misses the closed fibre. -/
theorem idealSheaf_eq_top_of_closedFiber (I : Y.IdealSheafData)
    (h : ∀ y, q y = IsLocalRing.closedPoint S → y ∉ I.support) : I = ⊤ := by
  apply (I.support_eq_bot_iff).mp
  apply SetLike.coe_injective
  exact closedSubset_eq_empty_of_closedFiber q I.supportSet I.isClosed_supportSet h

omit [UniversallyClosed q] in
/-- The closed fibre is an actual closed embedded subspace of the original source. -/
theorem isClosedEmbedding_closedFiber :
    Topology.IsClosedEmbedding (q.fiberι (IsLocalRing.closedPoint S)) := by
  refine ⟨(q.fiberι (IsLocalRing.closedPoint S)).isEmbedding, ?_⟩
  rw [Scheme.Hom.range_fiberι]
  exact (IsLocalRing.isClosed_singleton_closedPoint S).preimage q.continuous

/-- Actual finite type makes every nonempty closed support meet a CLOSED original point of the closed fibre. -/
theorem closedSubset_meets_closedPoint_closedFiber [LocallyOfFiniteType q]
    (Z : Set Y) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ y ∈ Z, IsClosed ({y} : Set Y) ∧ q y = IsLocalRing.closedPoint S := by
  obtain ⟨y, hyZ, hy⟩ := closedSubset_meets_closedFiber q Z hZ hne
  have hyr : y ∈ Set.range (q.fiberι (IsLocalRing.closedPoint S)) := by
    rw [Scheme.Hom.range_fiberι]
    exact hy
  obtain ⟨w, hw⟩ := hyr
  have hpre : IsClosed ((q.fiberι (IsLocalRing.closedPoint S)) ⁻¹' Z) :=
    hZ.preimage (q.fiberι (IsLocalRing.closedPoint S)).continuous
  have hne' : ((q.fiberι (IsLocalRing.closedPoint S)) ⁻¹' Z).Nonempty :=
    ⟨w, by simpa only [Set.mem_preimage, hw] using hyZ⟩
  obtain ⟨v, hvZ, hv⟩ := nonempty_inter_closedPoints hne' hpre.isLocallyClosed
  refine ⟨q.fiberι (IsLocalRing.closedPoint S) v, hvZ, ?_, ?_⟩
  · have hc := (isClosedEmbedding_closedFiber q).isClosedMap _ hv
    simpa only [Set.image_singleton] using hc
  · have hr : q.fiberι (IsLocalRing.closedPoint S) v ∈
        Set.range (q.fiberι (IsLocalRing.closedPoint S)) := ⟨v, rfl⟩
    rw [Scheme.Hom.range_fiberι] at hr
    exact hr

/-- It suffices to exclude closed original points over the closed point of the local base. -/
theorem closedSubset_eq_empty_of_closedPoint_closedFiber [LocallyOfFiniteType q]
    (Z : Set Y) (hZ : IsClosed Z)
    (h : ∀ y, IsClosed ({y} : Set Y) → q y = IsLocalRing.closedPoint S → y ∉ Z) : Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨y, hyZ, hyc, hy⟩ := closedSubset_meets_closedPoint_closedFiber q Z hZ ⟨z, hz⟩
  exact h y hyc hy hyZ

end EnvelopeProperty.ProperLocalSectionDetection
