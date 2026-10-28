import EnvelopeProperty.Potential.LineAffinoidUnions

/-! # Actual finite closed-cover growth and overlap induction -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {ι : Type*} [Fintype ι] {n : ι → ℕ} (V : ∀ i, FCStandardAffinoid w (n i))
variable (hVU : ∀ i, (V i).carrier ⊆ U.carrier)
variable (hcover : ∀ x ∈ U.carrier, ∃ i, x ∈ (V i).carrier)

include hVU hcover in
/-- EVERY nonempty proper actual cover stage has an actual overlap with an outside original piece. -/
theorem exists_crossing_cover_piece (S : Finset ι) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ ((V i).carrier ∩ (V j).carrier).Nonempty := by
  classical
  have houtside : ∃ j, j ∉ S := by
    by_contra! h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨i,hi⟩ := hS
  obtain ⟨j,hj⟩ := houtside
  let A : Set (RelativeSpectrum w K[X]) := ⋃ i ∈ S, (V i).carrier
  let B : Set (RelativeSpectrum w K[X]) := ⋃ j ∈ Finset.univ \ S, (V j).carrier
  have hA : IsClosed A := isClosed_biUnion_finset fun i _ => (V i).isClosed_carrier
  have hB : IsClosed B := isClosed_biUnion_finset fun j _ => (V j).isClosed_carrier
  have hcov : U.carrier ⊆ A ∪ B := by
    intro y hy
    obtain ⟨k,hk⟩ := hcover y hy
    by_cases hkS : k ∈ S
    · exact Or.inl (Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkS,hk⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hkS⟩,hk⟩⟩)
  have hUA : (U.carrier ∩ A).Nonempty :=
    ⟨(V i).outerGauss,hVU i (V i).outerGauss_mem,
      Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,(V i).outerGauss_mem⟩⟩⟩
  have hUB : (U.carrier ∩ B).Nonempty :=
    ⟨(V j).outerGauss,hVU j (V j).outerGauss_mem,
      Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩,(V j).outerGauss_mem⟩⟩⟩
  obtain ⟨y,_,hyA,hyB⟩ := (isPreconnected_closed_iff.mp U.isConnected_carrier.isPreconnected)
    A B hA hB hcov hUA hUB
  obtain ⟨i,hyI⟩ := Set.mem_iUnion.mp hyA
  obtain ⟨hi,hyI⟩ := Set.mem_iUnion.mp hyI
  obtain ⟨j,hyJ⟩ := Set.mem_iUnion.mp hyB
  obtain ⟨hj,hyJ⟩ := Set.mem_iUnion.mp hyJ
  exact ⟨i,hi,j,(Finset.mem_sdiff.mp hj).2,y,hyI,hyJ⟩

include hVU hcover in
theorem exists_piece_meeting_partial_union (S : Finset ι) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ j, j ∉ S ∧ ((⋃ i ∈ S, (V i).carrier) ∩ (V j).carrier).Nonempty := by
  obtain ⟨i,hi,j,hj,y,hyI,hyJ⟩ := U.exists_crossing_cover_piece V hVU hcover S hS hproper
  exact ⟨j,hj,y,Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hyI⟩⟩,hyJ⟩

include hVU hcover in
/-- Ordinary finite induction through ACTUAL overlapping cover additions; no graph/ordering certificate is supplied. -/
theorem finite_cover_overlap_induction (P : Finset ι → Prop)
    (hseed : ∀ i, P {i})
    (hstep : ∀ S, P S → ∀ j (hj : j ∉ S),
      ((⋃ i ∈ S, (V i).carrier) ∩ (V j).carrier).Nonempty → P (S.cons j hj)) :
    P Finset.univ := by
  classical
  obtain ⟨i₀,_⟩ := hcover U.outerGauss U.outerGauss_mem
  let good := Finset.univ.powerset.filter fun S : Finset ι => P S ∧ i₀ ∈ S
  have hstart : {i₀} ∈ good := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hseed i₀,Finset.mem_singleton_self _⟩
  obtain ⟨S,_,hmax⟩ := good.exists_le_maximal hstart
  have hPS : P S := (Finset.mem_filter.mp hmax.1).2.1
  have hi₀ : i₀ ∈ S := (Finset.mem_filter.mp hmax.1).2.2
  have hfull : S = Finset.univ := by
    by_contra hproper
    obtain ⟨j,hj,hoverlap⟩ := U.exists_piece_meeting_partial_union V hVU hcover S ⟨i₀,hi₀⟩ hproper
    have hPnew := hstep S hPS j hj hoverlap
    have hnew : S.cons j hj ∈ good := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hPnew,Finset.mem_cons.mpr (Or.inr hi₀)⟩
    have hsub : S ⊆ S.cons j hj := fun a ha => Finset.mem_cons.mpr (Or.inr ha)
    exact hj (hmax.2 hnew hsub (Finset.mem_cons.mpr (Or.inl rfl)))
  exact hfull ▸ hPS
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
