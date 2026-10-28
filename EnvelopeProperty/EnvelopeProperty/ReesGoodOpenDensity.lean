import EnvelopeProperty.ReesGoodOpen

/-! Dense original Rees good opens and surjectivity over regular centers. -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty

/-- The original principal open of any genuine non-zero-divisor is dense. -/
theorem dense_basicOpen_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  have hi := IsLocalization.injective (S := Localization.Away r)
    (Submonoid.powers_le.mpr hr)
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
      exact bot_le)
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  exact hd

namespace ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)
private local instance actualChartAlgebra (i : ι) : Algebra A (ReesChart.Chart g i) :=
  ReesChart.chartAlgebra g i

/-- Every original chart preserves regularity of every original coefficient. -/
theorem coefficient_mem_nonZeroDivisors (i : ι) (a : A) (ha : a ∈ nonZeroDivisors A) :
    algebraMap A (ReesChart.Chart g i) a ∈ nonZeroDivisors (ReesChart.Chart g i) := by
  apply mem_nonZeroDivisors_of_injective (ReesChart.toAway_injective g i)
  rw [(ReesChart.toAway g i).commutes]
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (g i))
    (S := Localization.Away (g i)) ha

set_option backward.isDefEq.respectTransparency false in
/-- The whole original projection preimage of a regular generator open is dense. -/
theorem dense_projection_preimage_basicOpen (j : ι) (hj : g j ∈ nonZeroDivisors A) :
    Dense ((projection g) ⁻¹' (PrimeSpectrum.basicOpen (g j) : Set (PrimeSpectrum A))) := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨x, hx⟩ := hne
  let 𝒰 := coordinateAffineOpenCover g
  obtain ⟨p, hp⟩ := 𝒰.covers x
  let i := 𝒰.idx x
  have hpoint : chartImmersion g i p = x := hp
  have hd := dense_basicOpen_of_mem_nonZeroDivisors
    (algebraMap A (ReesChart.Chart g i) (g j))
    (coefficient_mem_nonZeroDivisors g i (g j) hj)
  obtain ⟨z, hzV, hzD⟩ := hd.inter_open_nonempty
    ((chartImmersion g i) ⁻¹' V)
    (hV.preimage (chartImmersion g i).continuous)
    ⟨p, by simpa only [Set.mem_preimage, hpoint] using hx⟩
  refine ⟨chartImmersion g i z, hzV, ?_⟩
  have he := congrArg (fun f => f z) (chartImmersion_comp_projection g i)
  change (projection g) (chartImmersion g i z) ∈ PrimeSpectrum.basicOpen (g j)
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, he]
  exact hzD

set_option backward.isDefEq.respectTransparency false in
/-- The actual good-open lift contains every original point of the target good open. -/
theorem basicOpen_subset_range_projection (j : ι) :
    (PrimeSpectrum.basicOpen (g j) : Set (PrimeSpectrum A)) ⊆ Set.range (projection g) := by
  intro x hx
  obtain ⟨z, hz⟩ : x ∈ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))) := by
    change x ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (g j))))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (g j)) (g j)]
    exact hx
  refine ⟨goodOpenLift g j z, ?_⟩
  have he := congrArg (fun f => f z) (goodOpenLift_comp_projection g j)
  exact he.trans hz

set_option backward.isDefEq.respectTransparency false in
/-- The same finite-family Rees projection is surjective over a regular original center. -/
theorem projection_surjective_of_mem_nonZeroDivisors [Finite ι]
    (j : ι) (hj : g j ∈ nonZeroDivisors A) : Function.Surjective (projection g) := by
  let : IsProper (projection g) := projection_isProper g
  have hc : IsClosed (Set.range (projection g)) :=
    (projection g).isClosedMap.isClosed_range
  have hd := dense_basicOpen_of_mem_nonZeroDivisors (g j) hj
  have hsub := closure_minimal (basicOpen_subset_range_projection g j) hc
  change closure (PrimeSpectrum.basicOpen (g j) : Set (PrimeSpectrum A)) ⊆ Set.range (projection g) at hsub
  rw [hd.closure_eq] at hsub
  intro x
  exact hsub (Set.mem_univ x)

end ReesPresentation
end EnvelopeProperty
