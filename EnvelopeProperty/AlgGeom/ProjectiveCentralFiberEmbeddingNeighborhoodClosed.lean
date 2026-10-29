import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodCharts

/-! # The same finite original morphism is a closed immersion near the whole centre -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosed
open ProjectiveCentralFiberSectionLifting ProjectiveCentralFiberEmbeddingNeighborhood

private theorem closed_restrict_of_le {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (V T : Z.Opens) (hVT : V ≤ T) (hT : IsClosedImmersion (f ∣_ T)) :
    IsClosedImmersion (f ∣_ V) := by
  have h := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) hT (T.ι ⁻¹ᵁ V)
  have h' := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictRestrict f T (T.ι ⁻¹ᵁ V))).mp h
  have he : T.ι ''ᵁ (T.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVT]
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictEq f he)).mp h'

private theorem closed_restrict_iSup {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {ι : Type*} (W : ι → Z.Opens) (hW : ∀ i, IsClosedImmersion (f ∣_ W i)) :
    IsClosedImmersion (f ∣_ ⨆ i, W i) := by
  let T : Z.Opens := ⨆ i, W i
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsClosedImmersion)
  intro z
  have hz : z.1 ∈ ⨆ i, W i := z.2
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
  refine ⟨T.ι ⁻¹ᵁ W i, hi, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictRestrict f T (T.ι ⁻¹ᵁ W i))).mpr
  have he : T.ι ''ᵁ (T.ι ⁻¹ᵁ W i) = W i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_iSup W i)]
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictEq f he)).mpr (hW i)

/-- The actual finite original morphism is a closed immersion on an internally
constructed target open containing the ENTIRE original central target. -/
theorem exists_closed_target_neighborhood {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) [IsFinite f] (hf : f ≫ q = p)
    [IsClosedImmersion (centralMap p q f hf)] :
    ∃ T : Z.Opens, Set.range (zeroInclusion q) ⊆ (T : Set Z) ∧
      IsClosedImmersion (f ∣_ T) := by
  classical
  let J := { U : Z.Opens // IsClosedImmersion (f ∣_ U) }
  let W : J → Z.Opens := fun i => i.1
  refine ⟨⨆ i, W i, ?_, closed_restrict_iSup f W (fun i => i.2)⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨U, hU, hzU, _hUtop⟩ := exists_isAffineOpen_mem_and_subset
    (show zeroInclusion q z ∈ (⊤ : Z.Opens) by trivial)
  obtain ⟨r, _hr, hclosed, hcover⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodCharts.exists_closedImmersion_chart
      p q f hf ⟨U, hU⟩
  exact Opens.mem_iSup.mpr ⟨⟨Z.basicOpen r, hclosed⟩, hcover z hzU⟩

/-- A proper original target gives a genuine principal BASE neighbourhood on
which the SAME finite original morphism is a closed immersion. -/
theorem exists_closedImmersion_neighborhood_of_finite {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper q]
    (f : Y ⟶ Z) [IsFinite f] (hf : f ≫ q = p)
    [IsClosedImmersion (centralMap p q f hf)] :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      IsClosedImmersion (f ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  obtain ⟨T, hT, hclosed⟩ := exists_closed_target_neighborhood p q f hf
  obtain ⟨g, hg, hsubset⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_principal_neighborhood_of_fiber_subset
      q T hT
  exact ⟨g, hg, closed_restrict_of_le f _ T hsubset hclosed⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosed
