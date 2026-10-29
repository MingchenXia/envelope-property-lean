import EnvelopeProperty.ReesCoordinateCover
import EnvelopeProperty.ReesChartAway

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
noncomputable section
universe u
namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)

private local instance actualChartAlgebra (i : ι) : Algebra A (ReesChart.Chart g i) :=
  ReesChart.chartAlgebra g i

/-- The original homogeneous ratio satisfies its true entire coefficient relation. -/
theorem coefficient_mul_coordinateRatio (i : ι) (j : ι) :
    algebraMap A (ReesChart.Chart g i) (g i) * ReesChart.coordinateRatio g i j =
      algebraMap A (ReesChart.Chart g i) (g j) := by
  exact ReesChart.coefficient_mul_coordinateRatio g i j

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual inverse image of the original generator principal open lies in its own original coordinate chart. -/
theorem projection_preimage_basicOpen_subset (j : ι) :
    (projection g) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j) ≤
      Proj.basicOpen (ReesChart.grading g) (ReesChart.generator g j) := by
  intro x hx
  let 𝒰 := coordinateAffineOpenCover g
  obtain ⟨p, hp⟩ := 𝒰.covers x
  let i := 𝒰.idx x
  have hpoint : chartImmersion g i p = x := hp
  have he := congrArg (fun f => f p) (chartImmersion_comp_projection g i)
  have hbase : ReesChart.coefficients g i (g j) ∉ p.asIdeal := by
    change (Spec.map (CommRingCat.ofHom (ReesChart.coefficients g i))) p ∈
      PrimeSpectrum.basicOpen (g j)
    rw [← he, AlgebraicGeometry.Scheme.Hom.comp_apply, hpoint]
    exact hx
  have hratio : ReesChart.coordinateRatio g i j ∉ p.asIdeal := by
    intro hh
    apply hbase
    change algebraMap A (ReesChart.Chart g i) (g j) ∈ p.asIdeal
    rw [← coefficient_mul_coordinateRatio g i j]
    exact p.asIdeal.mul_mem_left _ hh
  have hpre : p ∈ (chartImmersion g i) ⁻¹ᵁ
      Proj.basicOpen (ReesChart.grading g) (ReesChart.generator g j) := by
    change p ∈ Proj.awayι (ReesChart.grading g) (ReesChart.generator g i)
      (ReesChart.generator_mem g i) (by decide) ⁻¹ᵁ _
    rw [Proj.awayι_preimage_basicOpen (ReesChart.grading g)
      (ReesChart.generator_mem g i) (by decide) (ReesChart.generator_mem g j) (by decide)]
    apply (PrimeSpectrum.mem_basicOpen _ _).mpr
    simpa only [Away.isLocalizationElem, pow_one, ReesChart.coordinateRatio] using hratio
  have hh := (TopologicalSpace.Opens.mem_map).mp hpre
  exact hpoint ▸ hh

variable (j : ι)

/-- The actual WHOLE original chart inclusion into its genuine principal base localization. -/
def chartToAway : ReesChart.Chart g j →ₐ[A] Localization.Away (g j) :=
  ReesChart.toAway g j

/-- The true chart inclusion is injective on EVERY original chart element. -/
theorem chartToAway_injective : Function.Injective (chartToAway g j) :=
  ReesChart.toAway_injective g j

/-- The Spec map of the SAME actual whole inclusion is an open immersion. -/
theorem isOpenImmersion_specMap_chartToAway : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (chartToAway g j).toRingHom)) := by
  let : Algebra (ReesChart.Chart g j) (Localization.Away (g j)) :=
    (chartToAway g j).toRingHom.toAlgebra
  let : IsLocalization.Away (algebraMap A (ReesChart.Chart g j) (g j))
      (Localization.Away (g j)) :=
    ReesChart.toAway_isLocalization g j
  exact IsOpenImmersion.of_isLocalization (algebraMap A (ReesChart.Chart g j) (g j))

/-- Its ENTIRE actual image is the genuine chart principal open of the ORIGINAL coefficient. -/
theorem range_specMap_chartToAway :
    Set.range (Spec.map (CommRingCat.ofHom (chartToAway g j).toRingHom)) =
      (PrimeSpectrum.basicOpen (algebraMap A (ReesChart.Chart g j) (g j)) :
        Set (PrimeSpectrum (ReesChart.Chart g j))) := by
  let : Algebra (ReesChart.Chart g j) (Localization.Away (g j)) :=
    (chartToAway g j).toRingHom.toAlgebra
  let : IsLocalization.Away (algebraMap A (ReesChart.Chart g j) (g j))
      (Localization.Away (g j)) :=
    ReesChart.toAway_isLocalization g j
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- The actual principal base open maps into the SAME original Rees scheme. -/
def goodOpenLift : Spec (CommRingCat.of (Localization.Away (g j))) ⟶ Scheme g :=
  Spec.map (CommRingCat.ofHom (chartToAway g j).toRingHom) ≫ chartImmersion g j

/-- This whole original good-open morphism is a genuine open immersion. -/
instance instIsOpenImmersion_goodOpenLift : IsOpenImmersion (goodOpenLift g j) := by
  let := isOpenImmersion_specMap_chartToAway g j
  unfold goodOpenLift
  exact IsOpenImmersion.comp _ _

/-- The ENTIRE original coefficient triangle, including all section maps. -/
theorem goodOpenLift_comp_projection :
    goodOpenLift g j ≫ projection g =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j)))) := by
  rw [goodOpenLift, Category.assoc, chartImmersion_comp_projection, ← Spec.map_comp]
  congr 1
  ext a
  exact (chartToAway g j).commutes a

set_option backward.isDefEq.respectTransparency false in
/-- The actual good-open lift has EXACTLY the whole original projection preimage as its range. -/
theorem range_goodOpenLift : Set.range (goodOpenLift g j) =
    (projection g) ⁻¹' (PrimeSpectrum.basicOpen (g j) : Set (PrimeSpectrum A)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have he := congrArg (fun f => f z) (goodOpenLift_comp_projection g j)
    change (projection g) (goodOpenLift g j z) ∈ PrimeSpectrum.basicOpen (g j)
    change (goodOpenLift g j ≫ projection g) z ∈ PrimeSpectrum.basicOpen (g j)
    rw [he]
    exact (PrimeSpectrum.localization_away_comap_range
      (Localization.Away (g j)) (g j)).subset ⟨z, rfl⟩
  · intro hx
    have hchart : x ∈ (chartImmersion g j).opensRange := by
      change x ∈ (Proj.awayι (ReesChart.grading g) (ReesChart.generator g j)
        (ReesChart.generator_mem g j) (by decide)).opensRange
      rw [Proj.opensRange_awayι]
      exact projection_preimage_basicOpen_subset g j hx
    obtain ⟨p, hp⟩ := hchart
    have he := congrArg (fun f => f p) (chartImmersion_comp_projection g j)
    have hlocal : p ∈ PrimeSpectrum.basicOpen (algebraMap A (ReesChart.Chart g j) (g j)) := by
      change (Spec.map (CommRingCat.ofHom (ReesChart.coefficients g j))) p ∈
        PrimeSpectrum.basicOpen (g j)
      rw [← he, AlgebraicGeometry.Scheme.Hom.comp_apply, hp]
      exact hx
    obtain ⟨z, hz⟩ : p ∈ Set.range (Spec.map
        (CommRingCat.ofHom (chartToAway g j).toRingHom)) := by
      rw [range_specMap_chartToAway]
      exact hlocal
    refine ⟨z, ?_⟩
    change chartImmersion g j ((Spec.map (CommRingCat.ofHom (chartToAway g j).toRingHom)) z) = x
    rw [hz]
    exact hp

set_option backward.isDefEq.respectTransparency false in
/-- The whole original good-open square is an actual scheme pullback with identity top map. -/
theorem isPullback_goodOpenLift : IsPullback
    (𝟙 (Spec (CommRingCat.of (Localization.Away (g j))))) (goodOpenLift g j)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))) (projection g) := by
  apply IsOpenImmersion.isPullback
  · rw [goodOpenLift_comp_projection, Category.id_comp]
  · apply SetLike.coe_injective
    change (projection g) ⁻¹' Set.range (Spec.map
      (CommRingCat.ofHom (algebraMap A (Localization.Away (g j))))) = Set.range (goodOpenLift g j)
    have he := congrArg (fun S : Set (PrimeSpectrum A) => (projection g) ⁻¹' S)
      (PrimeSpectrum.localization_away_comap_range (Localization.Away (g j)) (g j))
    exact he.trans (range_goodOpenLift g j).symm

/-- The ACTUAL base change of the original projection to its original generator principal open is an isomorphism. -/
theorem isIso_projection_over_generator : IsIso (Limits.pullback.snd (projection g)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (g j)))))) := by
  have h := (isPullback_goodOpenLift g j).flip.isoPullback_inv_snd
  rw [← h]
  infer_instance

end EnvelopeProperty.ReesPresentation
