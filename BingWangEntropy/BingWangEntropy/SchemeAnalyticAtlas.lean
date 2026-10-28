import BingWangEntropy.SchemeAnalyticPrincipalCharts

/-! # Actual overlap refinement of analytic affine charts

Principal opens refine every genuine affine chart overlap. Their native
open-immersion lifts, together with actual principal analytic open embeddings,
prove the local continuity and open mapping needed for genuine global charts.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

namespace BingWangEntropy

noncomputable section

/-- Actual principal opens refine every overlap of genuine affine open charts. -/
theorem exists_complexAffine_overlap_principal {X : Scheme} (c d : ComplexAffineChart X)
    (y : Spec d.ring) (hy : d.map y ∈ Set.range c.map) :
    ∃ r : d.ring, y ∈ PrimeSpectrum.basicOpen r ∧
      Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map := by
  let U : Set (PrimeSpectrum d.ring) := d.map ⁻¹' Set.range c.map
  have hopen : IsOpen U := (IsOpenImmersion.isOpen_range c.map).preimage d.map.continuous
  obtain ⟨s, ⟨r, rfl⟩, hyr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy hopen
  refine ⟨r, hyr, ?_⟩
  rintro x ⟨z, rfl⟩
  change d.map (complexPrincipalSchemeMap r z) ∈ Set.range c.map
  apply hsub
  have hz : complexPrincipalSchemeMap r z ∈ Set.range (complexPrincipalSchemeMap r) := ⟨z, rfl⟩
  change complexPrincipalSchemeMap r z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum d.ring))
  exact Eq.mp (congrArg (fun S : Set (PrimeSpectrum d.ring) =>
    complexPrincipalSchemeMap r z ∈ S) (complexPrincipalSchemeMap_range r)) hz

/-- The genuine overlap principal chart maps into the other affine chart by
the native open-immersion universal property. -/
def complexAffine_overlap_lift {X : Scheme} (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    Spec (.of (Localization.Away r)) ⟶ Spec c.ring :=
  IsOpenImmersion.lift c.map (complexPrincipalSchemeMap r ≫ d.map) hr

/-- The overlap lift recovers the actual chart morphism upon composition. -/
theorem complexAffine_overlap_lift_fac {X : Scheme} (c d : ComplexAffineChart X)
    (r : d.ring) (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    complexAffine_overlap_lift c d r hr ≫ c.map = complexPrincipalSchemeMap r ≫ d.map :=
  IsOpenImmersion.lift_fac c.map (complexPrincipalSchemeMap r ≫ d.map) hr

/-- Its compatibility with the complex structural morphism is derived from
the actual overlap factorization. -/
theorem complexAffine_overlap_lift_over {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    complexAffine_overlap_lift c d r hr ≫ (c.map ≫ f) =
      (complexPrincipalSchemeMap r ≫ d.map) ≫ f := by
  rw [← Category.assoc, complexAffine_overlap_lift_fac]

/-- Actual affine morphisms over the field act continuously, with any genuine
structural compatibility equation. -/
theorem affineSchemePointMap_over_continuous {A B : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (g : Spec B ⟶ Spec (.of ℂ)) (h : Spec A ⟶ Spec B)
    (hh : h ≫ g = f) :
    Continuous[affineSchemePointTopologyOfStructure f, affineSchemePointTopologyOfStructure g]
      (schemeComplexPointMap f g h hh) := by
  have heq : schemeComplexPointMap (h ≫ g) g h rfl ∘
      Equiv.cast (congrArg SchemeComplexPoint hh.symm) = schemeComplexPointMap f g h hh := by
    funext p
    apply Subtype.ext
    change ((Equiv.cast (congrArg SchemeComplexPoint hh.symm)) p).val ≫ h = p.val ≫ h
    rw [schemeComplexPoint_cast_val hh.symm p]
  have hc := @Continuous.comp _ _ _ (affineSchemePointTopologyOfStructure f)
    (affineSchemePointTopologyOfStructure (h ≫ g)) (affineSchemePointTopologyOfStructure g) _ _
    (affineSchemePointMapOfStructure_continuous g h) (affineSchemePoint_cast_continuous hh.symm)
  exact heq ▸ hc

/-- The actual principal overlap lift acts on the genuine inherited complex points. -/
def complexAffine_overlap_pointMap {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) →
      ComplexAffineChartPoint f c :=
  schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) (c.map ≫ f)
    (complexAffine_overlap_lift c d r hr)
    ((complexAffine_overlap_lift_over f c d r hr).trans (Category.assoc _ _ _))

/-- The genuine overlap point map is continuous for the actual affine topologies. -/
theorem complexAffine_overlap_pointMap_continuous {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    Continuous[affineSchemePointTopologyOfStructure (complexPrincipalSchemeMap r ≫ (d.map ≫ f)),
      complexAffineChartPointTopology f c] (complexAffine_overlap_pointMap f c d r hr) :=
  affineSchemePointMap_over_continuous _ _ _ _

/-- Both genuine chart maps take the actual principal overlap point to the
same global complex scheme point. -/
theorem complexAffine_overlap_pointMap_fac {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f))) :
    complexAffineChartPointMap f c (complexAffine_overlap_pointMap f c d r hr p) =
      complexAffineChartPointMap f d
        (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
          (d.map ≫ f) (complexPrincipalSchemeMap r) rfl p) := by
  apply Subtype.ext
  change (p.val ≫ complexAffine_overlap_lift c d r hr) ≫ c.map =
    (p.val ≫ complexPrincipalSchemeMap r) ≫ d.map
  rw [Category.assoc, complexAffine_overlap_lift_fac, Category.assoc]

/-- Every genuine affine chart acts as an open map in the global analytic topology. -/
theorem complexAffineChartPointMap_isOpenMap {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) :
    letI := schemeAnalyticPointTopology f
    IsOpenMap (complexAffineChartPointMap f c) := by
  let := schemeAnalyticPointTopology f
  intro V hV
  change IsOpen (complexAffineChartsPointMap f ⁻¹' (complexAffineChartPointMap f c '' V))
  rw [isOpen_sigma_iff]
  intro d
  change IsOpen (complexAffineChartPointMap f d ⁻¹' (complexAffineChartPointMap f c '' V))
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hglobal := (schemeComplexPointChart f c.map x).property
  change schemeComplexPointImage f (complexAffineChartPointMap f c x) ∈ Set.range c.map at hglobal
  rw [hxp, schemeComplexPointImage_chart] at hglobal
  obtain ⟨r, hyr, hr⟩ := exists_complexAffine_overlap_principal c d
    (schemeComplexPointImage (d.map ≫ f) p) hglobal
  have hpRange : schemeComplexPointImage (d.map ≫ f) p ∈ Set.range (complexPrincipalSchemeMap r) :=
    Eq.mpr (congrArg (fun S : Set (PrimeSpectrum d.ring) =>
      schemeComplexPointImage (d.map ≫ f) p ∈ S) (complexPrincipalSchemeMap_range r)) hyr
  let q := schemeComplexPointLift (d.map ≫ f) (complexPrincipalSchemeMap r) p hpRange
  have hqp : schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
      (d.map ≫ f) (complexPrincipalSchemeMap r) rfl q = p := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac (d.map ≫ f) (complexPrincipalSchemeMap r) p hpRange
  have hqx : complexAffine_overlap_pointMap f c d r hr q = x := by
    apply complexAffineChartPointMap_injective f c
    exact (complexAffine_overlap_pointMap_fac f c d r hr q).trans
      ((congrArg (complexAffineChartPointMap f d) hqp).trans hxp.symm)
  let := affineSchemePointTopologyOfStructure (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
  let W : Set (ComplexAffineChartPoint f d) :=
    schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
      (d.map ≫ f) (complexPrincipalSchemeMap r) rfl ''
      (complexAffine_overlap_pointMap f c d r hr ⁻¹' V)
  have hW : IsOpen W :=
    (complexPrincipalSchemePointMap_isOpenEmbedding (d.map ≫ f) r).isOpenMap _
      (hV.preimage (complexAffine_overlap_pointMap_continuous f c d r hr))
  have hqxV : complexAffine_overlap_pointMap f c d r hr q ∈ V :=
    Eq.mpr (congrArg (fun y => y ∈ V) hqx) hx
  have hpW : p ∈ W := ⟨q, hqxV, hqp⟩
  apply Filter.mem_of_superset (hW.mem_nhds hpW)
  rintro p' ⟨q', hq', rfl⟩
  exact ⟨complexAffine_overlap_pointMap f c d r hr q', hq',
    complexAffine_overlap_pointMap_fac f c d r hr q'⟩

/-- The genuine global affine charts are actual analytic open embeddings. -/
theorem complexAffineChartPointMap_isOpenEmbedding {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) :
    letI := schemeAnalyticPointTopology f
    Topology.IsOpenEmbedding (complexAffineChartPointMap f c) := by
  let := schemeAnalyticPointTopology f
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (complexAffineChartPointMap_continuous f c)
    (complexAffineChartPointMap_injective f c) (complexAffineChartPointMap_isOpenMap f c)

end

end BingWangEntropy
