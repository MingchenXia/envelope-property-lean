import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticTopology
import EnvelopeProperty.ComplexGeometry.Schemes.AffineComplexLocalization

/-! # Actual analytic open images of scheme charts

The underlying image of a genuine complex point is continuous to the Zariski
scheme space because basic-open preimages are evaluation nonvanishing loci.
Consequently the image of every genuine affine open chart is analytically open.
Proving the full chart open embedding requires the overlap comparison as well.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

namespace ComplexSchemes

noncomputable section

/-- Transporting the structural compatibility equation preserves the actual point morphism. -/
theorem schemeComplexPoint_cast_val {X : Scheme} {f g : X ⟶ Spec (.of ℂ)}
    (e : f = g) (p : SchemeComplexPoint f) :
    ((Equiv.cast (congrArg SchemeComplexPoint e)) p).val = p.val := by
  cases e
  rfl

/-- The arbitrary affine structural equivalence recovers the literal ring map. -/
theorem affineSchemePointEquivOfStructure_apply {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) (a : A) :
    letI := affinePointFieldAlgebra f
    affineSchemePointEquivOfStructure f p a = (Spec.preimage p.val).hom a := by
  change (Spec.preimage ((Equiv.cast
    (congrArg SchemeComplexPoint (affinePointFieldAlgebra_structure f).symm)) p).val).hom a = _
  rw [schemeComplexPoint_cast_val (affinePointFieldAlgebra_structure f).symm p]

/-- Spec full faithfulness derives the complex algebra map from an actual affine scheme morphism. -/
def affineSchemeMorphismAlgebraMap {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (h : Spec A ⟶ Spec B) :
    letI := affinePointFieldAlgebra f
    letI := affinePointFieldAlgebra (h ≫ f)
    B →ₐ[ℂ] A := by
  letI := affinePointFieldAlgebra f
  letI := affinePointFieldAlgebra (h ≫ f)
  exact
    { (Spec.preimage h).hom with
      commutes' c := by
        change (Spec.preimage h).hom ((Spec.preimage f).hom c) =
          (Spec.preimage (h ≫ f)).hom c
        rw [Spec.preimage_comp]
        rfl }

/-- Under genuine affine point equivalences, actual scheme composition is actual algebra pullback. -/
theorem affineSchemePointEquivOfStructure_naturality {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (h : Spec A ⟶ Spec B)
    (p : SchemeComplexPoint (h ≫ f)) :
    letI := affinePointFieldAlgebra f
    letI := affinePointFieldAlgebra (h ≫ f)
    affineSchemePointEquivOfStructure f
      (schemeComplexPointMap (h ≫ f) f h rfl p) =
      (affineSchemePointEquivOfStructure (h ≫ f) p).comp (affineSchemeMorphismAlgebraMap f h) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra (h ≫ f)
  apply AlgHom.ext
  intro b
  rw [affineSchemePointEquivOfStructure_apply, AlgHom.comp_apply,
    affineSchemePointEquivOfStructure_apply]
  change (Spec.preimage (p.val ≫ h)).hom b =
    (Spec.preimage p.val).hom ((Spec.preimage h).hom b)
  rw [Spec.preimage_comp]
  rfl

/-- Every actual affine scheme morphism is continuous for its inherited evaluation topologies. -/
theorem affineSchemePointMapOfStructure_continuous {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (h : Spec A ⟶ Spec B) :
    letI := affineSchemePointTopologyOfStructure (h ≫ f)
    letI := affineSchemePointTopologyOfStructure f
    Continuous (schemeComplexPointMap (h ≫ f) f h rfl) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra (h ≫ f)
  let := affineSchemePointTopologyOfStructure f
  let := affineSchemePointTopologyOfStructure (h ≫ f)
  have heq : schemeComplexPointMap (h ≫ f) f h rfl = fun p =>
      (affineSchemePointHomeomorphOfStructure f).symm
        (((affineSchemePointHomeomorphOfStructure (h ≫ f)) p).comp
          (affineSchemeMorphismAlgebraMap f h)) := by
    funext p
    apply (affineSchemePointHomeomorphOfStructure f).injective
    rw [Homeomorph.apply_symm_apply]
    exact affineSchemePointEquivOfStructure_naturality f h p
  rw [heq]
  exact (affineSchemePointHomeomorphOfStructure f).symm.continuous.comp
    ((complexPoint_pullback_continuous (affineSchemeMorphismAlgebraMap f h)).comp
      (affineSchemePointHomeomorphOfStructure (h ≫ f)).continuous)

/-- Structural equality transports genuine affine points continuously. -/
theorem affineSchemePoint_cast_continuous {A : CommRingCat}
    {f g : Spec A ⟶ Spec (.of ℂ)} (e : f = g) :
    Continuous[affineSchemePointTopologyOfStructure f, affineSchemePointTopologyOfStructure g]
      (Equiv.cast (congrArg SchemeComplexPoint e)) := by
  cases e
  let := affineSchemePointTopologyOfStructure f
  exact continuous_id

/-- On an actual affine scheme the global chart construction gives exactly its
proved evaluation topology. -/
theorem schemeAnalyticPointTopology_affine {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) :
    schemeAnalyticPointTopology f = affineSchemePointTopologyOfStructure f := by
  apply le_antisymm
  · let := affineSchemePointTopologyOfStructure f
    apply continuous_iff_coinduced_le.mp
    apply continuous_sigma_iff.mpr
    intro c
    exact affineSchemePointMapOfStructure_continuous f c.map
  · let := schemeAnalyticPointTopology f
    let c : ComplexAffineChart (Spec A) := ⟨A, 𝟙 _, inferInstance⟩
    have hc := complexAffineChartPointMap_continuous f c
    have hid : Continuous[affineSchemePointTopologyOfStructure f, schemeAnalyticPointTopology f]
        (complexAffineChartPointMap f c ∘
          Equiv.cast (congrArg SchemeComplexPoint (Category.id_comp f).symm)) :=
      @Continuous.comp _ _ _ (affineSchemePointTopologyOfStructure f)
        (complexAffineChartPointTopology f c) (schemeAnalyticPointTopology f) _ _
        hc (affineSchemePoint_cast_continuous (Category.id_comp f).symm)
    have heq : complexAffineChartPointMap f c ∘
        Equiv.cast (congrArg SchemeComplexPoint (Category.id_comp f).symm) =
        (id : SchemeComplexPoint f → SchemeComplexPoint f) := by
      funext p
      apply Subtype.ext
      change ((Equiv.cast (congrArg SchemeComplexPoint (Category.id_comp f).symm)) p).val ≫
        𝟙 (Spec A) = p.val
      rw [schemeComplexPoint_cast_val (Category.id_comp f).symm p, Category.comp_id]
    rw [heq] at hid
    simpa only [coinduced_id] using continuous_iff_coinduced_le.mp hid

/-- The actual underlying image lies in a Zariski principal open precisely when
its actual affine point evaluation is nonzero. -/
theorem affineSchemePointImage_mem_basicOpen {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) (a : A) :
    letI := affinePointFieldAlgebra f
    schemeComplexPointImage f p ∈ PrimeSpectrum.basicOpen a ↔
      affineSchemePointEquivOfStructure f p a ≠ 0 := by
  let := affinePointFieldAlgebra f
  rw [affineSchemePointEquivOfStructure_apply]
  change p.val default ∈ PrimeSpectrum.basicOpen a ↔ _
  nth_rw 1 [← Spec.map_preimage p.val]
  change default ∈ (Spec.map (Spec.preimage p.val) ⁻¹ᵁ PrimeSpectrum.basicOpen a) ↔ _
  rw [SpecMap_preimage_basicOpen]
  change default ∈ PrimeSpectrum.basicOpen ((Spec.preimage p.val).hom a) ↔ _
  rw [PrimeSpectrum.mem_basicOpen (R := ℂ)]
  have hd : (default : Spec (.of ℂ)).asIdeal = (⊥ : Ideal ℂ) := by
    calc
      (default : Spec (.of ℂ)).asIdeal = (⊥ : PrimeSpectrum ℂ).asIdeal :=
        congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (default : Spec (.of ℂ)) (⊥ : PrimeSpectrum ℂ))
      _ = ⊥ := PrimeSpectrum.asIdeal_bot
  have hm : (Spec.preimage p.val).hom a ∈ (default : Spec (.of ℂ)).asIdeal ↔
      (Spec.preimage p.val).hom a = 0 := hd.symm ▸ Ideal.mem_bot
  exact not_congr hm

/-- The genuine affine scheme point's underlying image is continuous to the
actual Zariski spectrum for the evaluation topology. -/
theorem affineSchemePointImage_continuous {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) :
    Continuous[affineSchemePointTopologyOfStructure f, inferInstance]
      (schemeComplexPointImage f) := by
  let := affinePointFieldAlgebra f
  let := affineSchemePointTopologyOfStructure f
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro s ⟨a, rfl⟩
  have heq : schemeComplexPointImage f ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      {p | affineSchemePointEquivOfStructure f p a ≠ 0} := by
    ext p
    exact affineSchemePointImage_mem_basicOpen f p a
  have hopen : IsOpen {p | affineSchemePointEquivOfStructure f p a ≠ 0} :=
    isOpen_ne_fun
      ((complexPoint_evaluation_continuous a).comp
        (affineSchemePointHomeomorphOfStructure f).continuous) continuous_const
  exact heq.symm ▸ hopen

/-- Underlying point images commute with every genuine affine chart map. -/
theorem schemeComplexPointImage_chart {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) (p : ComplexAffineChartPoint f c) :
    schemeComplexPointImage f (complexAffineChartPointMap f c p) =
      c.map (schemeComplexPointImage (c.map ≫ f) p) :=
  Scheme.Hom.comp_apply p.val c.map default

/-- The global genuine complex point's image is continuous to the actual
Zariski scheme space. -/
theorem schemeComplexPointImage_continuous {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    letI := schemeAnalyticPointTopology f
    Continuous (schemeComplexPointImage f) := by
  let := schemeAnalyticPointTopology f
  apply (schemeAnalyticPoint_continuous_iff f (schemeComplexPointImage f)).mpr
  intro c
  convert c.map.continuous.comp (affineSchemePointImage_continuous (c.map ≫ f)) using 1
  all_goals rfl

/-- Actual affine chart points have exactly the expected global image subset. -/
theorem complexAffineChartPointMap_range {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) :
    Set.range (complexAffineChartPointMap f c) =
      {p | schemeComplexPointImage f p ∈ Set.range c.map} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (schemeComplexPointChart f c.map q).property
  · intro hp
    refine ⟨schemeComplexPointLift f c.map p hp, ?_⟩
    apply Subtype.ext
    exact schemeComplexPointLift_fac f c.map p hp

/-- Actual open-immersion injectivity gives genuine point-chart injectivity. -/
theorem complexAffineChartPointMap_injective {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) : Function.Injective (complexAffineChartPointMap f c) := by
  intro p q h
  apply Subtype.ext
  apply (cancel_mono c.map).mp
  exact congrArg Subtype.val h

/-- Every genuine affine chart has open image in the global analytic point topology. -/
theorem complexAffineChartPointMap_isOpen_range {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) :
    letI := schemeAnalyticPointTopology f
    IsOpen (Set.range (complexAffineChartPointMap f c)) := by
  let := schemeAnalyticPointTopology f
  rw [complexAffineChartPointMap_range]
  exact (IsOpenImmersion.isOpen_range c.map).preimage (schemeComplexPointImage_continuous f)

end

end ComplexSchemes
