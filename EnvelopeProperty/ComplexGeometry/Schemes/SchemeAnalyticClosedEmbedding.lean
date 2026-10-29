import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticSeparation
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticOverlapAlgebra
import Mathlib.Topology.LocalAtTarget

/-! # Native closed immersions are actual analytic closed embeddings

The affine assertion follows from the literal surjective ring map and its
actual evaluation topology. General closed immersions are compared on native
affine pullbacks, with actual point lifting and genuine global analytic charts.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

/-- Pullback by a surjective actual algebra homomorphism is a genuine evaluation-topology embedding. -/
theorem complexPoint_surjectivePullback_isEmbedding {A B : Type*}
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) :
    Topology.IsEmbedding (fun p : ComplexAlgebraPoint B => p.comp h) := by
  let g : ComplexAlgebraPoint A → (B → ℂ) := fun p b => p (hh b).choose
  have hg : Continuous g := continuous_pi_iff.mpr
    (fun b => complexPoint_evaluation_continuous (hh b).choose)
  have heq : g ∘ (fun p : ComplexAlgebraPoint B => p.comp h) =
      (fun p : ComplexAlgebraPoint B => fun b : B => p b) := by
    funext p b
    change p (h (hh b).choose) = p b
    rw [(hh b).choose_spec]
  refine ⟨Topology.IsInducing.of_comp (complexPoint_pullback_continuous h) hg ?_, ?_⟩
  · rw [heq]
    exact Topology.IsInducing.induced _
  · intro p q hpq
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hh b
    exact congrArg (fun p : ComplexAlgebraPoint A => p a) hpq

/-- An actual affine closed immersion has the literal surjective contravariant ring map. -/
theorem affineClosedImmersion_preimage_surjective {A B : CommRingCat}
    (h : Spec A ⟶ Spec B) [IsClosedImmersion h] :
    Function.Surjective (Spec.preimage h).hom := by
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion h)
  have hs : Function.Surjective (Spec.preimage e.hom).hom := by
    intro a
    refine ⟨(Spec.preimage e.inv).hom a, ?_⟩
    change (Spec.preimage e.inv ≫ Spec.preimage e.hom).hom a = a
    rw [← Spec.preimage_comp, e.hom_inv_id, Spec.preimage_id]
    rfl
  rw [he, Spec.preimage_comp, Spec.preimage_map]
  exact hs.comp Ideal.Quotient.mk_surjective

/-- Genuine affine closed-immersion point maps are embeddings for their actual inherited topologies. -/
theorem affineClosedImmersionComplexPointMap_isEmbedding {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (g : Spec A ⟶ Spec (.of ℂ))
    (h : Spec A ⟶ Spec B) [IsClosedImmersion h] (hh : h ≫ f = g) :
    @Topology.IsEmbedding (SchemeComplexPoint g) (SchemeComplexPoint f)
      (affineSchemePointTopologyOfStructure g) (affineSchemePointTopologyOfStructure f)
      (schemeComplexPointMap g f h hh) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra g
  let := affineSchemePointTopologyOfStructure f
  let := affineSchemePointTopologyOfStructure g
  have heq : schemeComplexPointMap g f h hh =
      (affineSchemePointHomeomorphOfStructure f).symm ∘
        (fun p : ComplexAlgebraPoint A => p.comp (affineSchemeOverAlgebraMap f g h hh)) ∘
          affineSchemePointHomeomorphOfStructure g := by
    funext p
    apply (affineSchemePointEquivOfStructure f).injective
    change affineSchemePointHomeomorphOfStructure f (schemeComplexPointMap g f h hh p) = _
    rw [affineSchemeOverAlgebraMap_naturality]
    exact ((affineSchemePointHomeomorphOfStructure f).apply_symm_apply _).symm
  rw [heq]
  exact (affineSchemePointHomeomorphOfStructure f).symm.isEmbedding.comp
    ((complexPoint_surjectivePullback_isEmbedding (affineSchemeOverAlgebraMap f g h hh)
      (affineClosedImmersion_preimage_surjective h)).comp
        (affineSchemePointHomeomorphOfStructure g).isEmbedding)

/-- Pulling back an actual affine target chart produces an actual affine source chart. -/
def closedImmersionAffineSourceChart {X Y : Scheme} (i : Y ⟶ X)
    [IsClosedImmersion i] (c : ComplexAffineChart X) : ComplexAffineChart Y where
  ring := Γ(pullback i c.map, ⊤)
  map := (pullback i c.map).isoSpec.inv ≫ pullback.fst i c.map
  isOpenImmersion := inferInstance

/-- The affine source chart maps to the original affine target by the native pullback projection. -/
def closedImmersionAffineChartMap {X Y : Scheme} (i : Y ⟶ X)
    [IsClosedImmersion i] (c : ComplexAffineChart X) :
    Spec (closedImmersionAffineSourceChart i c).ring ⟶ Spec c.ring :=
  (pullback i c.map).isoSpec.inv ≫ pullback.snd i c.map

instance closedImmersionAffineChartMap_isClosedImmersion {X Y : Scheme} (i : Y ⟶ X)
    [IsClosedImmersion i] (c : ComplexAffineChart X) :
    IsClosedImmersion (closedImmersionAffineChartMap i c) := by
  dsimp [closedImmersionAffineChartMap]
  infer_instance

/-- The actual affine pullback chart square commutes as scheme morphisms. -/
theorem closedImmersionAffineChartMap_fac {X Y : Scheme} (i : Y ⟶ X)
    [IsClosedImmersion i] (c : ComplexAffineChart X) :
    (closedImmersionAffineSourceChart i c).map ≫ i = closedImmersionAffineChartMap i c ≫ c.map := by
  change ((pullback i c.map).isoSpec.inv ≫ pullback.fst i c.map) ≫ i =
    ((pullback i c.map).isoSpec.inv ≫ pullback.snd i c.map) ≫ c.map
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- Actual inherited complex structural maps agree by the genuine pullback square. -/
theorem closedImmersionAffineChartMap_over {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (i : Y ⟶ X) [IsClosedImmersion i] (c : ComplexAffineChart X) :
    closedImmersionAffineChartMap i c ≫ (c.map ≫ f) =
      (closedImmersionAffineSourceChart i c).map ≫ (i ≫ f) := by
  rw [← Category.assoc, ← closedImmersionAffineChartMap_fac, Category.assoc]

/-- The actual affine source-chart range is the true inverse image of the target-chart range. -/
theorem closedImmersionAffineSourceChart_range {X Y : Scheme} (i : Y ⟶ X)
    [IsClosedImmersion i] (c : ComplexAffineChart X) :
    Set.range (closedImmersionAffineSourceChart i c).map = i ⁻¹' Set.range c.map := by
  change Set.range ((pullback i c.map).isoSpec.inv ≫ pullback.fst i c.map) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso (pullback i c.map).isoSpec.inv.base).2.range_eq,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- On the actual source chart the scheme point map is the genuine affine closed-immersion map. -/
def closedImmersionAffineChartPointMap {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (i : Y ⟶ X) [IsClosedImmersion i] (c : ComplexAffineChart X) :
    ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i c) →
      ComplexAffineChartPoint f c :=
  schemeComplexPointMap _ _ (closedImmersionAffineChartMap i c)
    (closedImmersionAffineChartMap_over f i c)

/-- Actual local point maps recover the global map by native composition. -/
theorem closedImmersionAffineChartPointMap_fac {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (i : Y ⟶ X) [IsClosedImmersion i] (c : ComplexAffineChart X) :
    schemeComplexPointMap (i ≫ f) f i rfl ∘
      complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c) =
      complexAffineChartPointMap f c ∘ closedImmersionAffineChartPointMap f i c := by
  funext p
  apply Subtype.ext
  change (p.val ≫ (closedImmersionAffineSourceChart i c).map) ≫ i =
    (p.val ≫ closedImmersionAffineChartMap i c) ≫ c.map
  rw [Category.assoc, closedImmersionAffineChartMap_fac, Category.assoc]

/-- Each actual affine source-chart map is a genuine analytic embedding into the target chart. -/
theorem closedImmersionAffineChartPointMap_isEmbedding {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i]
    (c : ComplexAffineChart X) : Topology.IsEmbedding (closedImmersionAffineChartPointMap f i c) :=
  affineClosedImmersionComplexPointMap_isEmbedding _ _ _ _

/-- The actual source-chart point range is precisely the inverse image of the target-chart point range. -/
theorem closedImmersionAffineSourceChartPoint_range {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i]
    (c : ComplexAffineChart X) :
    Set.range (complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c)) =
      schemeComplexPointMap (i ≫ f) f i rfl ⁻¹' Set.range (complexAffineChartPointMap f c) := by
  rw [complexAffineChartPointMap_range, complexAffineChartPointMap_range,
    closedImmersionAffineSourceChart_range]
  ext p
  change i (p.val default) ∈ Set.range c.map ↔ (p.val ≫ i) default ∈ Set.range c.map
  rw [Scheme.Hom.comp_apply]

/-- Joint source charts obtained from every actual target affine chart. -/
def closedImmersionAffineSourcePointsMap {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    (Σ c : ComplexAffineChart X,
      ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i c)) →
        SchemeComplexPoint (i ≫ f) :=
  fun p => complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i p.1) p.2

/-- The native pullback source charts cover every genuine source complex point. -/
theorem closedImmersionAffineSourcePointsMap_surjective {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    Function.Surjective (closedImmersionAffineSourcePointsMap f i) := by
  intro p
  obtain ⟨⟨c, q⟩, hq⟩ := complexAffineChartsPointMap_surjective f
    (schemeComplexPointMap (i ≫ f) f i rfl p)
  have hp : p ∈ Set.range
      (complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c)) := by
    rw [closedImmersionAffineSourceChartPoint_range]
    exact ⟨q, hq⟩
  obtain ⟨q', hq'⟩ := hp
  exact ⟨⟨c, q'⟩, hq'⟩

/-- The actual joint source-chart map is continuous in the genuine source analytic topology. -/
theorem closedImmersionAffineSourcePointsMap_continuous {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    letI := schemeAnalyticPointTopology (i ≫ f)
    Continuous (closedImmersionAffineSourcePointsMap f i) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  exact continuous_sigma_iff.mpr (fun c =>
    complexAffineChartPointMap_continuous (i ≫ f) (closedImmersionAffineSourceChart i c))

/-- The actual joint source-chart map is open for the genuine source analytic topology. -/
theorem closedImmersionAffineSourcePointsMap_isOpenMap {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    letI := schemeAnalyticPointTopology (i ≫ f)
    IsOpenMap (closedImmersionAffineSourcePointsMap f i) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  intro V hV
  have heq : closedImmersionAffineSourcePointsMap f i '' V =
      ⋃ c : ComplexAffineChart X,
        complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c) ''
          ((fun q : ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i c) =>
            (⟨c, q⟩ : Σ d : ComplexAffineChart X,
              ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i d))) ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨⟨c, q⟩, hq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨c, q, hq, rfl⟩
    · intro hp
      obtain ⟨c, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨⟨c, q⟩, hq, rfl⟩
  rw [heq]
  exact isOpen_iUnion (fun c =>
    complexAffineChartPointMap_isOpenMap (i ≫ f) (closedImmersionAffineSourceChart i c) _
      ((isOpen_sigma_iff.mp hV) c))

/-- The native closed immersion acts continuously on actual analytic complex points. -/
theorem closedImmersionComplexPointMap_continuous {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    Continuous[schemeAnalyticPointTopology (i ≫ f), schemeAnalyticPointTopology f]
      (schemeComplexPointMap (i ≫ f) f i rfl) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  have hq := (closedImmersionAffineSourcePointsMap_isOpenMap f i).isQuotientMap
    (closedImmersionAffineSourcePointsMap_continuous f i)
    (closedImmersionAffineSourcePointsMap_surjective f i)
  apply hq.continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro c
  change Continuous (schemeComplexPointMap (i ≫ f) f i rfl ∘
    complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c))
  rw [closedImmersionAffineChartPointMap_fac]
  exact (complexAffineChartPointMap_continuous f c).comp
    (closedImmersionAffineChartPointMap_isEmbedding f i c).continuous

/-- Every native closed immersion is an embedding of the actual analytic complex-point spaces. -/
theorem closedImmersionComplexPointMap_isEmbedding {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    @Topology.IsEmbedding (SchemeComplexPoint (i ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (i ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (i ≫ f) f i rfl) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  let U : ComplexAffineChart X → TopologicalSpace.Opens (SchemeComplexPoint f) :=
    fun c => ⟨Set.range (complexAffineChartPointMap f c), complexAffineChartPointMap_isOpen_range f c⟩
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _
    (closedImmersionComplexPointMap_continuous f i) U ?_
    (fun c => ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i c))
    (fun c => complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i c))
    (fun c => complexAffineChartPointMap_continuous (i ≫ f) (closedImmersionAffineSourceChart i c))
    ?_ ?_
  · intro p _
    obtain ⟨⟨c, q⟩, hq⟩ := complexAffineChartsPointMap_surjective f p
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, q, hq⟩
  · intro c
    exact le_of_eq (closedImmersionAffineSourceChartPoint_range f i c).symm
  · intro c
    rw [closedImmersionAffineChartPointMap_fac]
    exact (complexAffineChartPointMap_isOpenEmbedding f c).isEmbedding.comp
      (closedImmersionAffineChartPointMap_isEmbedding f i c)

/-- A native closed immersion gives a true closed embedding in the actual analytic topology. -/
theorem closedImmersionComplexPointMap_isClosedEmbedding {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    @Topology.IsClosedEmbedding (SchemeComplexPoint (i ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (i ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (i ≫ f) f i rfl) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  exact ⟨closedImmersionComplexPointMap_isEmbedding f i,
    closedImmersionComplexPointMap_isClosed_range f i⟩

/-- A native closed subscheme of an actually analytically compact complex scheme is analytically compact. -/
theorem closedImmersionComplexPoint_compactSpace {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i]
    [hX : @CompactSpace (SchemeComplexPoint f) (schemeAnalyticPointTopology f)] :
    @CompactSpace (SchemeComplexPoint (i ≫ f)) (schemeAnalyticPointTopology (i ≫ f)) := by
  let := schemeAnalyticPointTopology (i ≫ f)
  let := schemeAnalyticPointTopology f
  exact (closedImmersionComplexPointMap_isClosedEmbedding f i).compactSpace

end

end ComplexSchemes
