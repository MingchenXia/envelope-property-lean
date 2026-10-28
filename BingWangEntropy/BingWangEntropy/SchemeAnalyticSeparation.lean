import BingWangEntropy.SchemeAnalyticOverlapAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Maps.OpenQuotient

/-! # Separation of actual complex scheme points

Closed immersion images are detected by genuine quotient ideals. The closed
native diagonal of a separated scheme morphism gives a closed equality locus
on the actual complex-point carrier with its affine evaluation topology.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped TensorProduct

namespace BingWangEntropy

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Two complex algebra points with the same actual kernel are equal. -/
theorem complexAlgebraPoint_eq_of_ker_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    (p q : ComplexAlgebraPoint A) (hpq : RingHom.ker p.toRingHom = RingHom.ker q.toRingHom) :
    p = q := by
  apply AlgHom.ext
  intro a
  have hm : a - algebraMap ℂ A (p a) ∈ RingHom.ker p.toRingHom := by
    change p (a - algebraMap ℂ A (p a)) = 0
    simp only [map_sub, p.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [hpq] at hm
  change q (a - algebraMap ℂ A (p a)) = 0 at hm
  have he : q a - p a = 0 := by
    simpa only [map_sub, q.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hm
  exact (sub_eq_zero.mp he).symm

/-- The genuine underlying prime of an actual complex affine point is exactly
its evaluation kernel. -/
theorem affineSchemePointImage_asIdeal {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra f
    (schemeComplexPointImage f p).asIdeal =
      RingHom.ker (affineSchemePointHomeomorphOfStructure f p).toRingHom := by
  let := affinePointFieldAlgebra f
  have hd : (default : Spec (.of ℂ)).asIdeal = (⊥ : Ideal ℂ) := by
    calc
      (default : Spec (.of ℂ)).asIdeal = (⊥ : PrimeSpectrum ℂ).asIdeal :=
        congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (default : Spec (.of ℂ)) (⊥ : PrimeSpectrum ℂ))
      _ = ⊥ := PrimeSpectrum.asIdeal_bot
  ext a
  change a ∈ (p.val default).asIdeal ↔ _
  nth_rw 1 [← Spec.map_preimage p.val]
  change (Spec.preimage p.val).hom a ∈ (default : Spec (.of ℂ)).asIdeal ↔ _
  rw [hd]
  change (Spec.preimage p.val).hom a = 0 ↔
    affineSchemePointHomeomorphOfStructure f p a = 0
  change (Spec.preimage p.val).hom a = 0 ↔ affineSchemePointEquivOfStructure f p a = 0
  rw [affineSchemePointEquivOfStructure_apply]

/-- The actual underlying image uniquely identifies a complex point of an
affine scheme over the complex field. -/
theorem affineSchemeComplexPointImage_injective {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) : Function.Injective (schemeComplexPointImage f) := by
  let := affinePointFieldAlgebra f
  intro p q hpq
  apply (affineSchemePointEquivOfStructure f).injective
  apply complexAlgebraPoint_eq_of_ker_eq
  exact (affineSchemePointImage_asIdeal f p).symm.trans
    ((congrArg PrimeSpectrum.asIdeal hpq).trans (affineSchemePointImage_asIdeal f q))

/-- The actual underlying image uniquely identifies a complex point of any
scheme over the complex field. -/
theorem schemeComplexPointImage_injective {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    Function.Injective (schemeComplexPointImage f) := by
  intro p q hpq
  obtain ⟨R, g, hg, y, hy⟩ := X.exists_Spec_apply_eq (schemeComplexPointImage f p)
  let c : ComplexAffineChart X := ⟨R, g, hg⟩
  have hp : schemeComplexPointImage f p ∈ Set.range c.map := ⟨y, hy⟩
  have hq : schemeComplexPointImage f q ∈ Set.range c.map := hpq ▸ hp
  let pc := schemeComplexPointLift f c.map p hp
  let qc := schemeComplexPointLift f c.map q hq
  have hpc : complexAffineChartPointMap f c pc = p := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac f c.map p hp
  have hqc : complexAffineChartPointMap f c qc = q := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac f c.map q hq
  have hlocal : schemeComplexPointImage (c.map ≫ f) pc =
      schemeComplexPointImage (c.map ≫ f) qc := by
    apply c.map.isOpenEmbedding.injective
    rw [← schemeComplexPointImage_chart, ← schemeComplexPointImage_chart, hpc, hqc, hpq]
  exact hpc.symm.trans ((congrArg (complexAffineChartPointMap f c)
    (affineSchemeComplexPointImage_injective (c.map ≫ f) hlocal)).trans hqc)

/-- A genuine complex affine point in the underlying image of a native
closed immersion factors through that actual closed subscheme. -/
theorem exists_affineClosedImmersionComplexPoint {Y : Scheme} {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (i : Y ⟶ Spec A) [IsClosedImmersion i]
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ Set.range i) :
    ∃ q : SchemeComplexPoint (i ≫ f),
      schemeComplexPointMap (i ≫ f) f i rfl q = p := by
  let := affinePointFieldAlgebra f
  obtain ⟨I, e, hi⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i)
  obtain ⟨y, hy⟩ := hp
  have hI : ∀ a ∈ I, (Spec.preimage p.val).hom a = 0 := by
    intro a ha
    have hm : a ∈ (schemeComplexPointImage f p).asIdeal := by
      rw [← hy, hi, Scheme.Hom.comp_apply]
      change Ideal.Quotient.mk I a ∈ (e.hom y).asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact Ideal.zero_mem _
    rw [affineSchemePointImage_asIdeal] at hm
    change affineSchemePointHomeomorphOfStructure f p a = 0 at hm
    change affineSchemePointEquivOfStructure f p a = 0 at hm
    rwa [affineSchemePointEquivOfStructure_apply] at hm
  let φ := Ideal.Quotient.lift I (Spec.preimage p.val).hom hI
  let qval : Spec (.of ℂ) ⟶ Y := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
  have hfac : qval ≫ i = p.val := by
    rw [hi]
    simp only [qval, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp]
    have hmap : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom φ =
        Spec.preimage p.val := by
      ext a
      exact Ideal.Quotient.lift_mk I _ hI
    rw [hmap, Spec.map_preimage]
  refine ⟨⟨qval, ?_⟩, ?_⟩
  · rw [← Category.assoc, hfac, p.property]
  · apply Subtype.ext
    exact hfac

/-- Every actual point in the underlying image of a general native closed
immersion has a genuine complex-point lift, derived on an actual affine chart. -/
theorem exists_closedImmersionComplexPoint {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i]
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ Set.range i) :
    ∃ q : SchemeComplexPoint (i ≫ f),
      schemeComplexPointMap (i ≫ f) f i rfl q = p := by
  obtain ⟨R, g, hg, y, hy⟩ := X.exists_Spec_apply_eq (schemeComplexPointImage f p)
  let c : ComplexAffineChart X := ⟨R, g, hg⟩
  have hpChart : schemeComplexPointImage f p ∈ Set.range c.map := ⟨y, hy⟩
  let pc := schemeComplexPointLift f c.map p hpChart
  have hpc : complexAffineChartPointMap f c pc = p := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac f c.map p hpChart
  have hpClosed : schemeComplexPointImage (c.map ≫ f) pc ∈
      Set.range (pullback.snd i c.map) := by
    rw [Scheme.Pullback.range_snd]
    change c.map (schemeComplexPointImage (c.map ≫ f) pc) ∈ Set.range i
    rw [← schemeComplexPointImage_chart, hpc]
    exact hp
  obtain ⟨qc, hqc⟩ := exists_affineClosedImmersionComplexPoint (c.map ≫ f)
    (pullback.snd i c.map) pc hpClosed
  have hfac : (qc.val ≫ pullback.fst i c.map) ≫ i = p.val := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hqcval : qc.val ≫ pullback.snd i c.map = pc.val := congrArg Subtype.val hqc
    rw [hqcval]
    exact schemeComplexPointLift_fac f c.map p hpChart
  refine ⟨⟨qc.val ≫ pullback.fst i c.map, ?_⟩, ?_⟩
  · rw [← Category.assoc, hfac, p.property]
  · apply Subtype.ext
    exact hfac

/-- The genuine image of a native closed immersion on complex points is
exactly the underlying closed-image condition. -/
theorem closedImmersionComplexPointMap_range {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    Set.range (schemeComplexPointMap (i ≫ f) f i rfl) =
      {p | schemeComplexPointImage f p ∈ Set.range i} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨schemeComplexPointImage (i ≫ f) q, ?_⟩
    exact (Scheme.Hom.comp_apply q.val i default).symm
  · exact exists_closedImmersionComplexPoint f i p

/-- A native closed immersion has a closed image in the actual analytic
topology, derived from its genuine point image and actual underlying-image continuity. -/
theorem closedImmersionComplexPointMap_isClosed_range {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) [IsClosedImmersion i] :
    letI := schemeAnalyticPointTopology f
    IsClosed (Set.range (schemeComplexPointMap (i ≫ f) f i rfl)) := by
  let := schemeAnalyticPointTopology f
  rw [closedImmersionComplexPointMap_range]
  exact i.isClosedEmbedding.isClosed_range.preimage (schemeComplexPointImage_continuous f)

/-- The inverse inherited affine point equivalence has the literal native
Spec morphism of its actual algebra point. -/
theorem affineSchemePointHomeomorphOfStructure_symm_val {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) :
    letI := affinePointFieldAlgebra f
    letI := affineSchemePointTopologyOfStructure f
    ∀ p : ComplexAlgebraPoint A,
      ((affineSchemePointHomeomorphOfStructure f).symm p).val =
        Spec.map (CommRingCat.ofHom p.toRingHom) := by
  let := affinePointFieldAlgebra f
  let := affineSchemePointTopologyOfStructure f
  intro p
  rw [← Spec.map_preimage ((affineSchemePointHomeomorphOfStructure f).symm p).val]
  congr 1
  ext a
  calc
    (Spec.preimage ((affineSchemePointHomeomorphOfStructure f).symm p).val).hom a =
        affineSchemePointEquivOfStructure f ((affineSchemePointHomeomorphOfStructure f).symm p) a :=
      (affineSchemePointEquivOfStructure_apply f _ a).symm
    _ = p a := congrArg (fun q : ComplexAlgebraPoint A => q a)
      ((affineSchemePointHomeomorphOfStructure f).apply_symm_apply p)

/-- A pair of actual complex algebra points evaluates the genuine tensor
product by the native algebra universal property. -/
def complexTensorPoint {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    ComplexAlgebraPoint (A ⊗[ℂ] B) :=
  Algebra.TensorProduct.lift p q (fun a b => Commute.all (p a) (q b))

/-- A pure tensor is evaluated by the actual product of its two evaluations. -/
@[simp]
theorem complexTensorPoint_tmul {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    (a : A) (b : B) : complexTensorPoint p q (a ⊗ₜ[ℂ] b) = p a * q b := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- Actual tensor-product point evaluation is continuous for the product of
the two actual affine evaluation topologies. -/
theorem complexTensorPoint_continuous {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] :
    Continuous (fun pq : ComplexAlgebraPoint A × ComplexAlgebraPoint B =>
      complexTensorPoint pq.1 pq.2) := by
  apply (continuous_complexPoint_iff _).mpr
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (continuous_const : Continuous
      (fun _ : ComplexAlgebraPoint A × ComplexAlgebraPoint B => (0 : ℂ)))
  | tmul a b =>
    simp only [complexTensorPoint_tmul]
    exact ((complexPoint_evaluation_continuous a).comp continuous_fst).mul
      ((complexPoint_evaluation_continuous b).comp continuous_snd)
  | add t u ht hu =>
    convert ht.add hu using 1
    funext pq
    simp only [Pi.add_apply, map_add]

/-- The actual complex point of a native scheme fiber product, constructed
from the two actual point morphisms by the native pullback universal property. -/
def schemeComplexPointPair {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) (q : SchemeComplexPoint g) :
    SchemeComplexPoint (pullback.fst f g ≫ f) :=
  ⟨pullback.lift p.val q.val (p.property.trans q.property.symm), by
    rw [← Category.assoc, pullback.lift_fst, p.property]⟩

/-- First projection recovers the literal first actual point morphism. -/
@[simp]
theorem schemeComplexPointPair_fst {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) (q : SchemeComplexPoint g) :
    (schemeComplexPointPair f g p q).val ≫ pullback.fst f g = p.val :=
  pullback.lift_fst _ _ _

/-- Second projection recovers the literal second actual point morphism. -/
@[simp]
theorem schemeComplexPointPair_snd {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f) (q : SchemeComplexPoint g) :
    (schemeComplexPointPair f g p q).val ≫ pullback.snd f g = q.val :=
  pullback.lift_snd _ _ _

/-- The tensor point pulls back to exactly its first input point. -/
@[simp]
theorem complexTensorPoint_comp_includeLeft {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    (complexTensorPoint p q).comp (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B) = p := by
  ext a
  change complexTensorPoint p q (a ⊗ₜ[ℂ] (1 : B)) = p a
  rw [complexTensorPoint_tmul, map_one, mul_one]

/-- The tensor point pulls back to exactly its second input point. -/
@[simp]
theorem complexTensorPoint_comp_includeRight {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    (complexTensorPoint p q).comp Algebra.TensorProduct.includeRight = q := by
  ext b
  change complexTensorPoint p q ((1 : A) ⊗ₜ[ℂ] b) = q b
  rw [complexTensorPoint_tmul, map_one, one_mul]

/-- The tensor product of two actual affine-chart rings maps to the native
scheme fiber product through its genuine chart morphisms. -/
def complexAffinePairSchemeMap {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) (d : ComplexAffineChart Y) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    Spec (.of (c.ring ⊗[ℂ] d.ring)) ⟶ pullback f g := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  exact pullback.lift
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : c.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫ c.map)
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : d.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫ d.map)
    (by
      rw [Category.assoc, Category.assoc]
      have hmap :
          Spec.preimage (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft : c.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫
              (c.map ≫ f)) =
          Spec.preimage (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : d.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫
              (d.map ≫ g)) := by
        rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map]
        ext z
        change (Algebra.TensorProduct.includeLeft : c.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring)
            (algebraMap ℂ c.ring z) =
          (Algebra.TensorProduct.includeRight : d.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring)
            (algebraMap ℂ d.ring z)
        exact (Algebra.TensorProduct.includeLeft : c.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).commutes z |>.trans
          ((Algebra.TensorProduct.includeRight : d.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).commutes z).symm
      simpa only [Spec.map_preimage] using congrArg Spec.map hmap)


/-- The literal first scheme projection of the actual tensor chart. -/
theorem complexAffinePairSchemeMap_fst {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) (d : ComplexAffineChart Y) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    complexAffinePairSchemeMap f g c d ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : c.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫ c.map :=
  pullback.lift_fst _ _ _

/-- The literal second scheme projection of the actual tensor chart. -/
theorem complexAffinePairSchemeMap_snd {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) (d : ComplexAffineChart Y) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    complexAffinePairSchemeMap f g c d ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : d.ring →ₐ[ℂ] c.ring ⊗[ℂ] d.ring).toRingHom) ≫ d.map :=
  pullback.lift_snd _ _ _

/-- On actual affine points the native scheme-product point is precisely
the literal tensor-product evaluation point followed by the genuine chart map. -/
theorem schemeComplexPointPair_affine_val {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (p : ComplexAffineChartPoint f c) (q : ComplexAffineChartPoint g d) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    (schemeComplexPointPair f g (complexAffineChartPointMap f c p)
      (complexAffineChartPointMap g d q)).val =
        Spec.map (CommRingCat.ofHom (complexTensorPoint
          (affineSchemePointHomeomorphOfStructure (c.map ≫ f) p)
          (affineSchemePointHomeomorphOfStructure (d.map ≫ g) q)).toRingHom) ≫
            complexAffinePairSchemeMap f g c d := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  let := affineSchemePointTopologyOfStructure (c.map ≫ f)
  let := affineSchemePointTopologyOfStructure (d.map ≫ g)
  have hp : p.val = Spec.map (CommRingCat.ofHom
      (affineSchemePointHomeomorphOfStructure (c.map ≫ f) p).toRingHom) := by
    simpa only [Homeomorph.symm_apply_apply] using
      affineSchemePointHomeomorphOfStructure_symm_val (c.map ≫ f)
        (affineSchemePointHomeomorphOfStructure (c.map ≫ f) p)
  have hq : q.val = Spec.map (CommRingCat.ofHom
      (affineSchemePointHomeomorphOfStructure (d.map ≫ g) q).toRingHom) := by
    simpa only [Homeomorph.symm_apply_apply] using
      affineSchemePointHomeomorphOfStructure_symm_val (d.map ≫ g)
        (affineSchemePointHomeomorphOfStructure (d.map ≫ g) q)
  apply pullback.hom_ext
  · rw [schemeComplexPointPair_fst, Category.assoc, complexAffinePairSchemeMap_fst,
      ← Category.assoc, ← Spec.map_comp]
    change p.val ≫ c.map = _
    rw [hp]
    congr 2
    exact congrArg (fun h : c.ring →ₐ[ℂ] ℂ => CommRingCat.ofHom h.toRingHom)
      (complexTensorPoint_comp_includeLeft _ _).symm
  · rw [schemeComplexPointPair_snd, Category.assoc, complexAffinePairSchemeMap_snd,
      ← Category.assoc, ← Spec.map_comp]
    change q.val ≫ d.map = _
    rw [hq]
    congr 2
    exact congrArg (fun h : d.ring →ₐ[ℂ] ℂ => CommRingCat.ofHom h.toRingHom)
      (complexTensorPoint_comp_includeRight _ _).symm

/-- The actual prime-spectrum image of a complex algebra point. -/
def complexAlgebraPointPrimeImage {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : ComplexAlgebraPoint A) : PrimeSpectrum A :=
  PrimeSpectrum.comap p.toRingHom (⊥ : PrimeSpectrum ℂ)

/-- Actual affine point prime images depend continuously on the evaluations. -/
theorem complexAlgebraPointPrimeImage_continuous {A : Type*} [CommRing A] [Algebra ℂ A] :
    Continuous (complexAlgebraPointPrimeImage (A := A)) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro U ⟨a, rfl⟩
  have heq : complexAlgebraPointPrimeImage ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      {p : ComplexAlgebraPoint A | p a ≠ 0} := by
    ext p
    change p a ∉ (⊥ : PrimeSpectrum ℂ).asIdeal ↔ p a ≠ 0
    rw [PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]
  rw [heq]
  exact isOpen_ne_fun (complexPoint_evaluation_continuous a) continuous_const

/-- The actual scheme-product image map is continuous on each pair of genuine
affine charts by literal tensor evaluations. -/
theorem schemeComplexPointPairImage_affine_continuous {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y) :
    Continuous (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
      schemeComplexPointImage (pullback.fst f g ≫ f)
        (schemeComplexPointPair f g (complexAffineChartPointMap f c pq.1)
          (complexAffineChartPointMap g d pq.2))) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  have ht : Continuous (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
      complexTensorPoint (affineSchemePointHomeomorphOfStructure (c.map ≫ f) pq.1)
        (affineSchemePointHomeomorphOfStructure (d.map ≫ g) pq.2)) :=
    by
      apply (continuous_complexPoint_iff _).mpr
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simpa only [map_zero] using (continuous_const : Continuous
          (fun _ : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d => (0 : ℂ)))
      | tmul a b =>
        simp only [complexTensorPoint_tmul]
        exact (((complexPoint_evaluation_continuous a).comp
          (affineSchemePointHomeomorphOfStructure (c.map ≫ f)).continuous).comp continuous_fst).mul
          (((complexPoint_evaluation_continuous b).comp
            (affineSchemePointHomeomorphOfStructure (d.map ≫ g)).continuous).comp continuous_snd)
      | add t u ht hu =>
        convert ht.add hu using 1
        funext pq
        simp only [Pi.add_apply, map_add]
  have h := (complexAffinePairSchemeMap f g c d).continuous.comp
    (complexAlgebraPointPrimeImage_continuous.comp ht)
  convert h using 1
  funext pq
  change (schemeComplexPointPair f g (complexAffineChartPointMap f c pq.1)
    (complexAffineChartPointMap g d pq.2)).val default = _
  rw [schemeComplexPointPair_affine_val, Scheme.Hom.comp_apply]
  congr 1

/-- The jointly surjective actual affine chart map is an open map for the
actual global analytic topology. -/
theorem complexAffineChartsPointMap_isOpenMap {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    letI := schemeAnalyticPointTopology f
    IsOpenMap (complexAffineChartsPointMap f) := by
  let := schemeAnalyticPointTopology f
  intro V hV
  have heq : complexAffineChartsPointMap f '' V =
      ⋃ c : ComplexAffineChart X, complexAffineChartPointMap f c '' (Sigma.mk c ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨⟨c, q⟩, hq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨c, q, hq, rfl⟩
    · intro hp
      obtain ⟨c, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨⟨c, q⟩, hq, rfl⟩
  rw [heq]
  exact isOpen_iUnion (fun c => complexAffineChartPointMap_isOpenMap f c _
    ((isOpen_sigma_iff.mp hV) c))

/-- The actual global affine chart cover is a genuine topological quotient. -/
theorem complexAffineChartsPointMap_isQuotientMap {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    letI := schemeAnalyticPointTopology f
    IsQuotientMap (complexAffineChartsPointMap f) := by
  let := schemeAnalyticPointTopology f
  exact (complexAffineChartsPointMap_isOpenMap f).isQuotientMap
    (complexAffineChartsPointMap_continuous f) (complexAffineChartsPointMap_surjective f)

/-- The actual underlying image of the native point pair in the genuine
scheme fiber product. -/
def schemeComplexPointPairImage {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (pq : SchemeComplexPoint f × SchemeComplexPoint g) :
    (pullback f g : Scheme) :=
  schemeComplexPointImage (pullback.fst f g ≫ f) (schemeComplexPointPair f g pq.1 pq.2)

/-- The actual native scheme-product image map is continuous for the product
of the genuine global analytic point topologies. -/
theorem schemeComplexPointPairImage_continuous {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ)) :
    letI := schemeAnalyticPointTopology f
    letI := schemeAnalyticPointTopology g
    Continuous (schemeComplexPointPairImage f g) := by
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticPointTopology g
  have hQ : IsQuotientMap (Prod.map (complexAffineChartsPointMap f) (complexAffineChartsPointMap g)) :=
    ((complexAffineChartsPointMap_isOpenMap f).prodMap (complexAffineChartsPointMap_isOpenMap g)).isQuotientMap
      ((complexAffineChartsPointMap_continuous f).prodMap (complexAffineChartsPointMap_continuous g))
      ((complexAffineChartsPointMap_surjective f).prodMap (complexAffineChartsPointMap_surjective g))
  apply hQ.continuous_iff.mpr
  let H : (Σ c : ComplexAffineChart X, ComplexAffineChartPoint f c) ×
      (Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d) ≃ₜ
      Σ c : ComplexAffineChart X, ComplexAffineChartPoint f c ×
        (Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d) := Homeomorph.sigmaProdDistrib
  apply (H.symm.isOpenMap.isQuotientMap H.symm.continuous H.symm.surjective).continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro c
  let K : (Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d) ×
      ComplexAffineChartPoint f c ≃ₜ
      ComplexAffineChartPoint f c × (Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d) :=
    Homeomorph.prodComm _ _
  apply (K.isOpenMap.isQuotientMap K.continuous K.surjective).continuous_iff.mpr
  let L : (Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d) ×
      ComplexAffineChartPoint f c ≃ₜ
      Σ d : ComplexAffineChart Y, ComplexAffineChartPoint g d × ComplexAffineChartPoint f c :=
    Homeomorph.sigmaProdDistrib
  apply (L.symm.isOpenMap.isQuotientMap L.symm.continuous L.symm.surjective).continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro d
  change Continuous (fun qp : ComplexAffineChartPoint g d × ComplexAffineChartPoint f c =>
    schemeComplexPointImage (pullback.fst f g ≫ f)
      (schemeComplexPointPair f g (complexAffineChartPointMap f c qp.2)
        (complexAffineChartPointMap g d qp.1)))
  exact @Continuous.comp
    (ComplexAffineChartPoint g d × ComplexAffineChartPoint f c)
    (ComplexAffineChartPoint f c × ComplexAffineChartPoint g d)
    (pullback f g : Scheme) inferInstance inferInstance inferInstance Prod.swap
    (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
      schemeComplexPointImage (pullback.fst f g ≫ f)
        (schemeComplexPointPair f g (complexAffineChartPointMap f c pq.1)
          (complexAffineChartPointMap g d pq.2)))
    (schemeComplexPointPairImage_affine_continuous f g c d) continuous_swap

/-- An actual pair of complex points lands in the underlying native diagonal
exactly when the two actual scheme points coincide. -/
theorem schemeComplexPointPairImage_mem_diagonal {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (p q : SchemeComplexPoint f) :
    schemeComplexPointPairImage f f (p, q) ∈ Set.range (pullback.diagonal f) ↔ p = q := by
  constructor
  · rintro ⟨x, hx⟩
    apply schemeComplexPointImage_injective f
    have hp : schemeComplexPointImage f p = x := by
      calc
        schemeComplexPointImage f p =
            ((schemeComplexPointPair f f p q).val ≫ pullback.fst f f) default :=
          congrArg (fun h : Spec (.of ℂ) ⟶ X => h default) (schemeComplexPointPair_fst f f p q).symm
        _ = pullback.fst f f ((schemeComplexPointPair f f p q).val default) :=
          Scheme.Hom.comp_apply _ _ _
        _ = pullback.fst f f (pullback.diagonal f x) := congrArg (pullback.fst f f) hx.symm
        _ = x := by rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
    have hq : schemeComplexPointImage f q = x := by
      calc
        schemeComplexPointImage f q =
            ((schemeComplexPointPair f f p q).val ≫ pullback.snd f f) default :=
          congrArg (fun h : Spec (.of ℂ) ⟶ X => h default) (schemeComplexPointPair_snd f f p q).symm
        _ = pullback.snd f f ((schemeComplexPointPair f f p q).val default) :=
          Scheme.Hom.comp_apply _ _ _
        _ = pullback.snd f f (pullback.diagonal f x) := congrArg (pullback.snd f f) hx.symm
        _ = x := by rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
    exact hp.trans hq.symm
  · rintro rfl
    have hdiag : (schemeComplexPointPair f f p p).val = p.val ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · rw [schemeComplexPointPair_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [schemeComplexPointPair_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    refine ⟨schemeComplexPointImage f p, ?_⟩
    change pullback.diagonal f (p.val default) = (schemeComplexPointPair f f p p).val default
    rw [hdiag]
    exact (Scheme.Hom.comp_apply _ _ _).symm

/-- Native separatedness makes the actual complex-point analytic topology
Hausdorff, through its actual closed diagonal and actual product image map. -/
theorem schemeAnalyticPoint_t2Space {X : Scheme} (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] :
    letI := schemeAnalyticPointTopology f
    T2Space (SchemeComplexPoint f) := by
  let := schemeAnalyticPointTopology f
  apply t2_iff_isClosed_diagonal.mpr
  have heq : Set.diagonal (SchemeComplexPoint f) =
      schemeComplexPointPairImage f f ⁻¹' Set.range (pullback.diagonal f) := by
    ext pq
    exact (schemeComplexPointPairImage_mem_diagonal f pq.1 pq.2).symm
  rw [heq]
  exact (pullback.diagonal f).isClosedEmbedding.isClosed_range.preimage
    (schemeComplexPointPairImage_continuous f f)

end

end BingWangEntropy
