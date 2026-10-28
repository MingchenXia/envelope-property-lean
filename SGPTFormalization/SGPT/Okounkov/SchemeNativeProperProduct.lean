import SGPT.Okounkov.SchemeAnalyticMorphismTopology
import BingWangEntropy.NativeProjectiveFano
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The actual analytic product and its proper projective-factor projection

The tensor evaluation construction already gives actual scheme point pairs.
Here its values prove continuity into the genuine analytic point topology,
not merely into the underlying Zariski scheme. The native product projections
then give the inverse homeomorphism and properness with a projective factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry BingWangEntropy
open scoped Topology

/-- Continuity retains any specified equality with the actual source structural map. -/
theorem schemeNativePointMap_continuous {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ))
    (h : X ⟶ Y) (hh : h ≫ g = f) :
    Continuous[schemeAnalyticPointTopology f, schemeAnalyticPointTopology g]
      (schemeComplexPointMap f g h hh) := by
  subst f
  exact schemeComplexPointMap_continuous g h

/-- Actual affine point families are continuous when every literal coefficient is. -/
theorem affineNativePointFamily_continuous {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) {T : Type*} [TopologicalSpace T]
    (p : T → SchemeComplexPoint f)
    (hp : ∀ a : A, Continuous (fun t => (Spec.preimage (p t).val).hom a)) :
    Continuous[inferInstance, schemeAnalyticPointTopology f] p := by
  rw [schemeAnalyticPointTopology_affine]
  let := affinePointFieldAlgebra f
  let := affineSchemePointTopologyOfStructure f
  have h : Continuous (fun t => affineSchemePointHomeomorphOfStructure f (p t)) := by
    apply (continuous_complexPoint_iff _).mpr
    intro a
    change Continuous (fun t => affineSchemePointEquivOfStructure f (p t) a)
    simpa only [affineSchemePointEquivOfStructure_apply] using hp a
  have hc := (affineSchemePointHomeomorphOfStructure f).symm.continuous.comp h
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hc

variable {X Y : Scheme} (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ))

/-- The literal tensor point over the actual product chart structural map. -/
def affineNativePairTensorPoint (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    SchemeComplexPoint (complexAffinePairSchemeMap f g c d ≫ (pullback.fst f g ≫ f)) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  refine ⟨Spec.map (CommRingCat.ofHom (complexTensorPoint
    (affineSchemePointHomeomorphOfStructure (c.map ≫ f) pq.1)
    (affineSchemePointHomeomorphOfStructure (d.map ≫ g) pq.2)).toRingHom), ?_⟩
  have h := (schemeComplexPointPair f g
    (complexAffineChartPointMap f c pq.1) (complexAffineChartPointMap g d pq.2)).property
  rw [schemeComplexPointPair_affine_val, Category.assoc] at h
  exact h

/-- Every tensor coefficient of the actual point family varies continuously. -/
theorem affineNativePairTensorPoint_continuous (c : ComplexAffineChart X)
    (d : ComplexAffineChart Y) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ g)
    Continuous[inferInstance, schemeAnalyticPointTopology
      (complexAffinePairSchemeMap f g c d ≫ (pullback.fst f g ≫ f))]
        (affineNativePairTensorPoint f g c d) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  apply affineNativePointFamily_continuous
  intro t
  change Continuous (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
    (Spec.preimage (Spec.map (CommRingCat.ofHom (complexTensorPoint
      (affineSchemePointHomeomorphOfStructure (c.map ≫ f) pq.1)
      (affineSchemePointHomeomorphOfStructure (d.map ≫ g) pq.2)).toRingHom))).hom t)
  simp only [Spec.preimage_map]
  change Continuous (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
    complexTensorPoint
      (affineSchemePointHomeomorphOfStructure (c.map ≫ f) pq.1)
      (affineSchemePointHomeomorphOfStructure (d.map ≫ g) pq.2) t)
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using
      (continuous_const : Continuous
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

/-- The actual original point pair is continuous on each genuine pair of affine charts. -/
theorem schemeNativePointPair_affine_continuous (c : ComplexAffineChart X)
    (d : ComplexAffineChart Y) :
    Continuous[inferInstance, schemeAnalyticPointTopology (pullback.fst f g ≫ f)]
      (fun pq : ComplexAffineChartPoint f c × ComplexAffineChartPoint g d =>
        schemeComplexPointPair f g (complexAffineChartPointMap f c pq.1)
          (complexAffineChartPointMap g d pq.2)) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  let := schemeAnalyticPointTopology
    (complexAffinePairSchemeMap f g c d ≫ (pullback.fst f g ≫ f))
  let := schemeAnalyticPointTopology (pullback.fst f g ≫ f)
  have h := (schemeComplexPointMap_continuous (pullback.fst f g ≫ f)
    (complexAffinePairSchemeMap f g c d)).comp
      (affineNativePairTensorPoint_continuous f g c d)
  convert h using 1
  funext pq
  apply Subtype.ext
  exact schemeComplexPointPair_affine_val f g c d pq.1 pq.2

/-- Native point pairing is continuous into the ACTUAL analytic scheme-product topology. -/
theorem schemeNativePointPair_continuous :
    letI := schemeAnalyticPointTopology f
    letI := schemeAnalyticPointTopology g
    Continuous[inferInstance, schemeAnalyticPointTopology (pullback.fst f g ≫ f)]
      (fun pq : SchemeComplexPoint f × SchemeComplexPoint g =>
        schemeComplexPointPair f g pq.1 pq.2) := by
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticPointTopology g
  let := schemeAnalyticPointTopology (pullback.fst f g ≫ f)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨p, q⟩
  obtain ⟨⟨c, p'⟩, rfl⟩ := complexAffineChartsPointMap_surjective f p
  obtain ⟨⟨d, q'⟩, rfl⟩ := complexAffineChartsPointMap_surjective g q
  change ContinuousAt (fun pq : SchemeComplexPoint f × SchemeComplexPoint g =>
    schemeComplexPointPair f g pq.1 pq.2)
      (Prod.map (complexAffineChartPointMap f c) (complexAffineChartPointMap g d) (p', q'))
  apply ((complexAffineChartPointMap_isOpenEmbedding f c).prodMap
    (complexAffineChartPointMap_isOpenEmbedding g d)).continuousAt_iff.mp
  exact (schemeNativePointPair_affine_continuous f g c d).continuousAt

/-- The actual original scheme product is the actual topological product on complex points. -/
def schemeNativeProductHomeomorph :
    letI := schemeAnalyticPointTopology f
    letI := schemeAnalyticPointTopology g
    letI := schemeAnalyticPointTopology (pullback.fst f g ≫ f)
    SchemeComplexPoint (pullback.fst f g ≫ f) ≃ₜ
      SchemeComplexPoint f × SchemeComplexPoint g := by
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticPointTopology g
  let := schemeAnalyticPointTopology (pullback.fst f g ≫ f)
  exact
    { toFun p :=
        (schemeComplexPointMap (pullback.fst f g ≫ f) f (pullback.fst f g) rfl p,
          schemeComplexPointMap (pullback.fst f g ≫ f) g (pullback.snd f g)
            pullback.condition.symm p)
      invFun pq := schemeComplexPointPair f g pq.1 pq.2
      left_inv p := by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact schemeComplexPointPair_fst f g _ _
        · exact schemeComplexPointPair_snd f g _ _
      right_inv pq := by
        apply Prod.ext
        · apply Subtype.ext
          exact schemeComplexPointPair_fst f g pq.1 pq.2
        · apply Subtype.ext
          exact schemeComplexPointPair_snd f g pq.1 pq.2
      continuous_toFun :=
        (schemeNativePointMap_continuous _ _ _ rfl).prodMk
          (schemeNativePointMap_continuous _ _ _ pullback.condition.symm)
      continuous_invFun := schemeNativePointPair_continuous f g }

/-- The product homeomorphism retains the literal first original point projection. -/
theorem schemeNativeProductHomeomorph_fst (p : SchemeComplexPoint (pullback.fst f g ≫ f)) :
    (schemeNativeProductHomeomorph f g p).1 =
      schemeComplexPointMap (pullback.fst f g ≫ f) f (pullback.fst f g) rfl p := rfl

/-- The product homeomorphism retains the literal second original point projection. -/
theorem schemeNativeProductHomeomorph_snd (p : SchemeComplexPoint (pullback.fst f g ≫ f)) :
    (schemeNativeProductHomeomorph f g p).2 =
      schemeComplexPointMap (pullback.fst f g ≫ f) g (pullback.snd f g)
        pullback.condition.symm p := rfl

/-- Compactness of the actual second factor makes the original first projection proper. -/
theorem schemeNativeProduct_fst_isProper
    [hY : @CompactSpace (SchemeComplexPoint g) (schemeAnalyticPointTopology g)] :
    @IsProperMap (SchemeComplexPoint (pullback.fst f g ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (pullback.fst f g ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (pullback.fst f g ≫ f) f (pullback.fst f g) rfl) := by
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticPointTopology g
  let := schemeAnalyticPointTopology (pullback.fst f g ≫ f)
  exact isProperMap_fst_of_compactSpace.comp (schemeNativeProductHomeomorph f g).isProperMap

/-- Genuine projective geometry internally supplies the compact factor for the original projection. -/
theorem schemeNativeProjectiveProduct_fst_isProper (e : ClosedProjectiveEmbedding g) :
    @IsProperMap (SchemeComplexPoint (pullback.fst f g ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (pullback.fst f g ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (pullback.fst f g ≫ f) f (pullback.fst f g) rfl) := by
  let := schemeAnalyticPointTopology g
  let : CompactSpace (SchemeComplexPoint g) := e.analyticCompact
  exact schemeNativeProduct_fst_isProper f g

end SGPT.Okounkov
