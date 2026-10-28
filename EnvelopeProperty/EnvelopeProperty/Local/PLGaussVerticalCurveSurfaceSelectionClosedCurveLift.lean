import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionNormalizationDimension
import EnvelopeProperty.AlgGeom.CurveFiniteMapDegrees

/-! # Actual CLOSED integral curves lifted through an original finite surjection

The original pointed pullback-component construction retains closedness of
its SAME map into the source model. Whole dimension and projectivity are
internally derived; no normal/flat target or curve-lift certificate is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedCurveLift
variable {X Y C : Scheme.{u}}

/-- The original projective central curve lifts as an ACTUAL CLOSED curve in the source of the SAME finite surjection. -/
theorem exists_closed_projective_curve_lift {k : Type u} [Field k] [IsIntegral C]
    (p : X ⟶ Spec (CommRingCat.of k)) (q : C ⟶ Spec (CommRingCat.of k))
    (hq : IsProjectiveFactorization q) (hdC : topologicalKrullDim C = 1)
    (i : C ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q)
    (f : Y ⟶ X) [IsFinite f] [Surjective f] :
    ∃ (D : Scheme.{u}) (g : D ⟶ C) (j : D ⟶ Y),
      IsIntegral D ∧ IsFinite g ∧ IsDominant g ∧ IsClosedImmersion j ∧
      topologicalKrullDim D = 1 ∧ IsProjectiveFactorization (g ≫ q) ∧
      j ≫ f = g ≫ i ∧ j ≫ (f ≫ p) = g ≫ q := by
  obtain ⟨y, hy⟩ := f.surjective (i (genericPoint C))
  obtain ⟨z, _hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := i) y (genericPoint C) hy
  let B : Scheme.{u} := pullback f i
  let Z : Closeds B := ⟨irreducibleComponent z, isClosed_irreducibleComponent⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let D : Scheme.{u} := I.subscheme
  let e : D ⟶ B := I.subschemeι
  let : IsIntegral D := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z
    isIrreducible_irreducibleComponent
  let : IsClosedImmersion e := inferInstance
  let g : D ⟶ C := e ≫ pullback.snd f i
  let j : D ⟶ Y := e ≫ pullback.fst f i
  have hzK : z ∈ Set.range e := by
    change z ∈ Set.range I.subschemeι
    rw [I.range_subschemeι]
    exact mem_irreducibleComponent
  obtain ⟨w, hw⟩ := hzK
  have hgeneric : g w = genericPoint C := by
    change (pullback.snd f i) (e w) = _
    rw [hw]
    exact hz₂
  let : IsFinite g := inferInstance
  let : IsClosedImmersion j := inferInstance
  let : IsDominant g := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (genericPoint_spec C).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨w, hgeneric⟩)
  let : IsProper q := hq.isProper
  have hdim : topologicalKrullDim D = 1 :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizationDimension.whole_dimension_eq_of_finite_dominant q g).trans hdC
  have htriangle : j ≫ f = g ≫ i := by
    change (e ≫ pullback.fst f i) ≫ f = (e ≫ pullback.snd f i) ≫ i
    simp only [Category.assoc, pullback.condition]
  have hbase : j ≫ (f ≫ p) = g ≫ q := by
    rw [← Category.assoc, htriangle, Category.assoc, hi]
  exact ⟨D, g, j, inferInstance, inferInstance, inferInstance, inferInstance, hdim,
    CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g, htriangle, hbase⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedCurveLift
