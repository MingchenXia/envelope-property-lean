import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAffineFunctor
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeComplexPointOpen

/-! # Analytic topology on genuine complex scheme points

Affine charts carry the actual evaluation topology through the proved affine
point equivalence. Their images define a coinduced topology on the genuine
scheme-point set. Chart surjectivity is derived from native affine charts and
the actual open-immersion lifting property.
-/

open CategoryTheory AlgebraicGeometry

namespace ComplexSchemes

noncomputable section

/-- The complex algebra structure derived from an actual affine structural morphism. -/
@[instance_reducible] def affinePointFieldAlgebra {A : CommRingCat} (h : Spec A ⟶ Spec (.of ℂ)) : Algebra ℂ A :=
  (Spec.preimage h).hom.toAlgebra

/-- Its canonical affine structural map is the given actual morphism. -/
theorem affinePointFieldAlgebra_structure {A : CommRingCat}
    (h : Spec A ⟶ Spec (.of ℂ)) :
    letI := affinePointFieldAlgebra h
    complexAffineStructureMap A = h := by
  change Spec.map (Spec.preimage h) = h
  exact Spec.map_preimage h

/-- An arbitrary actual affine structural morphism has the genuine algebra-point equivalence. -/
def affineSchemePointEquivOfStructure {A : CommRingCat}
    (h : Spec A ⟶ Spec (.of ℂ)) :
    letI := affinePointFieldAlgebra h
    SchemeComplexPoint h ≃ ComplexAlgebraPoint A := by
  letI := affinePointFieldAlgebra h
  exact (Equiv.cast (congrArg SchemeComplexPoint (affinePointFieldAlgebra_structure h).symm)).trans
    (affineSchemeComplexPointEquiv A)

/-- The actual evaluation topology for an arbitrary affine structural morphism. -/
@[instance_reducible] def affineSchemePointTopologyOfStructure {A : CommRingCat}
    (h : Spec A ⟶ Spec (.of ℂ)) : TopologicalSpace (SchemeComplexPoint h) :=
  letI := affinePointFieldAlgebra h
  TopologicalSpace.induced (affineSchemePointEquivOfStructure h) inferInstance

/-- The genuine affine point equivalence is a homeomorphism for that topology. -/
def affineSchemePointHomeomorphOfStructure {A : CommRingCat}
    (h : Spec A ⟶ Spec (.of ℂ)) :
    letI := affinePointFieldAlgebra h
    letI := affineSchemePointTopologyOfStructure h
    SchemeComplexPoint h ≃ₜ ComplexAlgebraPoint A := by
  letI := affinePointFieldAlgebra h
  letI := affineSchemePointTopologyOfStructure h
  exact
    { toEquiv := affineSchemePointEquivOfStructure h
      continuous_toFun := continuous_induced_dom
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        convert (continuous_id : Continuous (id : ComplexAlgebraPoint A → ComplexAlgebraPoint A))
          using 1
        funext p
        exact (affineSchemePointEquivOfStructure h).right_inv p }

/-- Genuine affine chart data: a ring and an actual open immersion into the scheme. -/
structure ComplexAffineChart (X : Scheme) where
  ring : CommRingCat
  map : Spec ring ⟶ X
  isOpenImmersion : IsOpenImmersion map

attribute [instance] ComplexAffineChart.isOpenImmersion

/-- The actual complex points of an affine chart over its inherited structural map. -/
abbrev ComplexAffineChartPoint {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) := SchemeComplexPoint (c.map ≫ f)

/-- Every genuine affine chart carries its derived evaluation topology. -/
instance complexAffineChartPointTopology {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) : TopologicalSpace (ComplexAffineChartPoint f c) :=
  affineSchemePointTopologyOfStructure (c.map ≫ f)

/-- Chart points map to the actual global point by native scheme composition. -/
def complexAffineChartPointMap {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c : ComplexAffineChart X) : ComplexAffineChartPoint f c → SchemeComplexPoint f :=
  schemeComplexPointMap (c.map ≫ f) f c.map rfl

/-- The joint chart map uses all genuine affine open charts. -/
def complexAffineChartsPointMap {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    (Σ c : ComplexAffineChart X, ComplexAffineChartPoint f c) → SchemeComplexPoint f :=
  fun p => complexAffineChartPointMap f p.1 p.2

/-- Every genuine global complex point comes from a genuine affine chart. -/
theorem complexAffineChartsPointMap_surjective {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) : Function.Surjective (complexAffineChartsPointMap f) := by
  intro p
  obtain ⟨R, g, hg, y, hy⟩ := X.exists_Spec_apply_eq (schemeComplexPointImage f p)
  let c : ComplexAffineChart X := ⟨R, g, hg⟩
  refine ⟨⟨c, schemeComplexPointLift f g p ⟨y, hy⟩⟩, ?_⟩
  apply Subtype.ext
  exact schemeComplexPointLift_fac f g p ⟨y, hy⟩

/-- The analytic topology on genuine scheme complex points, coinduced by all affine charts. -/
@[instance_reducible] def schemeAnalyticPointTopology {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) :=
  TopologicalSpace.coinduced (complexAffineChartsPointMap f) inferInstance

/-- The joint map of genuine affine charts is continuous for the analytic topology. -/
theorem complexAffineChartsPointMap_continuous {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :
    letI := schemeAnalyticPointTopology f
    Continuous (complexAffineChartsPointMap f) := continuous_coinduced_rng

/-- Every individual genuine affine chart maps continuously into the global analytic topology. -/
theorem complexAffineChartPointMap_continuous {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c : ComplexAffineChart X) :
    letI := schemeAnalyticPointTopology f
    Continuous (complexAffineChartPointMap f c) := by
  let := schemeAnalyticPointTopology f
  exact (complexAffineChartsPointMap_continuous f).comp (continuous_sigmaMk (i := c))

/-- A map out of the global analytic point space is continuous exactly when it is
continuous on every genuine affine chart. -/
theorem schemeAnalyticPoint_continuous_iff {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    {T : Type*} [TopologicalSpace T] (g : SchemeComplexPoint f → T) :
    letI := schemeAnalyticPointTopology f
    Continuous g ↔ ∀ c : ComplexAffineChart X, Continuous (g ∘ complexAffineChartPointMap f c) := by
  let := schemeAnalyticPointTopology f
  rw [continuous_coinduced_dom]
  exact continuous_sigma_iff

end

end ComplexSchemes
