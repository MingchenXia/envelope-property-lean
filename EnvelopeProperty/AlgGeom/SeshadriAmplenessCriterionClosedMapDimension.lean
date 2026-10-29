import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionDrop

/-!
# Seshadri Ampleness Criterion Closed Map Dimension

The actual source of a proper closed immersion has lower dimension,
by its native closed range and the existing strict-chain dimension theorem. -/

noncomputable section
open AlgebraicGeometry TopologicalSpace Topology
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionClosedMapDimension

/-- Actual nonsurjective closed immersions lower a finite dimension bound.
The source need not be integral or reduced. No chosen image comparison,
point-closure matching, projectivity or target-dimension certificate. -/
theorem closedImmersion_dimension_drop
    {X Y : Scheme.{u}} [IrreducibleSpace X]
    (j : Y ⟶ X) [IsClosedImmersion j] (hj : ¬Function.Surjective j)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim Y ≤ d := by
  let Z : Closeds X := ⟨Set.range j, j.isClosedEmbedding.isClosed_range⟩
  have hZ : Z ≠ ⊤ := by
    intro ht
    apply hj
    apply Set.range_eq_univ.mp
    exact congrArg (fun W : Closeds X => (W : Set X)) ht
  let e : Y ≃ₜ Z := j.isClosedEmbedding.isEmbedding.toHomeomorph
  have he : topologicalKrullDim Y = topologicalKrullDim Z :=
    IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  exact (le_of_eq he).trans
    (SeshadriAmplenessCriterion.properClosed_dimension_drop Z hZ d hdim)

end EnvelopeProperty.SeshadriAmplenessCriterionClosedMapDimension
