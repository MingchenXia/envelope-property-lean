import EnvelopeProperty.Potential.ConnectedProperMaximum

/-! # Proper native maximum over every original complete ultrametric field

The actual completed algebraic closure, genuine scalar-restriction surjectivity
and standard geometric connectedness supply the full arbitrary-field consumer.
-/

open scoped NNReal Topology Classical
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The actual completed algebraic closure constructs a genuine whole native
lift of every original point on the literal scalar-changed original scheme. -/
theorem nativeMap_surjective_completeAlgebraicClosure :
    Function.Surjective (nativeMap
      (v := NormedField.valuation (K := K))
      (w := NormedField.valuation (K := CompleteAlgebraicClosure K))
      (fun c => nnnorm_algebraMap' (CompleteAlgebraicClosure K) c) f) :=
  nativeMap_surjective_algebraicCompletion (L := ValuedAlgebraicClosure K) f

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}

/-- Every actual proper geometrically connected original scheme over an
arbitrary complete ultrametric field satisfies the whole native maximum
principle, with genuine completed-algebraic-closure lifts derived internally. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_geometricallyConnected_proper
    [IsProper f] [GeometricallyConnected f]
    (hu : IsLocallyPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y)
    (z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) : u z = u y := by
  let E := CompleteAlgebraicClosure K
  let g := SchemeScalarBaseChange.structureMap (S := E) f
  let p := SchemeScalarBaseChange.nativeMap
    (v := NormedField.valuation (K := K)) (w := NormedField.valuation (K := E))
    (fun c => nnnorm_algebraMap' E c) f
  have hsurj : Function.Surjective p :=
    SchemeScalarBaseChange.nativeMap_surjective_completeAlgebraicClosure f
  obtain ⟨a, ha⟩ := hsurj y
  obtain ⟨b, hb⟩ := hsurj z
  have : GeometricallyConnected g := inferInstance
  have : ConnectedSpace (SchemeScalarBaseChange.model (S := E) f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton g
  have hlocal : IsLocallyPSHOn Set.univ (fun q => u (p q)) := by
    simpa only [Set.preimage_univ] using
      SchemeScalarBaseChange.isLocallyPSHOn_comp_nativeMap
        (fun c => nnnorm_algebraMap' E c) f hu
  have hamax : IsMaxOn (fun q => u (p q)) Set.univ a := by
    intro q hq
    change u (p q) ≤ u (p a)
    rw [ha]
    exact hy (Set.mem_univ _)
  have h := hlocal.eq_of_isMaxOn_univ_connected_proper a hamax b
  simpa only [ha, hb] using h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
