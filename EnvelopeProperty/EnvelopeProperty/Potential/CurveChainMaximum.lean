import EnvelopeProperty.Potential.IntegralSchemeCurveMaximum
import EnvelopeProperty.Potential.CurveClosedPointChains
import EnvelopeProperty.Berkovich.SchemeClosedImmersion

/-! # Actual native maximum propagation along original closed integral curves -/

open scoped NNReal Topology Classical
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]
  {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}

/-- Actual whole native points on one original closed integral curve share
the attained original global maximum, derived by genuine pullback. -/
theorem IsLocallyPSHOn.eq_of_integral_closed_curve_of_isMaxOn
    (hu : IsLocallyPSHOn Set.univ u)
    {y z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f}
    (hymax : IsMaxOn u Set.univ y) {C : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ X) [IsClosedImmersion i] (hC : topologicalKrullDim C ≤ 1)
    (hy : y.1.point ∈ Set.range i) (hz : z.1.point ∈ Set.range i) : u z = u y := by
  have hyr : y ∈ Set.range (map (fX := i ≫ f) (fY := f) i rfl) := by
    rw [range_map_of_isClosedImmersion]
    exact hy
  have hzr : z ∈ Set.range (map (fX := i ≫ f) (fY := f) i rfl) := by
    rw [range_map_of_isClosedImmersion]
    exact hz
  obtain ⟨a, ha⟩ := hyr
  obtain ⟨b, hb⟩ := hzr
  have hlocal : IsLocallyPSHOn Set.univ (fun q => u (map (fX := i ≫ f) (fY := f) i rfl q)) := by
    have h := hu.comp_mapOverBase (fX := i ≫ f) (RingHom.id K) (fun _ => rfl) i (by simp)
    simpa only [Set.preimage_univ, mapOverBase_id] using h
  have hamax : IsMaxOn (fun q => u (map (fX := i ≫ f) (fY := f) i rfl q)) Set.univ a := by
    intro q hq
    change u (map i rfl q) ≤ u (map i rfl a)
    rw [ha]
    exact hymax (Set.mem_univ _)
  have heq := hlocal.eq_of_isMaxOn_univ_integral_curve hC a hamax b
  simpa only [ha, hb] using heq

/-- The actual reduced singleton handles the empty original curve chain at a
closed support, without a valuation-uniqueness assumption. -/
theorem IsLocallyPSHOn.eq_of_closed_support_eq_of_isMaxOn
    (hu : IsLocallyPSHOn Set.univ u)
    {y z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f}
    (hymax : IsMaxOn u Set.univ y) (hyc : IsClosed ({y.1.point} : Set X))
    (hz : z.1.point = y.1.point) : u z = u y := by
  let Z : TopologicalSpace.Closeds X := ⟨{y.1.point}, hyc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral I.subscheme :=
    FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z isIrreducible_singleton
  have hpoint (a : I.subscheme) : I.subschemeι a = y.1.point := by
    have h : I.subschemeι a ∈ Set.range I.subschemeι := ⟨a, rfl⟩
    rw [I.range_subschemeι] at h
    exact Set.mem_singleton_iff.mp h
  have : Subsingleton I.subscheme := ⟨fun a b =>
    I.subschemeι.isClosedEmbedding.injective ((hpoint a).trans (hpoint b).symm)⟩
  have hdim : topologicalKrullDim I.subscheme ≤ 1 :=
    (topologicalKrullDim_zero_of_discreteTopology I.subscheme).trans (by norm_num)
  apply hu.eq_of_integral_closed_curve_of_isMaxOn hymax I.subschemeι hdim
  · rw [I.range_subschemeι]
    exact Set.mem_singleton _
  · rw [I.range_subschemeι]
    exact Set.mem_singleton_iff.mpr hz

/-- Actual native point existence at closed intermediates derives maximum
propagation along the constructed original projective curve chain. -/
theorem IsLocallyPSHOn.eq_of_closed_projectiveCurveChain_of_isMaxOn
    (hu : IsLocallyPSHOn Set.univ u)
    {y z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f}
    (hymax : IsMaxOn u Set.univ y) (hyc : IsClosed ({y.1.point} : Set X))
    (hchain : Relation.ReflTransGen
      (fun a b => FcProjectiveCurveChains.ProjectiveCurveStep f a b ∧
        IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) y.1.point z.1.point) : u z = u y := by
  have aux {t : X} (h : Relation.ReflTransGen
      (fun a b => FcProjectiveCurveChains.ProjectiveCurveStep f a b ∧
        IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) y.1.point t) :
      ∀ a : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f,
        a.1.point = t → u a = u y := by
    induction h with
    | refl =>
      intro a ha
      exact hu.eq_of_closed_support_eq_of_isMaxOn hymax hyc ha
    | @tail s t _ hst ih =>
      intro a ha
      obtain ⟨b, hb⟩ := exists_nativePoint_of_isClosed_support f s hst.2.1
      have hbval := ih b hb
      have hbmax : IsMaxOn u Set.univ b := by
        intro q hq
        exact (hymax hq).trans_eq hbval.symm
      have hstep : FcProjectiveCurveChains.ProjectiveCurveStep f b.1.point a.1.point := by
        rw [hb, ha]
        exact hst.1
      obtain ⟨C, i, hi, hC, hd, _, hbC, haC⟩ := hstep
      have : IsIntegral C := hC
      have : IsClosedImmersion i := hi
      exact (hu.eq_of_integral_closed_curve_of_isMaxOn hbmax i hd.le hbC haC).trans hbval
  exact aux hchain z rfl

omit [LocallyOfFiniteType f] in
/-- Original connected projective geometry supplies every curve and every
intermediate lift; closed-support maximum propagation has no certificate input. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_of_closed_supports
    [FiniteType f] [IsProjective f] [PreconnectedSpace X]
    (hu : IsLocallyPSHOn Set.univ u)
    {y z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f}
    (hymax : IsMaxOn u Set.univ y) (hyc : IsClosed ({y.1.point} : Set X))
    (hzc : IsClosed ({z.1.point} : Set X)) : u z = u y := by
  apply hu.eq_of_closed_projectiveCurveChain_of_isMaxOn hymax hyc
  exact FcProjectiveCurveChains.closed_projectiveCurveChain_of_connected_finiteType
    f y.1.point z.1.point hyc hzc

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
