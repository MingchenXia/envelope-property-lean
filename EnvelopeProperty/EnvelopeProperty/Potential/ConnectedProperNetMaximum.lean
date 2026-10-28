import EnvelopeProperty.Potential.IntegralCurveNetMaximum
import EnvelopeProperty.Berkovich.SchemeNetPSHAlgebra
import EnvelopeProperty.Potential.ConnectedProperMaximum
import EnvelopeProperty.Potential.GeometricallyConnectedProperMaximum

/-! # The whole proper maximum principle for genuine directed local PL nets

Original function definitions remain unchanged. All geometric curve chains,
rational sections, true scalar lifts and global coefficient producers are
reused; actual directed curve comparison supplies the broader function class.
-/

open scoped NNReal Classical Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}

/-- Actual whole native points on one original closed integral curve share
the attained original global maximum, derived by genuine pullback. -/
theorem IsLocallyNetPSHOn.eq_of_integral_closed_curve_of_isMaxOn
    [LocallyOfFiniteType f]
    (hu : IsLocallyNetPSHOn Set.univ u)
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
  have hlocal : IsLocallyNetPSHOn Set.univ (fun q => u (map (fX := i ≫ f) (fY := f) i rfl q)) := by
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
theorem IsLocallyNetPSHOn.eq_of_closed_support_eq_of_isMaxOn
    [LocallyOfFiniteType f]
    (hu : IsLocallyNetPSHOn Set.univ u)
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

/-- The actual connected finite-type curve chain gives closed-support native
maximum propagation without projectivity or properness assumptions. -/
theorem IsLocallyNetPSHOn.eq_of_isMaxOn_univ_of_closed_supports_finiteType
    [FiniteType f] [PreconnectedSpace X]
    (hu : IsLocallyNetPSHOn Set.univ u)
    {y z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f}
    (hymax : IsMaxOn u Set.univ y) (hyc : IsClosed ({y.1.point} : Set X))
    (hzc : IsClosed ({z.1.point} : Set X)) : u z = u y := by
  have hchain := FcSchemeCurveChains.closed_curveChain_of_connected_finiteType
    f y.1.point z.1.point hyc hzc
  have aux {t : X} (h : Relation.ReflTransGen
      (fun a b => FcSchemeCurveChains.CurveStep a b ∧
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
      have hstep : FcSchemeCurveChains.CurveStep b.1.point a.1.point := by
        rw [hb, ha]
        exact hst.1
      obtain ⟨C, i, hi, hC, hd, hbC, haC⟩ := hstep
      have : IsIntegral C := hC
      have : IsClosedImmersion i := hi
      exact (hu.eq_of_integral_closed_curve_of_isMaxOn hbmax i hd.le hbC haC).trans hbval
  exact aux hchain z rfl

open SchemeScalarBaseChange in
omit [CompleteSpace K] in
private theorem IsLocallyNetPSHOn.eq_rationalSection_of_either_isMaxOn_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyNetPSHOn Set.univ u)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hmax : IsMaxOn u Set.univ y ∨
      IsMaxOn u Set.univ (sectionNativePoint (NormedField.valuation (K := K)) f s hs)) :
    u y = u (sectionNativePoint (NormedField.valuation (K := K)) f s hs) := by
  let E := fcRationalLiftField f y
  let g := structureMap (S := E) f
  let p := nativeMap (fcRationalLiftField_val_algebraMap f y) f
  let a := sectionNativePoint (NormedField.valuation (K := E)) g
    (fcScalarChangeRationalSection (E := E) f s hs)
    (fcScalarChangeRationalSection_structure (E := E) f s hs)
  let b := fcRationalScalarLift f y
  have ha : p a = sectionNativePoint (NormedField.valuation (K := K)) f s hs :=
    nativeMap_sectionNativePoint f s hs
  have hb : p b = y := fcRationalScalarLift_nativeMap f y
  have : GeometricallyConnected f := FieldGlobalSections.geometricallyConnected f
  have : GeometricallyConnected g := inferInstance
  have : FiniteType g := ⟨⟩
  have : ConnectedSpace (model (S := E) f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton g
  have hlocal : IsLocallyNetPSHOn Set.univ (fun q => u (p q)) := by
    simpa only [Set.preimage_univ] using
      isLocallyNetPSHOn_comp_nativeMap (fcRationalLiftField_val_algebraMap f y) f hu
  have hac : IsClosed ({a.1.point} : Set (model (S := E) f)) :=
    isClosed_support_sectionNativePoint _ _ _ _
  have hbc : IsClosed ({b.1.point} : Set (model (S := E) f)) :=
    isClosed_support_fcRationalScalarLift f y
  rcases hmax with hy | hsmax
  · have hbmax : IsMaxOn (fun q => u (p q)) Set.univ b := by
      intro q hq
      change u (p q) ≤ u (p b)
      rw [hb]
      exact hy (Set.mem_univ _)
    have h := hlocal.eq_of_isMaxOn_univ_of_closed_supports_finiteType hbmax hbc hac
    simpa only [ha, hb] using h.symm
  · have hamax : IsMaxOn (fun q => u (p q)) Set.univ a := by
      intro q hq
      change u (p q) ≤ u (p a)
      rw [ha]
      exact hsmax (Set.mem_univ _)
    have h := hlocal.eq_of_isMaxOn_univ_of_closed_supports_finiteType hamax hac hbc
    simpa only [ha, hb] using h

omit [CompleteSpace K] in
/-- On the actual integral proper source, scalar rationalization propagates
an arbitrary-support original maximum to every actual original rational section. -/
theorem IsLocallyNetPSHOn.eq_section_of_isMaxOn_univ_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyNetPSHOn Set.univ u)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y) :
    u (sectionNativePoint (NormedField.valuation (K := K)) f s hs) = u y :=
  (hu.eq_rationalSection_of_either_isMaxOn_integral_proper s hs y (Or.inl hy)).symm

omit [CompleteSpace K] in
/-- A maximum at an actual original rational section propagates to every
whole native point on the actual original integral proper scheme. -/
theorem IsLocallyNetPSHOn.eq_of_isMaxOn_section_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyNetPSHOn Set.univ u)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hy : IsMaxOn u Set.univ (sectionNativePoint (NormedField.valuation (K := K)) f s hs))
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) :
    u y = u (sectionNativePoint (NormedField.valuation (K := K)) f s hs) :=
  hu.eq_rationalSection_of_either_isMaxOn_integral_proper s hs y (Or.inr hy)

omit [CompleteSpace K] [IsAlgClosed K] in
/-- The actual reduced closure of the original support lifts the entire point
and constructs a genuine original integral closed subscheme. -/
private theorem exists_integral_net_support_lift
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X), IsIntegral C ∧ IsClosedImmersion i ∧
      ∃ z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) (i ≫ f),
        map i rfl z = y := by
  let Z : TopologicalSpace.Closeds X := ⟨closure ({y.1.point} : Set X), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : IsIntegral I.subscheme :=
    FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z
      isIrreducible_singleton.closure
  have hy : y ∈ Set.range (map (fX := I.subschemeι ≫ f) (fY := f) I.subschemeι rfl) := by
    rw [range_map_of_isClosedImmersion, I.range_subschemeι]
    exact subset_closure (Set.mem_singleton _)
  obtain ⟨z, hz⟩ := hy
  exact ⟨I.subscheme, I.subschemeι, hI, inferInstance, z, hz⟩

omit [CompleteSpace K] in
/-- The original geometry constructs an attained global maximizer at a closed
support from an arbitrary attained maximum; no rational-lift premise occurs. -/
theorem IsLocallyNetPSHOn.exists_closed_support_maximizer_of_isMaxOn_univ
    [IsProper f] (hu : IsLocallyNetPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y) :
    ∃ z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f,
      IsClosed ({z.1.point} : Set X) ∧ u z = u y := by
  obtain ⟨C, i, hC, hi, a, ha⟩ := exists_integral_net_support_lift y
  have : IsIntegral C := hC
  have : IsClosedImmersion i := hi
  let g := i ≫ f
  let p := map (v := NormedField.valuation (K := K)) (fX := g) (fY := f) i rfl
  have hlocal : IsLocallyNetPSHOn Set.univ (fun q => u (p q)) := by
    have h := hu.comp_mapOverBase (fX := g) (RingHom.id K) (fun _ => rfl) i (by simp [g])
    have hmap (q : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) g) :
        mapOverBase (RingHom.id K) (fun _ => rfl) i (by simp [g]) q = p q :=
      Subtype.ext rfl
    simpa only [Set.preimage_univ, hmap] using h
  have hamax : IsMaxOn (fun q => u (p q)) Set.univ a := by
    intro q hq
    change u (map i rfl q) ≤ u (map i rfl a)
    rw [ha]
    exact hy (Set.mem_univ _)
  obtain ⟨s, hs⟩ := exists_rational_section_of_finiteType_nonempty g
  let b := sectionNativePoint (NormedField.valuation (K := K)) g s hs
  refine ⟨p b, ?_, ?_⟩
  · have hbc := isClosed_support_sectionNativePoint (NormedField.valuation (K := K)) g s hs
    change IsClosed ({i b.1.point} : Set X)
    simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap _ hbc
  · have h := hlocal.eq_section_of_isMaxOn_univ_integral_proper s hs a hamax
    change u (p b) = u (p a) at h
    have hpa : p a = y := ha
    rw [hpa] at h
    exact h

/-- On every actual connected proper original scheme, an attained native
locally psh global maximum propagates to EVERY entire original native point.
All scalar rationalization, integral closures and curve chains are derived. -/
theorem IsLocallyNetPSHOn.eq_of_isMaxOn_univ_connected_proper
    [IsProper f] [PreconnectedSpace X]
    (hu : IsLocallyNetPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y)
    (z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) : u z = u y := by
  have : FiniteType f := ⟨⟩
  obtain ⟨w, hwc, hw⟩ := hu.exists_closed_support_maximizer_of_isMaxOn_univ y hy
  have hwmax : IsMaxOn u Set.univ w := by
    intro q hq
    exact (hy hq).trans_eq hw.symm
  obtain ⟨C, i, hC, hi, a, ha⟩ := exists_integral_net_support_lift z
  have : IsIntegral C := hC
  have : IsClosedImmersion i := hi
  let g := i ≫ f
  let p := map (v := NormedField.valuation (K := K)) (fX := g) (fY := f) i rfl
  have hlocal : IsLocallyNetPSHOn Set.univ (fun q => u (p q)) := by
    have h := hu.comp_mapOverBase (fX := g) (RingHom.id K) (fun _ => rfl) i (by simp [g])
    have hmap (q : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) g) :
        mapOverBase (RingHom.id K) (fun _ => rfl) i (by simp [g]) q = p q :=
      Subtype.ext rfl
    simpa only [Set.preimage_univ, hmap] using h
  obtain ⟨s, hs⟩ := exists_rational_section_of_finiteType_nonempty g
  let b := sectionNativePoint (NormedField.valuation (K := K)) g s hs
  have hbc : IsClosed ({(p b).1.point} : Set X) := by
    have hb := isClosed_support_sectionNativePoint (NormedField.valuation (K := K)) g s hs
    change IsClosed ({i b.1.point} : Set X)
    simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap _ hb
  have hbval : u (p b) = u w :=
    hu.eq_of_isMaxOn_univ_of_closed_supports_finiteType hwmax hwc hbc
  have hbmax : IsMaxOn (fun q => u (p q)) Set.univ b := by
    intro q hq
    exact (hwmax (Set.mem_univ _)).trans_eq hbval.symm
  have h := hlocal.eq_of_isMaxOn_section_integral_proper s hs hbmax a
  change u (p a) = u (p b) at h
  have hpa : p a = z := ha
  rw [hpa] at h
  exact h.trans (hbval.trans hw)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}

/-- Every actual proper geometrically connected original scheme over an
arbitrary complete ultrametric field satisfies the whole native maximum
principle, with genuine completed-algebraic-closure lifts derived internally. -/
theorem IsLocallyNetPSHOn.eq_of_isMaxOn_univ_geometricallyConnected_proper
    [IsProper f] [GeometricallyConnected f]
    (hu : IsLocallyNetPSHOn Set.univ u)
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
  have hlocal : IsLocallyNetPSHOn Set.univ (fun q => u (p q)) := by
    simpa only [Set.preimage_univ] using
      SchemeScalarBaseChange.isLocallyNetPSHOn_comp_nativeMap
        (fun c => nnnorm_algebraMap' E c) f hu
  have hamax : IsMaxOn (fun q => u (p q)) Set.univ a := by
    intro q hq
    change u (p q) ≤ u (p a)
    rw [ha]
    exact hy (Set.mem_univ _)
  have h := hlocal.eq_of_isMaxOn_univ_connected_proper a hamax b
  simpa only [ha, hb] using h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
