import EnvelopeProperty.Potential.RationalSectionMaximum
import EnvelopeProperty.Potential.CurveChainMaximum
import EnvelopeProperty.FieldGlobalSections

/-! # Native maximum on the original connected proper scheme

All scalar lifts, rational sections, integral reduced support closures and
closed curve-chain intermediates are constructed from the original geometry.
-/

open scoped NNReal Classical Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.FcSchemeCurveChains

variable {F : Type u} [Field F] [IsAlgClosed F] {X : Scheme.{u}}

/-- The original finite-type geometry constructs a curve chain with every
intermediate support closed, retaining the actual original integral curves. -/
theorem closed_curveChain_of_connected_finiteType
    (f : X ⟶ Spec (CommRingCat.of F)) [FiniteType f] [PreconnectedSpace X]
    (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    Relation.ReflTransGen
      (fun a b => CurveStep a b ∧ IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) x y := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have aux (z : X) (hz : CurveChain x z) : ∀ w ∈ closure ({z} : Set X),
      IsClosed ({w} : Set X) → Relation.ReflTransGen
        (fun a b => CurveStep a b ∧ IsClosed ({a} : Set X) ∧ IsClosed ({b} : Set X)) x w := by
    induction hz with
    | refl =>
      intro w hw _
      have hwx : w = x := Set.mem_singleton_iff.mp (hx.closure_eq ▸ hw)
      subst w
      exact Relation.ReflTransGen.refl
    | @tail z t _ hzt ih =>
      intro w hw hwc
      obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints
        (show (closure ({z} : Set X)).Nonempty from ⟨z, subset_closure (by simp)⟩)
        isClosed_closure.isLocallyClosed
      obtain ⟨C, i, hi, hC, hd, hzC, htC⟩ := hzt
      have : IsClosedImmersion i := hi
      have hzc : closure ({z} : Set X) ⊆ Set.range i :=
        closure_minimal (Set.singleton_subset_iff.mpr hzC) i.isClosedEmbedding.isClosed_range
      have htc : closure ({t} : Set X) ⊆ Set.range i :=
        closure_minimal (Set.singleton_subset_iff.mpr htC) i.isClosedEmbedding.isClosed_range
      exact (ih v hv hvc).tail ⟨⟨C, i, hi, hC, hd, hzc hv, htc hw⟩, hvc, hwc⟩
  exact aux y (curveChain_of_connected_finiteType f x y hx hy)
    y (subset_closure (by simp)) hy

end EnvelopeProperty.FcSchemeCurveChains

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {u : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f → EReal}

/-- The actual connected finite-type curve chain gives closed-support native
maximum propagation without projectivity or properness assumptions. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_of_closed_supports_finiteType
    [FiniteType f] [PreconnectedSpace X]
    (hu : IsLocallyPSHOn Set.univ u)
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
private theorem IsLocallyPSHOn.eq_rationalSection_of_either_isMaxOn_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyPSHOn Set.univ u)
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
  have hlocal : IsLocallyPSHOn Set.univ (fun q => u (p q)) := by
    simpa only [Set.preimage_univ] using
      isLocallyPSHOn_comp_nativeMap (fcRationalLiftField_val_algebraMap f y) f hu
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
theorem IsLocallyPSHOn.eq_section_of_isMaxOn_univ_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyPSHOn Set.univ u)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y) :
    u (sectionNativePoint (NormedField.valuation (K := K)) f s hs) = u y :=
  (hu.eq_rationalSection_of_either_isMaxOn_integral_proper s hs y (Or.inl hy)).symm

omit [CompleteSpace K] in
/-- A maximum at an actual original rational section propagates to every
whole native point on the actual original integral proper scheme. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_section_integral_proper
    [IsIntegral X] [IsProper f]
    (hu : IsLocallyPSHOn Set.univ u)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hy : IsMaxOn u Set.univ (sectionNativePoint (NormedField.valuation (K := K)) f s hs))
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) :
    u y = u (sectionNativePoint (NormedField.valuation (K := K)) f s hs) :=
  hu.eq_rationalSection_of_either_isMaxOn_integral_proper s hs y (Or.inr hy)

omit [CompleteSpace K] [IsAlgClosed K] in
/-- The actual reduced closure of the original support lifts the entire point
and constructs a genuine original integral closed subscheme. -/
private theorem exists_integral_support_lift
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
theorem IsLocallyPSHOn.exists_closed_support_maximizer_of_isMaxOn_univ
    [IsProper f] (hu : IsLocallyPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y) :
    ∃ z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f,
      IsClosed ({z.1.point} : Set X) ∧ u z = u y := by
  obtain ⟨C, i, hC, hi, a, ha⟩ := exists_integral_support_lift y
  have : IsIntegral C := hC
  have : IsClosedImmersion i := hi
  let g := i ≫ f
  let p := map (v := NormedField.valuation (K := K)) (fX := g) (fY := f) i rfl
  have hlocal : IsLocallyPSHOn Set.univ (fun q => u (p q)) := by
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
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_connected_proper
    [IsProper f] [PreconnectedSpace X]
    (hu : IsLocallyPSHOn Set.univ u)
    (y : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f)
    (hy : IsMaxOn u Set.univ y)
    (z : RelativeSchemeValuedPoint (NormedField.valuation (K := K)) f) : u z = u y := by
  have : FiniteType f := ⟨⟩
  obtain ⟨w, hwc, hw⟩ := hu.exists_closed_support_maximizer_of_isMaxOn_univ y hy
  have hwmax : IsMaxOn u Set.univ w := by
    intro q hq
    exact (hy hq).trans_eq hw.symm
  obtain ⟨C, i, hC, hi, a, ha⟩ := exists_integral_support_lift z
  have : IsIntegral C := hC
  have : IsClosedImmersion i := hi
  let g := i ≫ f
  let p := map (v := NormedField.valuation (K := K)) (fX := g) (fY := f) i rfl
  have hlocal : IsLocallyPSHOn Set.univ (fun q => u (p q)) := by
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
